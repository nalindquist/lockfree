extern crate crossbeam;
extern crate rand;

pub mod stack;
pub mod queue;
pub mod dict;
pub mod linearization;


///////////////////////////////////////////////////////////////////////////////
//// Utilities
///////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod utilities {
  use super::linearization::*;
  use std::time::{Duration, Instant};
  use std::fs::File;
  use std::io::Write;
  use rand::{self, Rng, ThreadRng};
  use crossbeam;

  pub trait TestOp: Copy {}

  pub trait Tester {
    fn execute_op(&mut self, rng: &mut ThreadRng);
  }

  pub trait ConcurrentTester: Clone + Send + Sync
  where Self::L: Linearization {
    type L;

    fn execute_op(&mut self, rng: &mut ThreadRng);
    fn record_op(&mut self, rng: &mut ThreadRng, tid: usize, i: usize) -> Action<<Self::L as Linearization>::P>;
    fn lin(&self) -> Self::L;
  }

  pub fn duration_to_ns(d: Duration) -> f64 {
    (d.as_secs() as f64) * 1_000_000_000.0 +
      (d.subsec_nanos() as f64)
  }

  pub fn secs_to_duration(t: f64) -> Duration {
    Duration::new(
      t as u64,
      ((t - ((t as u64) as f64)) * 1_000_000_000.0) as u32)
  }

  pub fn write_log<P: Op>(mut log: Vec<Action<P>>, name: &str) {
    log.sort_by(|a1, a2| {
      a1.get_start().cmp(&a2.get_start())
    });

    let mut f = File::create(name).unwrap();
    for a in log.iter() {
      f.write_all(format!("{:?}\n", a).as_bytes()).unwrap();
    }
  }

  pub fn write_history<P: Op>(history: &Vec<Action<P>>, name: &str) {
    let mut f = File::create(name).unwrap();

    for a in history.iter() {
      f.write_all(format!("{:?}\n", a).as_bytes()).unwrap();
    }
  }

  pub fn choose_op<P: TestOp>(rng: &mut ThreadRng, ops: &Vec<(P, f64)>) -> P {
    let f = rng.next_f64();
    let mut acc = 0.0;

    for pair in ops.iter() {
      acc += pair.1;
      if acc > f {
        return pair.0
      }
    }

    panic!("Unable to select operation.");
  }

  pub fn gen_args(rng: &mut ThreadRng, n: usize) -> Vec<i32> {
    let mut v = Vec::new();
    for _ in 0..n {
      v.push(rng.gen());
    }
    v
  }

  pub fn test_throughput<T: Tester>(mut tester: T, t_secs: f64) {
    let mut rng = rand::thread_rng();
    let mut n_ops = 0;
    let duration = secs_to_duration(t_secs);
    let start_time = Instant::now();

    let elapsed = loop {
      tester.execute_op(&mut rng);
      n_ops += 1;

      let d = start_time.elapsed();
      if d >= duration {
        break d
      }
    };

    let ns_elapsed = duration_to_ns(elapsed);
    let ns_per_op = ns_elapsed/(n_ops as f64);

    println!("");
    println!("Time elapsed (s): {}", ns_elapsed / 1_000_000_000.0);
    println!("Ops completed:    {}", n_ops);
    println!("Time per op (ns): {}", ns_per_op);
  }

  pub fn test_concurrent_correctness<T>(tester: T, t_secs: f64, n_threads: usize)
  where T: ConcurrentTester, <T::L as Linearization>::P: Send + Sync {
    let mut handles = Vec::new();
    let mut log = Vec::new();

    crossbeam::scope(|scope| {
      for tid in 0..n_threads {
        let mut tester = tester.clone();

        let h = scope.spawn(move || {
          let mut rng = rand::thread_rng();
          let mut log = Vec::new();
          let mut i = 0;
          let duration = secs_to_duration(t_secs);
          let start_time = Instant::now();

          loop {
            let a = tester.record_op(&mut rng, tid, i);
            log.push(a);
            i += 1;

            let d = start_time.elapsed();
            if d >= duration {
              break;
            }
          }

          log
        });

        handles.push(h);
      }
    });

    for h in handles {
      for entry in h.join() {
        log.push(entry);
      }
    }

    write_log(log.clone(), "log.txt");

    let history = tester.lin().linearize(log).expect(
      "No valid linearization found.");

    write_history(&history, "history.txt");
  }

  pub fn test_concurrent_throughput<T>(tester: T, t_secs: f64, n_threads: usize)
  where T: ConcurrentTester, <T::L as Linearization>::P: Send + Sync {
    let mut handles = Vec::new();

    crossbeam::scope(|scope| {
      for _ in 0..n_threads {
        let mut tester = tester.clone();

        let h = scope.spawn(move || {
          let mut rng = rand::thread_rng();
          let mut n_ops = 0;
          let duration = secs_to_duration(t_secs);
          let start_time = Instant::now();

          let elapsed = loop {
            tester.execute_op(&mut rng);
            n_ops += 1;

            let d = start_time.elapsed();
            if d >= duration {
              break d
            }
          };

          (elapsed, n_ops)
        });

        handles.push(h);
      }
    });

    let mut ns_elapsed = 0.0;
    let mut op_total = 0;
    for h in handles {
      let (elapsed, n_ops) = h.join();
      ns_elapsed += duration_to_ns(elapsed);
      op_total += n_ops;
    }
    let ns_per_op = ns_elapsed/(op_total as f64);

    println!("");
    println!("Time elapsed (s): {}", ns_elapsed / 1_000_000_000.0);
    println!("Ops completed:    {}", op_total);
    println!("Time per op (ns): {}", ns_per_op);
  }
}


///////////////////////////////////////////////////////////////////////////////
//// Linearization Tests
///////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod linearization_tests {
  use std::thread;
  use std::time::{SystemTime, Duration};
  use super::linearization::*;

  #[test]
  fn empty_linearization_test() {
    let log = Vec::new();

    let mut slin : StackLinearization<i32> = StackLinearization::new();
    let history = slin.linearize(log).expect(
      "No valid linearization found.");

    assert_eq!(history.len(), 0);
  }

  #[test]
  fn no_overlap_linearization_test() {
    let d = Duration::from_millis(10);
    let n = 10;
    let mut actions = Vec::new();

    for i in 0..n {
      let t1 = SystemTime::now();
      thread::sleep(d);
      let t2 = SystemTime::now();
      thread::sleep(d);

      actions.push(Action::new(
        (0, i),
        StackOp::Push(1),
        t1,
        t2));
    }

    let mut log1 = Vec::new();
    let mut log2 = Vec::new();
    for i in 0..n {
      log1.push(actions[i]);
      log2.push(actions[n-i-1]);
    }

    let mut slin1 = StackLinearization::new();
    let history1 = slin1.linearize(log1).expect(
      "No valid linearization found.");

    assert_eq!(history1.len(), n);
    for i in 0..n {
      assert_eq!(history1[i].get_id(), (0, i));
    }

    let mut slin2 = StackLinearization::new();
    let history2 = slin2.linearize(log2).expect(
      "No valid linearization found.");

    assert_eq!(history2.len(), n);
    for i in 0..n {
      assert_eq!(history2[i].get_id(), (0, i));
    }
  }

  #[test]
  fn overlap_linearization_test() {
    let d = Duration::from_millis(10);
    let mut log = Vec::new();

    let t1 = SystemTime::now();
    thread::sleep(d);
    let t2 = SystemTime::now();
    thread::sleep(d);
    let t3 = SystemTime::now();
    thread::sleep(d);
    let t4 = SystemTime::now();
    thread::sleep(d);

    log.push(Action::new(
      (0, 0),
      StackOp::Pop(Some(1)),
      t1,
      t3));
    log.push(Action::new(
      (1, 0),
      StackOp::Push(1),
      t2,
      t4));

    let mut slin = StackLinearization::new();
    let history = slin.linearize(log).expect(
      "No valid linearization found.");

    assert_eq!(history[0].get_id(), (1, 0));
    assert_eq!(history[1].get_id(), (0, 0));
  }

  #[test]
  fn identical_time_linearization_test() {
    let d = Duration::from_millis(10);
    let n = 10;
    let mut actions = Vec::new();

    let t1 = SystemTime::now();
    thread::sleep(d);
    let t2 = SystemTime::now();

    for i in 0..n {
      let op: StackOp<usize>;

      if i % 2 == 0 {
        op = StackOp::Push(i);
      } else {
        op = StackOp::Pop(Some(i-1));
      }

      actions.push(Action::new(
        (i, 0),
        op,
        t1,
        t2));
    }

    let mut log = Vec::new();
    for i in 0..n {
      log.push(actions[(n-i-1)]);
    }

    let mut slin = StackLinearization::new();
    let history = slin.linearize(log).expect(
      "No valid linearization found.");

    assert_eq!(history.len(), n);
    for i in 0..n {
      if i % 2 == 0 {
        let i_push = history.iter().position(|a| {
          a.get_id() == (i, 0)
        }).unwrap();
        let i_pop = history.iter().position(|a| {
          a.get_id() == (i+1, 0)
        }).unwrap();
        assert!(i_push < i_pop);
      }
    }
  }

  #[test]
  fn invalid_no_overlap_linearization_test() {
    let d = Duration::from_millis(10);
    let mut log = Vec::new();

    let t1 = SystemTime::now();
    thread::sleep(d);
    let t2 = SystemTime::now();
    thread::sleep(d);
    let t3 = SystemTime::now();
    thread::sleep(d);
    let t4 = SystemTime::now();
    thread::sleep(d);

    log.push(Action::new(
      (0, 0),
      StackOp::Pop(Some(1)),
      t1,
      t2));
    log.push(Action::new(
      (1, 0),
      StackOp::Push(1),
      t3,
      t4));

    let mut slin = StackLinearization::new();
    assert_eq!(slin.linearize(log), None);
  }

  #[test]
  fn invalid_overlap_linearization_test() {
    let d = Duration::from_millis(10);
    let mut log = Vec::new();

    let t1 = SystemTime::now();
    thread::sleep(d);
    let t2 = SystemTime::now();
    thread::sleep(d);
    let t3 = SystemTime::now();
    thread::sleep(d);
    let t4 = SystemTime::now();
    thread::sleep(d);

    log.push(Action::new(
      (0, 0),
      StackOp::Pop(Some(1)),
      t1,
      t3));
    log.push(Action::new(
      (1, 0),
      StackOp::Push(2),
      t2,
      t4));

    let mut slin = StackLinearization::new();
    assert_eq!(slin.linearize(log), None);
  }
}


///////////////////////////////////////////////////////////////////////////////
//// Stack Tests
///////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod stack_tests {
  use std::time::SystemTime;
  use super::utilities::*;
  use super::stack;
  use super::stack::*;
  use super::linearization::*;
  use rand::ThreadRng;

  #[derive(Copy)]
  #[derive(Clone)]
  enum StackTestOp {
    Push,
    Pop,
  }

  impl TestOp for StackTestOp {}

  struct StackTester<S> {
    stack: S,
    ops: Vec<(StackTestOp, f64)>,
  }

  impl<S> StackTester<S>
  where S: Stack<i32> {
    pub fn new(stack: S, p_pop: f64) -> Self {
      Self {
        stack: stack,
        ops: vec![(StackTestOp::Push, 1.0 - p_pop),
                  (StackTestOp::Pop,  p_pop)],
      }
    }
  }

  impl<S> Tester for StackTester<S>
  where S: Stack<i32> {
    fn execute_op(&mut self, rng: &mut ThreadRng) {
      match choose_op(rng, &self.ops) {
        StackTestOp::Push => {
          self.stack.push(42);
        }
        StackTestOp::Pop => {
          self.stack.pop();
        }
      }
    }
  }

  #[derive(Clone)]
  struct ConcurrentStackTester<S>
  where S: ConcurrentStack<i32> {
    stack: S,
    ops: Vec<(StackTestOp, f64)>,
  }

  impl<S> ConcurrentStackTester<S>
  where S: ConcurrentStack<i32> {
    pub fn new(stack: S, p_pop: f64) -> Self {
      Self {
        stack: stack,
        ops: vec![(StackTestOp::Push, 1.0 - p_pop),
                  (StackTestOp::Pop,  p_pop)],
      }
    }
  }

  impl<S> ConcurrentTester for ConcurrentStackTester<S>
  where S: ConcurrentStack<i32> {
    type L = StackLinearization<i32>;

    fn execute_op(&mut self, rng: &mut ThreadRng) {
      match choose_op(rng, &self.ops) {
        StackTestOp::Push => {
          self.stack.push(42);
        }
        StackTestOp::Pop => {
          self.stack.pop();
        }
      }
    }

    fn record_op(&mut self, rng: &mut ThreadRng, tid: usize, i: usize) -> Action<<Self::L as Linearization>::P> {
      let start: SystemTime;
      let stop: SystemTime;
      let op: StackOp<i32>;

      match choose_op(rng, &self.ops) {
        StackTestOp::Push => {
          let args = gen_args(rng, 1);
          start = SystemTime::now();
          self.stack.push(args[0]);
          stop = SystemTime::now();
          op = StackOp::Push(args[0]);
        }
        StackTestOp::Pop => {
          start = SystemTime::now();
          let r = self.stack.pop();
          stop = SystemTime::now();
          op = StackOp::Pop(r);
        }
      }

      Action::new((tid, i), op, start, stop)
    }

    fn lin(&self) -> Self::L {
      StackLinearization::new()
    }
  }

  fn test_stack_correctness<S: Stack<i32>>(mut stack: S) {
    assert_eq!(stack.pop(), None);
    assert!(stack.is_empty());

    stack.push(4);

    assert_eq!(stack.size(), 1);
    assert!(!stack.is_empty());

    stack.push(1);

    assert_eq!(stack.size(), 2);
    assert!(!stack.is_empty());

    assert_eq!(stack.pop(), Some(1));

    assert_eq!(stack.size(), 1);
    assert!(!stack.is_empty());

    assert_eq!(stack.pop(), Some(4));

    assert_eq!(stack.size(), 0);
    assert!(stack.is_empty());

    assert_eq!(stack.pop(), None);

    stack.push(3);

    assert_eq!(stack.size(), 1);
    assert!(!stack.is_empty());
  }

  fn test_stack_speed<S: Stack<i32>>(stack: S, t_secs: f64, p_pop: f64) {
    let tester = StackTester::new(stack, p_pop);
    test_throughput(tester, t_secs);
  }

  fn test_stack_concurrent_correctness<S: ConcurrentStack<i32>>(
    stack: S, t_secs: f64, p_pop: f64, n_threads: usize) {
    let tester = ConcurrentStackTester::new(stack, p_pop);
    test_concurrent_correctness(tester, t_secs, n_threads);
  }

  fn test_stack_concurrent_speed<S: ConcurrentStack<i32>>(
    stack: S, t_secs: f64, p_pop: f64, n_threads: usize) {
    let tester = ConcurrentStackTester::new(stack, p_pop);
    test_concurrent_throughput(tester, t_secs, n_threads);
  }

  #[test]
  fn array_stack_correctness() {
    test_stack_correctness(ArrayStack::new());
  }

  #[test]
  fn array_stack_speed() {
    test_stack_speed(ArrayStack::new(), 1.0, 0.5);
  }

  #[test]
  fn list_stack_correctness() {
    test_stack_correctness(ListStack::new());
  }

  #[test]
  fn list_stack_speed() {
    test_stack_speed(ListStack::new(), 1.0, 0.5);
  }

  #[test]
  fn coarse_lock_stack_correctness() {
    test_stack_correctness(CoarseLockStack::new());
  } 

  #[test]
  fn coarse_lock_stack_correctness_concurrent() {
    for _ in 0..10 {
      test_stack_concurrent_correctness(
        CoarseLockStack::new(), 0.0001, 0.8, 10);
    }
  }

  #[test]
  fn coarse_lock_stack_speed() {
    test_stack_speed(CoarseLockStack::new(), 1.0, 0.5);
  }

  #[test]
  fn coarse_lock_stack_speed_concurrent() {
    test_stack_concurrent_speed(
      CoarseLockStack::new(), 1.0, 0.5, 10);
  }

  #[test]
  fn treiber_stack_correctness() {
    test_stack_correctness(TreiberStack::new());
  }

  #[test]
  fn treiber_stack_correctness_concurrent() {
    for _ in 0..10 {
      test_stack_concurrent_correctness(
        stack::TreiberStack::new(), 0.0001, 0.8, 10);
    }
  }

  #[test]
  fn treiber_stack_speed() {
    test_stack_speed(TreiberStack::new(), 1.0, 0.5);
  }

  #[test]
  fn treiber_stack_speed_concurrent() {
    test_stack_concurrent_speed(
      TreiberStack::new(), 1.0, 0.5, 10);
  }
}


///////////////////////////////////////////////////////////////////////////////
//// Queue Tests
///////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod queue_tests {
  use std::time::SystemTime;
  use super::utilities::*;
  use super::queue::*;
  use super::linearization::*;
  use rand::ThreadRng;

  #[derive(Copy)]
  #[derive(Clone)]
  enum QueueTestOp {
    Enq,
    Deq
  }

  impl TestOp for QueueTestOp {}

  struct QueueTester<Q> {
    queue: Q,
    ops: Vec<(QueueTestOp, f64)>,
  }

  impl<Q> QueueTester<Q>
  where Q: Queue<i32> {
    pub fn new(queue: Q, p_enq: f64) -> Self {
      Self {
        queue: queue,
        ops: vec![(QueueTestOp::Enq, p_enq),
                  (QueueTestOp::Deq, 1.0 - p_enq)],
      }
    }
  }

  impl<Q> Tester for QueueTester<Q>
  where Q: Queue<i32> {
    fn execute_op(&mut self, rng: &mut ThreadRng) {
      match choose_op(rng, &self.ops) {
        QueueTestOp::Enq => {
          self.queue.enq(42);
        }
        QueueTestOp::Deq => {
          self.queue.deq();
        }
      }
    }
  }

  #[derive(Clone)]
  struct ConcurrentQueueTester<Q>
  where Q: ConcurrentQueue<i32> {
    queue: Q,
    ops: Vec<(QueueTestOp, f64)>,
  }

  impl<Q> ConcurrentQueueTester<Q>
  where Q: ConcurrentQueue<i32> {
    pub fn new(queue: Q, p_enq: f64) -> Self {
      Self {
        queue: queue,
        ops: vec![(QueueTestOp::Enq, p_enq),
                  (QueueTestOp::Deq, 1.0 - p_enq)],
      }
    }
  }

  impl<Q> ConcurrentTester for ConcurrentQueueTester<Q>
  where Q: ConcurrentQueue<i32> {
    type L = QueueLinearization<i32>;

    fn execute_op(&mut self, rng: &mut ThreadRng) {
      match choose_op(rng, &self.ops) {
        QueueTestOp::Enq => {
          self.queue.enq(42);
        }
        QueueTestOp::Deq => {
          self.queue.deq();
        }
      }
    }

    fn record_op(&mut self, rng: &mut ThreadRng, tid: usize, i: usize) -> Action<<Self::L as Linearization>::P> {
      let start: SystemTime;
      let stop: SystemTime;
      let op: QueueOp<i32>;

      match choose_op(rng, &self.ops) {
        QueueTestOp::Enq => {
          let args = gen_args(rng, 1);
          start = SystemTime::now();
          self.queue.enq(args[0]);
          stop = SystemTime::now();
          op = QueueOp::Enq(args[0]);
        }
        QueueTestOp::Deq => {
          start = SystemTime::now();
          let r = self.queue.deq();
          stop = SystemTime::now();
          op = QueueOp::Deq(r);
        }
      }

      Action::new((tid, i), op, start, stop)
    }

    fn lin(&self) -> Self::L {
      QueueLinearization::new()
    }
  }

  fn test_queue_correctness<Q: Queue<i32>>(mut queue: Q) {
    assert_eq!(queue.deq(), None);
    assert_eq!(queue.size(), 0);
    assert!(queue.is_empty());

    queue.enq(1);

    assert_eq!(queue.size(), 1);
    assert!(!queue.is_empty());

    assert_eq!(queue.deq(), Some(1));
    assert_eq!(queue.size(), 0);
    assert!(queue.is_empty());
    assert_eq!(queue.deq(), None);

    queue.enq(2);

    assert_eq!(queue.size(), 1);

    queue.enq(3);

    assert_eq!(queue.size(), 2);
    assert_eq!(queue.deq(), Some(2));
    assert_eq!(queue.deq(), Some(3));
    assert_eq!(queue.deq(), None);
    assert_eq!(queue.size(), 0);
    assert!(queue.is_empty());

    let n = 100;
    for i in 0..n {
      queue.enq(i);
    }
    for i in 0..n {
      assert_eq!(queue.size(), (n-i) as usize);
      assert_eq!(queue.deq(), Some(i));
    }
    assert_eq!(queue.deq(), None);
    assert_eq!(queue.size(), 0);
  }

  fn test_queue_speed<Q: Queue<i32>>(queue: Q, t_secs: f64, p_enq: f64) {
    let tester = QueueTester::new(queue, p_enq);
    test_throughput(tester, t_secs);
  }

  fn test_queue_concurrent_correctness<Q: ConcurrentQueue<i32>>(
    queue: Q, t_secs: f64, p_enq: f64, n_threads: usize) {
    let tester = ConcurrentQueueTester::new(queue, p_enq);
    test_concurrent_correctness(tester, t_secs, n_threads);
  }

  fn test_queue_concurrent_speed<Q: ConcurrentQueue<i32>>(
    queue: Q, t_secs: f64, p_enq: f64, n_threads: usize) {
    let tester = ConcurrentQueueTester::new(queue, p_enq);
    test_concurrent_throughput(tester, t_secs, n_threads);
  }

  #[test]
  fn list_queue_correctness() {
    test_queue_correctness(ListQueue::new());
  }

  #[test]
  fn list_queue_speed() {
    test_queue_speed(ListQueue::new(), 1.0, 0.5);
  }

  #[test]
  fn coarse_lock_queue_correctness() {
    test_queue_correctness(CoarseLockQueue::new());
  }

  #[test]
  fn coarse_lock_queue_correctness_concurrent() {
    for _ in 0..10 {
      test_queue_concurrent_correctness(
        CoarseLockQueue::new(), 0.0001, 0.2, 10);
    }
  }

  #[test]
  fn coarse_lock_queue_speed() {
    test_queue_speed(CoarseLockQueue::new(), 1.0, 0.5);
  }

  #[test]
  fn coarse_lock_queue_speed_concurrent() {
    test_queue_concurrent_speed(
      CoarseLockQueue::new(), 1.0, 0.5, 10);
  }

  #[test]
  fn ms_queue_correctness() {
    test_queue_correctness(MSQueue::new());
  }

  #[test]
  fn ms_queue_correctness_concurrent() {
    for _ in 0..10 {
      test_queue_concurrent_correctness(
        MSQueue::new(), 0.0001, 0.2, 10);
    }
  }

  #[test]
  fn ms_queue_speed() {
    test_queue_speed(MSQueue::new(), 1.0, 0.5);
  }

  #[test]
  fn ms_queue_speed_concurrent() {
    test_queue_concurrent_speed(
      MSQueue::new(), 1.0, 0.5, 10);
  }
}


///////////////////////////////////////////////////////////////////////////////
//// Dictionary Tests
///////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod dict_tests {
  use std::time::SystemTime;
  use super::utilities::*;
  use super::dict::*;
  use super::linearization::*;
  use rand::ThreadRng;

  #[derive(Copy)]
  #[derive(Clone)]
  enum DictTestOp {
    Get,
    Put,
    Remove,
  }

  impl TestOp for DictTestOp {}

  struct DictTester<D> {
    dict: D,
    ops: Vec<(DictTestOp, f64)>,
  }

  impl<D> DictTester<D>
  where D: Dict<i32,i32> {
    pub fn new(dict: D, p_get: f64, p_put: f64) -> Self {
      Self {
        dict: dict,
        ops: vec![(DictTestOp::Get,    p_get),
                  (DictTestOp::Put,    p_put),
                  (DictTestOp::Remove, 1.0 - p_get - p_put)],
      }
    }
  }

  impl<D> Tester for DictTester<D>
  where D: Dict<i32,i32> {
    fn execute_op(&mut self, rng: &mut ThreadRng) {
      match choose_op(rng, &self.ops) {
        DictTestOp::Get => {
          let args = gen_args(rng, 1);
          self.dict.get(&args[0]);
        }
        DictTestOp::Put => {
          let args = gen_args(rng, 2);
          self.dict.put(args[0], args[1]);
        }
        DictTestOp::Remove => {
          let args = gen_args(rng, 1);
          self.dict.remove(&args[0]);
        }
      }
    }
  }

  #[derive(Clone)]
  struct ConcurrentDictTester<D>
  where D: ConcurrentDict<i32,i32> {
    dict: D,
    ops: Vec<(DictTestOp, f64)>,
  }

  impl<D> ConcurrentDictTester<D>
  where D: ConcurrentDict<i32,i32> {
    pub fn new(dict: D, p_get: f64, p_put: f64) -> Self {
      Self {
        dict: dict,
        ops: vec![(DictTestOp::Get,    p_get),
                  (DictTestOp::Put,    p_put),
                  (DictTestOp::Remove, 1.0 - p_get - p_put)],
      }
    }
  }

  impl<D> ConcurrentTester for ConcurrentDictTester<D>
  where D: ConcurrentDict<i32,i32> {
    type L = DictLinearization<i32,i32>;

    fn execute_op(&mut self, rng: &mut ThreadRng) {
      match choose_op(rng, &self.ops) {
        DictTestOp::Get => {
          let args = gen_args(rng, 1);
          let k = args[0].abs() % 50;
          self.dict.get(&k);
        }
        DictTestOp::Put => {
          let args = gen_args(rng, 2);
          let k = args[0].abs() % 50;
          self.dict.put(k, args[1]);
        }
        DictTestOp::Remove => {
          let args = gen_args(rng, 1);
          let k = args[0].abs() % 50;
          self.dict.remove(&k);
        }
      }
    }

    fn record_op(&mut self, rng: &mut ThreadRng, tid: usize, i: usize) -> Action<<Self::L as Linearization>::P> {
      let start: SystemTime;
      let stop: SystemTime;
      let op: DictOp<i32,i32>;

      match choose_op(rng, &self.ops) {
        DictTestOp::Get => {
          let args = gen_args(rng, 1);
          let k = args[0].abs() % 50;
          start = SystemTime::now();
          let r = self.dict.get(&k);
          stop = SystemTime::now();
          op = DictOp::Get(k, r);
        }
        DictTestOp::Put => {
          let args = gen_args(rng, 2);
          let k = args[0].abs() % 50;
          start = SystemTime::now();
          let r = self.dict.put(k, args[1]);
          stop = SystemTime::now();
          op = DictOp::Put(k, args[1], r);
        }
        DictTestOp::Remove => {
          let args = gen_args(rng, 1);
          let k = args[0].abs() % 50;
          start = SystemTime::now();
          let r = self.dict.remove(&k);
          stop = SystemTime::now();
          op = DictOp::Remove(k, r);
        }
      }

      Action::new((tid, i), op, start, stop)
    }

    fn lin(&self) -> Self::L {
      DictLinearization::new()
    }
  }

  fn test_dict_correctness<D: Dict<i32,i32>>(mut dict: D) {
    assert_eq!(dict.get(&0), None);
    assert_eq!(dict.size(), 0);
    assert!(dict.is_empty());
    assert_eq!(dict.get(&1), None);

    dict.put(0, 1);

    assert_eq!(dict.get(&0), Some(1));
    assert_eq!(dict.size(), 1);
    assert!(!dict.is_empty());

    assert_eq!(dict.remove(&0), Some(1));

    assert_eq!(dict.get(&0), None);
    assert_eq!(dict.size(), 0);
    assert!(dict.is_empty());
    assert_eq!(dict.get(&1), None);

    dict.put(0, 2);

    assert_eq!(dict.get(&0), Some(2));
    assert_eq!(dict.size(), 1);
    assert!(!dict.is_empty());

    dict.put(0, 3);

    assert_eq!(dict.get(&0), Some(3));
    assert_eq!(dict.size(), 1);
    assert!(!dict.is_empty());

    dict.put(1, 0);

    assert_eq!(dict.get(&0), Some(3));
    assert_eq!(dict.get(&1), Some(0));
    assert_eq!(dict.size(), 2);
    assert!(!dict.is_empty());

    dict.put(1, 1);

    assert_eq!(dict.get(&0), Some(3));
    assert_eq!(dict.get(&1), Some(1));
    assert_eq!(dict.size(), 2);
    assert!(!dict.is_empty());

    assert_eq!(dict.remove(&1), Some(1));

    assert_eq!(dict.get(&0), Some(3));
    assert_eq!(dict.get(&1), None);
    assert_eq!(dict.size(), 1);
    assert!(!dict.is_empty());

    dict.put(1, 5);

    assert_eq!(dict.get(&0), Some(3));
    assert_eq!(dict.get(&1), Some(5));
    assert_eq!(dict.size(), 2);
    assert!(!dict.is_empty());

    assert_eq!(dict.remove(&2), None);

    assert_eq!(dict.get(&0), Some(3));
    assert_eq!(dict.get(&1), Some(5));
    assert_eq!(dict.get(&2), None);
    assert_eq!(dict.size(), 2);
    assert!(!dict.is_empty());

    assert_eq!(dict.remove(&0), Some(3));
    assert_eq!(dict.remove(&1), Some(5));

    assert_eq!(dict.get(&0), None);
    assert_eq!(dict.get(&1), None);
    assert_eq!(dict.get(&2), None);
    assert_eq!(dict.size(), 0);
    assert!(dict.is_empty());

    let n = 100;

    for i in 0..n {
      dict.put(i, i+1);
    }
    assert_eq!(dict.size(), n as usize);
    assert!(!dict.is_empty());
    for i in 0..n {
      assert_eq!(dict.get(&i), Some(i+1));
    }

    for i in n..2*n {
      assert_eq!(dict.remove(&i), None);
    }
    for i in 0..n {
      assert_eq!(dict.remove(&i), Some(i+1));
    }
    assert_eq!(dict.size(), 0);
    assert!(dict.is_empty());
    for i in 0..n {
      assert_eq!(dict.get(&i), None);
    }
  }

  fn test_dict_throughput<D: Dict<i32,i32>>(
    dict: D, t_secs: f64, p_get: f64, p_put: f64) {
    let tester = DictTester::new(dict, p_get, p_put);
    test_throughput(tester, t_secs);
  }

  fn test_dict_concurrent_correctness<D: ConcurrentDict<i32,i32>>(
    dict: D, t_secs: f64, p_get: f64, p_put: f64, n_threads: usize) {
    let tester = ConcurrentDictTester::new(dict, p_get, p_put);
    test_concurrent_correctness(tester, t_secs, n_threads);
  }

  fn test_dict_concurrent_throughput<D: ConcurrentDict<i32,i32>>(
    dict: D, t_secs: f64, p_get: f64, p_put: f64, n_threads: usize) {
    let tester = ConcurrentDictTester::new(dict, p_get, p_put);
    test_concurrent_throughput(tester, t_secs, n_threads);
  }

  #[test]
  fn ht_dict_correctness() {
    test_dict_correctness(HtDict::new());
  }

  #[test]
  fn ht_dict_speed() {
    test_dict_throughput(HtDict::new(), 1.0, 0.33, 0.33);
  }

  #[test]
  fn coarse_lock_ht_dict_correctness() {
    test_dict_correctness(CoarseLockHtDict::new());
  }

  #[test]
  fn coarse_lock_ht_dict_correctness_concurrent() {
    for _ in 0..10 {
      test_dict_concurrent_correctness(
        CoarseLockHtDict::new(), 0.0001, 0.70, 0.20, 10);
    }
  }

  #[test]
  fn coarse_lock_ht_dict_speed() {
    test_dict_throughput(CoarseLockHtDict::new(), 1.0, 0.33, 0.33);
  }

  #[test]
  fn coarse_lock_ht_dict_speed_concurrent() {
    test_dict_concurrent_throughput(
      CoarseLockHtDict::new(), 1.0, 0.33, 0.33, 10);
  }

  #[test]
  fn skiplist_dict_correctness() {
    test_dict_correctness(Skiplist::new());
  }

  #[test]
  fn skiplist_dict_speed() {
    test_dict_throughput(Skiplist::new(), 1.0, 0.33, 0.33);
  }
}
