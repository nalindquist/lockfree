extern crate crossbeam;
extern crate rand;

pub mod stack;
pub mod queue;
pub mod linearization;


///////////////////////////////////////////////////////////////////////////////
//// Utilities
///////////////////////////////////////////////////////////////////////////////


#[cfg(test)]
mod utilities {
  use std::time::Duration;

  pub fn duration_to_ns(d: Duration) -> f64 {
    (d.as_secs() as f64) * 1_000_000_000.0 +
      (d.subsec_nanos() as f64)
  }

  pub fn secs_to_duration(t: f64) -> Duration {
    Duration::new(
      t as u64,
      ((t - ((t as u64) as f64)) * 1_000_000_000.0) as u32)
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

      actions.push(StackAction::new(
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

    log.push(StackAction::new(
      (0, 0),
      StackOp::Pop(Some(1)),
      t1,
      t3));
    log.push(StackAction::new(
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

      actions.push(StackAction::new(
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

    log.push(StackAction::new(
      (0, 0),
      StackOp::Pop(Some(1)),
      t1,
      t2));
    log.push(StackAction::new(
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

    log.push(StackAction::new(
      (0, 0),
      StackOp::Pop(Some(1)),
      t1,
      t3));
    log.push(StackAction::new(
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
  use std::time::{Instant, SystemTime};
  use super::utilities::*;
  use super::stack;
  use super::stack::*;
  use super::linearization::*;
  use crossbeam;
  use rand::{self, Rng};

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

  fn test_stack_speed<S: Stack<i32>>(mut stack: S, t_secs: f64, p_pop: f64) {
    let mut rng = rand::thread_rng();
    let mut n_ops = 0;
    let duration = secs_to_duration(t_secs);
    let start_time = Instant::now();

    let elapsed = loop {
      let f = rng.next_f64();
      if f < p_pop {
        stack.push(42);
      } else {
        stack.pop();
      }
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

  fn test_stack_concurrent_correctness<S: ConcurrentStack<i32>>(
    stack: S, t_secs: f64, p_pop: f64, n_threads: usize) {
    let mut handles = Vec::new();
    let mut log = Vec::new();

    crossbeam::scope(|scope| {
      for tid in 0..n_threads {
        let mut stack = stack.clone();

        let h = scope.spawn(move || {
          let mut rng = rand::thread_rng();
          let mut log = Vec::new();
          let mut i = 0;
          let duration = secs_to_duration(t_secs);
          let start_time = Instant::now();

          loop {
            let op: StackOp<i32>;
            let op_start: SystemTime;
            let op_stop: SystemTime;

            let f = rng.next_f64();
            if f > p_pop {
              let i: i32 = rng.gen();

              op_start = SystemTime::now();
              stack.push(i);
              op_stop = SystemTime::now();

              op = StackOp::Push(i);
            } else {
              op_start = SystemTime::now();
              let output = stack.pop();
              op_stop = SystemTime::now();

              op = StackOp::Pop(output);
            }

            log.push(StackAction::new(
              (tid, i),
              op,
              op_start,
              op_stop));
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

    let mut slin = StackLinearization::new();
    let history = slin.linearize(log).expect(
      "No valid linearization found.");

    write_history(&history, "history.txt");
  }

  fn test_stack_concurrent_speed<S: ConcurrentStack<i32>>(
    stack: S, t_secs: f64, p_pop: f64, n_threads: usize) {
    let mut handles = Vec::new();

    crossbeam::scope(|scope| {
      for _ in 0..n_threads {
        let mut stack = stack.clone();

        let h = scope.spawn(move || {
          let mut rng = rand::thread_rng();
          let mut n_ops = 0;
          let duration = secs_to_duration(t_secs);
          let start_time = Instant::now();

          let elapsed = loop {
            let f = rng.next_f64();
            if f > p_pop {
              stack.push(42);
            } else {
              stack.pop();
            }

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
        CoarseLockStack::new(), 0.00001, 0.5, 10);
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
        stack::TreiberStack::new(), 0.00001, 0.5, 10);
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
  use std::time::{Instant, SystemTime};
  use super::utilities::*;
  use super::queue::*;
  use super::linearization::*;
  use crossbeam;
  use rand::{self, Rng};

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

    let n = 10;
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

  fn test_queue_speed<Q: Queue<i32>>(mut queue: Q, t_secs: f64, p_enq: f64) {
    let mut rng = rand::thread_rng();
    let mut n_ops = 0;
    let duration = secs_to_duration(t_secs);
    let start_time = Instant::now();

    let elapsed = loop {
      let f = rng.next_f64();
      if f < p_enq {
        queue.enq(42);
      } else {
        queue.deq();
      }
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

  fn test_queue_concurrent_correctness<Q: ConcurrentQueue<i32>>(
    queue: Q, t_secs: f64, p_enq: f64, n_threads: usize) {   
    let mut handles = Vec::new();
    let mut log = Vec::new();

    crossbeam::scope(|scope| {
      for tid in 0..n_threads {
        let mut queue = queue.clone();

        let h = scope.spawn(move || {
          let mut rng = rand::thread_rng();
          let mut log = Vec::new();
          let mut i = 0;
          let duration = secs_to_duration(t_secs);
          let start_time = Instant::now();

          loop {
            let op: QueueOp<i32>;
            let op_start: SystemTime;
            let op_stop: SystemTime;

            let f = rng.next_f64();
            if f > p_enq {
              let i: i32 = rng.gen();

              op_start = SystemTime::now();
              queue.enq(i);
              op_stop = SystemTime::now();

              op = QueueOp::Enq(i);
            } else {
              op_start = SystemTime::now();
              let output = queue.deq();
              op_stop = SystemTime::now();

              op = QueueOp::Deq(output);
            }

            log.push(QueueAction::new(
              (tid, i),
              op,
              op_start,
              op_stop));
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

    let mut qlin = QueueLinearization::new();
    let history = qlin.linearize(log).expect(
      "No valid linearization found.");

    write_history(&history, "history.txt");
  }

  fn test_queue_concurrent_speed<Q: ConcurrentQueue<i32>>(
    queue: Q, t_secs: f64, p_enq: f64, n_threads: usize) {
    let mut handles = Vec::new();

    crossbeam::scope(|scope| {
      for _ in 0..n_threads {
        let mut queue = queue.clone();

        let h = scope.spawn(move || {
          let mut rng = rand::thread_rng();
          let mut n_ops = 0;
          let duration = secs_to_duration(t_secs);
          let start_time = Instant::now();

          let elapsed = loop {
            let f = rng.next_f64();
            if f > p_enq {
              queue.enq(42);
            } else {
              queue.deq();
            }

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
        CoarseLockQueue::new(), 0.0001, 0.5, 2);
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
        MSQueue::new(), 0.0001, 0.5, 2);
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
