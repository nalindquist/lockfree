//! Queue implementations
//!
//! This module provides one example of a sequential queue: the `ListQueue`,
//! which is implemented using a linked list. The implementation is based
//! on [this blog post](http://cglab.ca/~abeinges/blah/too-many-lists/book/).
//!
//! This module also provides two concurrent queues. The `CoarseLockQueue`
//! uses a single mutex to wrap a `ListQueue`. The `MSQueue` is a
//! lock-free queue based on the Michael-Scott algorithm, as described
//! by *The Art of Multiprocessor Programming*. The `MSQueue` also
//! relies on Aaron Turon's [epoch-based 
//! reclamation](https://aturon.github.io/blog/2015/08/27/epoch/) for 
//! garbage collection.

mod list;
mod coarse_lock;
mod ms;

pub use self::list::ListQueue;
pub use self::coarse_lock::CoarseLockQueue;
pub use self::ms::MSQueue;

/// The `Queue<T>` abstract data type.
pub trait Queue<T> {
  /// Creates a new, empty `Queue<T>`.
  fn new() -> Self;

  /// Enqueues an element onto the queue.
  fn enq(&mut self, elem: T);

  /// Dequeues an element from the queue, if there is one.
  fn deq(&mut self) -> Option<T>;

  /// Predicate that tests if the queue is empty.
  fn is_empty(&self) -> bool;

  /// Returns the number of elements in the queue.
  fn size(&self) -> usize;
}

/// The specification for a thread-safe `Queue<T>`.
pub trait ConcurrentQueue<T>: Queue<T> + Clone + Send + Sync {}


#[cfg(test)]
mod queue_tests {
  use std::time::Instant;
  use rand::ThreadRng;
  use ::testing::*;
  use ::linearization::*;
  use super::*;
  
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
      let start: Instant;
      let stop: Instant;
      let op: QueueOp<i32>;

      match choose_op(rng, &self.ops) {
        QueueTestOp::Enq => {
          let args = gen_args(rng, 1);
          start = Instant::now();
          self.queue.enq(args[0]);
          stop = Instant::now();
          op = QueueOp::Enq(args[0]);
        }
        QueueTestOp::Deq => {
          start = Instant::now();
          let r = self.queue.deq();
          stop = Instant::now();
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
