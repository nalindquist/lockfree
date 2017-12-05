//! Priority queue implementations
//!
//! This module provides one sequential priority queue, the `HeapPQueue`,
//! which is based on Rust's `BinaryHeap` type.
//!
//! This module also provides two concurrent priority queues. The 
//! `CoarseLockHeapPQueue` uses a single mutex to wrap a `HeapPQueue`. The
//! `SkiplistPQueue` uses a lock-free skiplist to implement a priority
//! queue, as described by *The Art of Multiprocessor Programming*. The
//! algorithm has been modified using a timestamping idea from [this article]
//! (http://people.csail.mit.edu/shanir/publications/Priority_Queues.pdf)
//! to make it linearizeable. The `SkiplistPQueue` also relies on Aaron Turon's 
//! [epoch-based reclamation](https://aturon.github.io/blog/2015/08/27/epoch/) 
//! for garbage collection.
//!
//! Currently, the priority queues implemented in this module do not
//! allow for multiple elements of the same priority.

mod heap;
mod coarse_lock_heap;
mod skiplist;

pub use self::heap::HeapPQueue;
pub use self::coarse_lock_heap::CoarseLockHeapPQueue;
pub use self::skiplist::SkiplistPQueue;

/// The `PQueue<T>` abstract data type.
pub trait PQueue<T> {
  /// Creates a new, empty priority queue.
  fn new() -> Self;

  /// Inserts an element into the priority queue as long as no element
  /// of equal priority exists. Returns true if the insert succeeded.
  fn insert(&mut self, elem: T) -> bool;

  /// Removes the minimum element from the priority queue, if present.
  fn remove_min(&mut self) -> Option<T>;

  /// Predicate to test that the priority queue is empty.
  fn is_empty(&self) -> bool;

  /// Returns the number of elements in the priority queue.
  fn size(&self) -> usize;
}

/// The specification for a thread-safe `PQueue<T>`.
pub trait ConcurrentPQueue<T>: PQueue<T> + Clone + Send + Sync {}


#[cfg(test)]
mod pqueue_tests {
  use std::time::Instant;
  use rand::ThreadRng;
  use ::testing::*;
  use ::linearization::*;
  use super::*;

  #[derive(Copy)]
  #[derive(Clone)]
  enum PqTestOp {
    Insert,
    RemoveMin,
  }

  impl TestOp for PqTestOp {}

  struct PqTester<P> {
    pq: P,
    n: usize,
    i: i32,
    ops: Vec<(PqTestOp, f64)>,
  }

  impl<P> PqTester<P>
  where P: PQueue<i32> {
    pub fn new(pq: P, n: usize, p_insert: f64) -> Self {
      Self {
        pq: pq,
        n: n,
        i: 0,
        ops: vec![(PqTestOp::Insert,    p_insert),
                  (PqTestOp::RemoveMin, 1.0 - p_insert)],
      }
    }
  }

  impl<P> Tester for PqTester<P>
  where P: PQueue<i32> {
    fn execute_op(&mut self, rng: &mut ThreadRng) {
      match choose_op(rng, &self.ops) {
        PqTestOp::Insert => {
          self.pq.insert(self.i);
        }
        PqTestOp::RemoveMin => {
          self.pq.remove_min();
        }
      }

      self.i = (self.i+1) % self.n as i32;
    }
  }

  #[derive(Clone)]
  struct ConcurrentPqTester<P>
  where P: ConcurrentPQueue<i32> {
    pq: P,
    n: usize,
    i: i32,
    ops: Vec<(PqTestOp, f64)>,
  }

  impl<P> ConcurrentPqTester<P>
  where P: ConcurrentPQueue<i32> {
    pub fn new(pq: P, n: usize, p_insert: f64) -> Self {
      Self {
        pq: pq,
        n: n,
        i: 0,
        ops: vec![(PqTestOp::Insert,    p_insert),
                  (PqTestOp::RemoveMin, 1.0 - p_insert)],
      }
    }
  }

  impl<P> ConcurrentTester for ConcurrentPqTester<P>
  where P: ConcurrentPQueue<i32> {
    type L = PQueueLinearization<i32>;

    fn execute_op(&mut self, rng: &mut ThreadRng) {
      match choose_op(rng, &self.ops) {
        PqTestOp::Insert => {
          self.pq.insert(self.i);
        }
        PqTestOp::RemoveMin => {
          self.pq.remove_min();
        }
      }

      self.i = (self.i+1) % self.n as i32;
    }

    fn record_op(&mut self, rng: &mut ThreadRng, tid: usize, i: usize) 
                 -> Action<<Self::L as Linearization>::P> 
    {
      let start: Instant;
      let stop: Instant;
      let op: PQueueOp<i32>;

      match choose_op(rng, &self.ops) {
        PqTestOp::Insert => {
          let args = gen_args(rng, 1);
          let i = args[0].abs() % self.n as i32;
          start = Instant::now();
          let c = self.pq.insert(i);
          stop = Instant::now();
          op = PQueueOp::Insert(i, c);
        }
        PqTestOp::RemoveMin => {
          start = Instant::now();
          let r = self.pq.remove_min();
          stop = Instant::now();
          op = PQueueOp::RemoveMin(r);
        }
      }

      Action::new((tid, i), op, start, stop)
    }

    fn lin(&self) -> Self::L {
      PQueueLinearization::new()
    }
  }

  fn test_pqueue_correctness<P: PQueue<i32>>(mut pq: P) {
    assert!(pq.is_empty());
    assert_eq!(pq.size(), 0);
    assert_eq!(pq.remove_min(), None);

    pq.insert(1);

    assert!(!pq.is_empty());
    assert_eq!(pq.size(), 1);
    assert_eq!(pq.remove_min(), Some(1));
    assert!(pq.is_empty());
    assert_eq!(pq.size(), 0);
    assert_eq!(pq.remove_min(), None);

    pq.insert(1);

    assert!(!pq.is_empty());
    assert_eq!(pq.size(), 1);
    assert_eq!(pq.remove_min(), Some(1));
    assert!(pq.is_empty());
    assert_eq!(pq.size(), 0);
    assert_eq!(pq.remove_min(), None);

    pq.insert(2);

    assert!(!pq.is_empty());
    assert_eq!(pq.size(), 1);
    assert_eq!(pq.remove_min(), Some(2));
    assert!(pq.is_empty());
    assert_eq!(pq.size(), 0);
    assert_eq!(pq.remove_min(), None);

    pq.insert(10);
    pq.insert(5);

    assert!(!pq.is_empty());
    assert_eq!(pq.size(), 2);
    assert_eq!(pq.remove_min(), Some(5));
    assert!(!pq.is_empty());
    assert_eq!(pq.size(), 1);
    assert_eq!(pq.remove_min(), Some(10));
    assert!(pq.is_empty());
    assert_eq!(pq.size(), 0);
    assert_eq!(pq.remove_min(), None);

    pq.insert(5);
    pq.insert(10);

    assert!(!pq.is_empty());
    assert_eq!(pq.size(), 2);
    assert_eq!(pq.remove_min(), Some(5));
    assert!(!pq.is_empty());
    assert_eq!(pq.size(), 1);
    assert_eq!(pq.remove_min(), Some(10));
    assert!(pq.is_empty());
    assert_eq!(pq.size(), 0);
    assert_eq!(pq.remove_min(), None);

    // pq.insert(5);
    // pq.insert(5);

    // assert!(!pq.is_empty());
    // assert_eq!(pq.size(), 2);
    // assert_eq!(pq.remove_min(), Some(5));
    // assert!(!pq.is_empty());
    // assert_eq!(pq.size(), 1);
    // assert_eq!(pq.remove_min(), Some(5));
    // assert!(pq.is_empty());
    // assert_eq!(pq.size(), 0);
    // assert_eq!(pq.remove_min(), None);

    let n = 100;

    for i in (0..n).rev() {
      assert_eq!(pq.size(), n-i-1);
      pq.insert(i as i32);
    }

    assert_eq!(pq.size(), n);
    for i in 0..n {
      assert_eq!(pq.remove_min(), Some(i as i32));
      assert_eq!(pq.size(), n-i-1);
    }
    for _ in 0..n {
      assert_eq!(pq.remove_min(), None);
      assert_eq!(pq.size(), 0);
    }
  }

  fn test_pqueue_throughput<P: PQueue<i32>>(
    pq: P, n: usize, t_secs: f64, p_insert: f64) {
    let tester = PqTester::new(pq, n, p_insert);
    test_throughput(tester, t_secs);
  }

  fn test_pqueue_concurrent_correctness<P: ConcurrentPQueue<i32>>(
    pq: P, n: usize, t_secs: f64, p_insert: f64, n_threads: usize) {
    let tester = ConcurrentPqTester::new(pq, n, p_insert);
    test_concurrent_correctness(tester, t_secs, n_threads);
  }

  fn test_pqueue_concurrent_throughput<P: ConcurrentPQueue<i32>>(
    pq: P, n: usize, t_secs: f64, p_insert: f64, n_threads: usize) {
    let tester = ConcurrentPqTester::new(pq, n, p_insert);
    test_concurrent_throughput(tester, t_secs, n_threads);
  }

  #[test]
  fn heap_pqueue_correctness() {
    test_pqueue_correctness(HeapPQueue::new());
  }

  #[test]
  fn heap_pqueue_speed() {
    test_pqueue_throughput(HeapPQueue::new(), 50, 1.0, 0.5);
  }

  #[test]
  fn coarse_lock_heap_pqueue_correctness() {
    test_pqueue_correctness(CoarseLockHeapPQueue::new());
  }

  #[test]
  fn coarse_lock_heap_pqueue_correctness_concurrent() {
    for _ in 0..20 {
      test_pqueue_concurrent_correctness(
        CoarseLockHeapPQueue::new(), 50, 0.00005, 0.5, 10);
    }
  }

  #[test]
  fn coarse_lock_heap_pqueue_speed() {
    test_pqueue_throughput(CoarseLockHeapPQueue::new(), 50, 1.0, 0.5);
  }

  #[test]
  fn coarse_lock_heap_pqueue_speed_concurrent() {
    for i in 0..6 {
      let t = 2usize.pow(i);
      println!("\nThreads: {}", t);
      test_pqueue_concurrent_throughput(
        CoarseLockHeapPQueue::new(), 50, 1.0, 0.5, t);
    }
  }

  #[test]
  fn skiplist_pqueue_correctness() {
    test_pqueue_correctness(SkiplistPQueue::new());
  }

  #[test]
  fn skiplist_pqueue_correctness_concurrent() {
    for _ in 0..20 {
      test_pqueue_concurrent_correctness(
        SkiplistPQueue::new(), 50, 0.00005, 0.5, 10);
    }
  }

  #[test]
  fn skiplist_pqueue_speed() {
    test_pqueue_throughput(SkiplistPQueue::new(), 50, 1.0, 0.5);
  }

  #[test]
  fn skiplist_pqueue_speed_concurrent() {
    for i in 0..6 {
      let t = 2usize.pow(i);
      println!("\nThreads: {}", t);
      test_pqueue_concurrent_throughput(
        SkiplistPQueue::new(), 50, 1.0, 0.5, t);
    }
  }
}
