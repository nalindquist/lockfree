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
