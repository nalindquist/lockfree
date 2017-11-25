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
