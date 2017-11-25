//! Stack implementations
//!
//! This module provides two examples of sequential stacks: an array-based
//! `ArrayStack` and a linked-list-based `ListStack`. The `ListStack` is
//! is based on [this blog post](http://cglab.ca/~abeinges/blah/too-many-lists/book/).
//!
//! This module also provides two examples of concurrent stacks. The
//! `CoarseLockStack` just uses a single mutex around a `ListStack`, while
//! the `TreiberStack` is a lock-free stack. The `TreiberStack` is based
//! on a [blog post](https://aturon.github.io/blog/2015/08/27/epoch/) written
//! by Aaron Turon. 

mod array;
mod list;
mod coarse_lock_list;
mod treiber;

pub use self::array::ArrayStack;
pub use self::list::ListStack;
pub use self::coarse_lock_list::CoarseLockStack;
pub use self::treiber::TreiberStack;

/// The `Stack<T>` abstract data type.
pub trait Stack<T> {
  /// Creates a new, empty `Stack<T>`.
  fn new() -> Self;

  /// Pushes an element onto the stack.
  fn push(&mut self, elem: T);

  /// Pops an element from the stack, if there is one.
  fn pop(&mut self) -> Option<T>;

  /// Predicate that tests if the stack is empty.
  fn is_empty(&self) -> bool;

  /// Returns the number of elements in the stack.
  fn size(&self) -> usize;
}

/// The specification for a thread-safe `Stack`.
pub trait ConcurrentStack<T>: Stack<T> + Clone + Send + Sync {}
