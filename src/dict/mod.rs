//! Dictionary implementations
//!
//! This module provides two sequential dictionaries. The `HtDict` is a
//! dictionary implemented using Rust's `HashMap` type. The `SkiplistDict` 
//! is based on the skiplist data structure, as outlined by *The Art of 
//! Multiprocessor Programming*.
//!
//! This module also provides two concurrent dictionaries. The
//! `CoarseLockHtDict` uses a single mutex to wrap a `HtDict`. The
//! `ConcurrentSkiplistDict` uses a lock-free skiplist implementation
//! outlined by *The Art of Multiprocessor Programming*. The 
//! `ConcurrentSkiplistDict` also relies on Aaron Turon's [epoch-based 
//! reclamation](https://aturon.github.io/blog/2015/08/27/epoch/) for
//! garbage collection.

mod ht;
mod skiplist;
mod coarse_lock_ht;
mod concurrent_skiplist;

pub use self::ht::HtDict;
pub use self::skiplist::SkiplistDict;
pub use self::coarse_lock_ht::CoarseLockHtDict;
pub use self::concurrent_skiplist::ConcurrentSkiplistDict;

/// The `Dict<K,V>` abstract data type.
pub trait Dict<K,V> {
  /// Creates a new, empty `Dict<K,V>`.
  fn new() -> Self;

  /// Returns the value associated with the given key, if present.
  fn get(&self, k: &K) -> Option<V>;

  /// Adds a new key-value pair to the dictionary. Returns the previous
  /// value, if present.
  fn put(&mut self, k: K, v: V) -> Option<V>;

  /// Removes the key from the dictionary. Returns the associated value,
  /// if present.
  fn remove(&mut self, k: &K) -> Option<V>;

  /// Predicate that tests is the dictionary is empty.
  fn is_empty(&self) -> bool;

  /// Returns the number of key-value pairs in the dictionary.
  fn size(&self) -> usize;
}

/// The specification for a thread-safe `Dict<K,V>`.
pub trait ConcurrentDict<K,V>: Dict<K,V> + Clone + Send + Sync {}
