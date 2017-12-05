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


#[cfg(test)]
mod dict_tests {
  use std::time::Instant;
  use rand::ThreadRng;
  use ::testing::*;
  use ::linearization::*;
  use super::*;

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
    n: usize,
    i: i32,
    ops: Vec<(DictTestOp, f64)>,
  }

  impl<D> DictTester<D>
  where D: Dict<i32,i32> {
    pub fn new(dict: D, n: usize, p_get: f64, p_put: f64) -> Self {
      Self {
        dict: dict,
        n: n,
        i: 0,
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
          self.dict.get(&self.i);
        }
        DictTestOp::Put => {
          self.dict.put(self.i, 42);
        }
        DictTestOp::Remove => {
          self.dict.remove(&self.i);
        }
      }

      self.i = (self.i+1) % self.n as i32;
    }
  }

  #[derive(Clone)]
  struct ConcurrentDictTester<D>
  where D: ConcurrentDict<i32,i32> {
    dict: D,
    n: usize,
    i: i32,
    ops: Vec<(DictTestOp, f64)>,
  }

  impl<D> ConcurrentDictTester<D>
  where D: ConcurrentDict<i32,i32> {
    pub fn new(dict: D, n: usize, p_get: f64, p_put: f64) -> Self {
      Self {
        dict: dict,
        n: n,
        i: 0,
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
          self.dict.get(&self.i);
        }
        DictTestOp::Put => {
          self.dict.put(self.i, 42);
        }
        DictTestOp::Remove => {
          self.dict.remove(&self.i);
        }
      }

      self.i = (self.i+1) % self.n as i32;
    }

    fn record_op(&mut self, rng: &mut ThreadRng, tid: usize, i: usize) 
                 -> Action<<Self::L as Linearization>::P> 
    {
      let start: Instant;
      let stop: Instant;
      let op: DictOp<i32,i32>;

      match choose_op(rng, &self.ops) {
        DictTestOp::Get => {
          let args = gen_args(rng, 1);
          let k = args[0].abs() % self.n as i32;
          start = Instant::now();
          let r = self.dict.get(&k);
          stop = Instant::now();
          op = DictOp::Get(k, r);
        }
        DictTestOp::Put => {
          let args = gen_args(rng, 2);
          let k = args[0].abs() % self.n as i32;
          start = Instant::now();
          let r = self.dict.put(k, args[1]);
          stop = Instant::now();
          op = DictOp::Put(k, args[1], r);
        }
        DictTestOp::Remove => {
          let args = gen_args(rng, 1);
          let k = args[0].abs() % self.n as i32;
          start = Instant::now();
          let r = self.dict.remove(&k);
          stop = Instant::now();
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
    dict: D, n: usize, t_secs: f64, p_get: f64, p_put: f64) {
    let tester = DictTester::new(dict, n, p_get, p_put);
    test_throughput(tester, t_secs);
  }

  fn test_dict_concurrent_correctness<D: ConcurrentDict<i32,i32>>(
    dict: D, n: usize, t_secs: f64, p_get: f64, p_put: f64, n_threads: usize) {
    let tester = ConcurrentDictTester::new(dict, n, p_get, p_put);
    test_concurrent_correctness(tester, t_secs, n_threads);
  }

  fn test_dict_concurrent_throughput<D: ConcurrentDict<i32,i32>>(
    dict: D, n: usize, t_secs: f64, p_get: f64, p_put: f64, n_threads: usize) {
    let tester = ConcurrentDictTester::new(dict, n, p_get, p_put);
    test_concurrent_throughput(tester, t_secs, n_threads);
  }

  #[test]
  fn ht_dict_correctness() {
    test_dict_correctness(HtDict::new());
  }

  #[test]
  fn ht_dict_speed() {
    test_dict_throughput(HtDict::new(), 50, 1.0, 0.33, 0.33);
  }

  #[test]
  fn coarse_lock_ht_dict_correctness() {
    test_dict_correctness(CoarseLockHtDict::new());
  }

  #[test]
  fn coarse_lock_ht_dict_correctness_concurrent() {
    for _ in 0..20 {
      test_dict_concurrent_correctness(
        CoarseLockHtDict::new(), 10, 0.00005, 0.33, 0.33, 10);
    }
  }

  #[test]
  fn coarse_lock_ht_dict_speed() {
    test_dict_throughput(CoarseLockHtDict::new(), 50, 1.0, 0.33, 0.33);
  }

  #[test]
  fn coarse_lock_ht_dict_speed_concurrent() {
    for i in 0..6 {
      let t = 2usize.pow(i);
      println!("\nThreads: {}", t);
      test_dict_concurrent_throughput(
        CoarseLockHtDict::new(), 50, 1.0, 0.33, 0.33, t);
    }
  }

  #[test]
  fn skiplist_dict_correctness() {
    test_dict_correctness(SkiplistDict::new());
  }

  #[test]
  fn skiplist_dict_speed() {
    test_dict_throughput(SkiplistDict::new(), 50, 1.0, 0.33, 0.33);
  }

  #[test]
  fn lockfree_skiplist_dict_correctness() {
    test_dict_correctness(ConcurrentSkiplistDict::new());
  }

  #[test]
  fn lockfree_skiplist_dict_correctness_concurrent() {
    for _ in 0..20 {
      test_dict_concurrent_correctness(
        ConcurrentSkiplistDict::new(), 10, 0.00005, 0.33, 0.33, 10);
    }
  }

  #[test]
  fn lockfree_skiplist_dict_speed() {
    test_dict_throughput(ConcurrentSkiplistDict::new(), 50, 1.0, 0.33, 0.33);
  }

  #[test]
  fn lockfree_skiplist_dict_speed_concurrent() {
    for i in 0..6 {
      let t = 2usize.pow(i);
      println!("\nThreads: {}", t);
      test_dict_concurrent_throughput(
        ConcurrentSkiplistDict::new(), 50, 1.0, 0.33, 0.33, t);
    }
  }
}
