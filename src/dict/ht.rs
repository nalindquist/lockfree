use std::collections::HashMap;
use std::hash::Hash;
use super::*;

/// A `Dict<K,V>` based on Rust's `HashMap`.
pub struct HtDict<K,V> {
  ht: HashMap<K,V>,
}

impl<K,V> Dict<K,V> for HtDict<K,V>
where K: Eq + Hash, V: Clone {
  fn new() -> Self {
    Self {
      ht: HashMap::new()
    }
  }

  fn get(&self, k: &K) -> Option<V> {
    self.ht.get(k).map(|v| {
      v.clone()
    })
  }

  fn put(&mut self, k: K, v: V) -> Option<V> {
    self.ht.insert(k, v)
  }

  fn remove(&mut self, k: &K) -> Option<V> {
    self.ht.remove(k)
  }

  fn is_empty(&self) -> bool {
    self.ht.is_empty()
  }

  fn size(&self) -> usize {
    self.ht.keys().count()
  }
}
