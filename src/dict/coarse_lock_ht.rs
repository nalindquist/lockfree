use std::hash::Hash;
use std::sync::{Mutex, Arc};
use super::*;

/// A `ConcurrentDict<K,V>` that uses a single mutex to wrap a `HtDict<K,V>`.
pub struct CoarseLockHtDict<K,V> {
  arc: Arc<Mutex<HtDict<K,V>>>,
}

impl<K,V> Dict<K,V> for CoarseLockHtDict<K,V>
where K: Eq + Hash, V: Clone {
  fn new() -> Self {
    Self {
      arc: Arc::new(Mutex::new(HtDict::new())),
    }
  }

  fn get(&self, k: &K) -> Option<V> {
    self.arc.lock().unwrap().get(k)
  }

  fn put(&mut self, k: K, v: V) -> Option<V> {
    self.arc.lock().unwrap().put(k, v)
  }

  fn remove(&mut self, k: &K) -> Option<V> {
    self.arc.lock().unwrap().remove(k)
  }

  fn is_empty(&self) -> bool {
    self.arc.lock().unwrap().is_empty()
  }

  fn size(&self) -> usize {
    self.arc.lock().unwrap().size()
  }
}

impl<K,V> Clone for CoarseLockHtDict<K,V>
where K: Eq + Hash, V: Clone {
  fn clone(&self) -> Self {
    Self {
      arc: self.arc.clone(),
    }
  }
}

impl<K,V> ConcurrentDict<K,V> for CoarseLockHtDict<K,V>
where K: Eq + Hash + Send + Sync, V: Clone + Send + Sync {}
