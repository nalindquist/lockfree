use std::hash::Hash;
use std::sync::{Mutex, Arc};
use super::*;

/// A `ConcurrentPQueue<T>` that using a single mutex to wrap a 
/// `HeapPQueue<T>`.
pub struct CoarseLockHeapPQueue<T> {
  arc: Arc<Mutex<HeapPQueue<T>>>,
}

impl<T> PQueue<T> for CoarseLockHeapPQueue<T> 
where T: Eq + Ord + Hash + Clone {
  fn new() -> Self {
    Self {
      arc: Arc::new(Mutex::new(HeapPQueue::new())),
    }
  }

  fn insert(&mut self, elem: T) -> bool {
    self.arc.lock().unwrap().insert(elem)
  }

  fn remove_min(&mut self) -> Option<T> {
    self.arc.lock().unwrap().remove_min()
  }

  fn is_empty(&self) -> bool {
    self.arc.lock().unwrap().is_empty()
  }

  fn size(&self) -> usize {
    self.arc.lock().unwrap().size()
  }
}

impl<T> Clone for CoarseLockHeapPQueue<T> {
  fn clone(&self) -> Self {
    Self {
      arc: self.arc.clone()
    }
  }
}

impl<T> ConcurrentPQueue<T> for CoarseLockHeapPQueue<T> 
where T: Eq + Ord + Hash + Clone + Send + Sync {}
