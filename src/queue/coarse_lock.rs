use std::sync::{Mutex, Arc};
use super::*;

/// A `ConcurrentQueue<T>` that uses a single mutex to wrap a `ListQueue<T>`.
pub struct CoarseLockQueue<T> {
  arc: Arc<Mutex<ListQueue<T>>>,
}

impl<T> Queue<T> for CoarseLockQueue<T> {
  fn new() -> Self {
    Self {
      arc: Arc::new(Mutex::new(ListQueue::new())),
    }
  }

  fn enq(&mut self, elem: T) {
    self.arc.lock().unwrap().enq(elem);
  }

  fn deq(&mut self) -> Option<T> {
    self.arc.lock().unwrap().deq()
  }

  fn is_empty(&self) -> bool {
    self.arc.lock().unwrap().is_empty()
  }

  fn size(&self) -> usize {
    self.arc.lock().unwrap().size()
  }
}

impl<T> Clone for CoarseLockQueue<T> {
  fn clone(&self) -> Self {
    Self {
      arc: self.arc.clone()
    }
  }
}

unsafe impl<T> Send for CoarseLockQueue<T>
where T: Send {}

unsafe impl<T> Sync for CoarseLockQueue<T>
where T: Sync {}

impl<T> ConcurrentQueue<T> for CoarseLockQueue<T> 
where T: Send + Sync {}
