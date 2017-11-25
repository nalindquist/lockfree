use std::sync::{Mutex, Arc};
use super::*;

/// A `ConcurrentStack<T>` that uses a single mutex to wrap a `ListStack<T>`.
pub struct CoarseLockStack<T> {
  arc: Arc<Mutex<ListStack<T>>>,
}

impl<T> Stack<T> for CoarseLockStack<T> {
  fn new() -> Self {
    Self {
      arc: Arc::new(Mutex::new(ListStack::new())),
    }
  }

  fn push(&mut self, elem: T) {
    self.arc.lock().unwrap().push(elem);
  }

  fn pop(&mut self) -> Option<T> {
    self.arc.lock().unwrap().pop()
  }

  fn is_empty(&self) -> bool {
    self.arc.lock().unwrap().is_empty()
  }

  fn size(&self) -> usize {
    self.arc.lock().unwrap().size()
  }
}

impl<T> Clone for CoarseLockStack<T> {
  fn clone(&self) -> Self {
    Self {
      arc: self.arc.clone()
    }
  }
}

impl<T> ConcurrentStack<T> for CoarseLockStack<T> 
where T: Send + Sync {}
