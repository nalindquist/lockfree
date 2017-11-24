///////////////////////////////////////////////////////////////////////////////
//// 
//// Module: pqueue
////
///////////////////////////////////////////////////////////////////////////////

use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::sync::{Mutex, Arc};


///////////////////////////////////////////////////////////////////////////////
//// Trait Definitions
///////////////////////////////////////////////////////////////////////////////

pub trait PQueue<T> {
  fn new() -> Self;
  fn insert(&mut self, elem: T);
  fn remove_min(&mut self) -> Option<T>;
  fn is_empty(&self) -> bool;
  fn size(&self) -> usize;
}

pub trait ConcurrentPQueue<T>: PQueue<T> + Clone + Send + Sync {}


///////////////////////////////////////////////////////////////////////////////
//// HeapPQueue
///////////////////////////////////////////////////////////////////////////////

#[derive(Eq)]
#[derive(PartialEq)]
struct RevOrd<T> {
  data: T,
}

impl<T> RevOrd<T> {
  fn new(data: T) -> Self {
    Self {
      data: data,
    }
  }

  fn into_data(self) -> T {
    self.data
  }
}

impl<T> Ord for RevOrd<T>
where T: Ord {
  fn cmp(&self, other: &Self) -> Ordering {
    other.data.cmp(&self.data)
  }
}

impl<T> PartialOrd for RevOrd<T>
where T: Ord {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

pub struct HeapPQueue<T> {
  heap: BinaryHeap<RevOrd<T>>,
}

impl<T> PQueue<T> for HeapPQueue<T>
where T: Ord {
  fn new() -> Self {
    Self {
      heap: BinaryHeap::new(),
    }
  }

  fn insert(&mut self, elem: T) {
    self.heap.push(RevOrd::new(elem));
  }

  fn remove_min(&mut self) -> Option<T> {
    self.heap.pop().map(|ro| {
      ro.into_data()
    })
  }

  fn is_empty(&self) -> bool {
    self.heap.is_empty()
  }

  fn size(&self) -> usize {
    self.heap.len()
  }
}


///////////////////////////////////////////////////////////////////////////////
//// CoarseLockHeapPQueue
///////////////////////////////////////////////////////////////////////////////

pub struct CoarseLockHeapPQueue<T> {
  arc: Arc<Mutex<HeapPQueue<T>>>,
}

impl<T> PQueue<T> for CoarseLockHeapPQueue<T> 
where T: Ord {
  fn new() -> Self {
    Self {
      arc: Arc::new(Mutex::new(HeapPQueue::new())),
    }
  }

  fn insert(&mut self, elem: T) {
    self.arc.lock().unwrap().insert(elem);
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
where T: Ord + Send + Sync {}
