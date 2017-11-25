use std::cmp;
use std::hash::Hash;
use std::collections::{BinaryHeap, HashSet};
use super::*;


//////////////////////////////////////////////////////////////////////////////
//// Ordering Reversal
//////////////////////////////////////////////////////////////////////////////

// needed since BinaryHeap is a max-heap

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
  fn cmp(&self, other: &Self) -> cmp::Ordering {
    other.data.cmp(&self.data)
  }
}

impl<T> PartialOrd for RevOrd<T>
where T: Ord {
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
    Some(self.cmp(other))
  }
}


//////////////////////////////////////////////////////////////////////////////
//// HeapPQueue Implementation
//////////////////////////////////////////////////////////////////////////////

/// A `PQueue<T>` implemented using Rust's `BinaryHeap`.
pub struct HeapPQueue<T> {
  heap: BinaryHeap<RevOrd<T>>,
  set: HashSet<T>,
}

impl<T> PQueue<T> for HeapPQueue<T>
where T: Eq + Ord + Hash + Clone {
  fn new() -> Self {
    Self {
      heap: BinaryHeap::new(),
      set: HashSet::new(),
    }
  }

  fn insert(&mut self, elem: T) -> bool {
    if self.set.contains(&elem) {
      false
    } else {
      self.set.insert(elem.clone());
      self.heap.push(RevOrd::new(elem));
      true
    }
  }

  fn remove_min(&mut self) -> Option<T> {
    self.heap.pop().map(|ro| {
      let t = ro.into_data();
      self.set.remove(&t);
      t
    })
  }

  fn is_empty(&self) -> bool {
    self.heap.is_empty()
  }

  fn size(&self) -> usize {
    self.heap.len()
  }
}
