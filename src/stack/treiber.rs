use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::ptr;
use crossbeam::epoch::{self, Atomic, Owned};
use super::*;

struct Node<T> {
  data: T,
  next: Atomic<Node<T>>,
}

/// A lock-free `ConcurrentStack<T>` implementation.
pub struct TreiberStack<T> {
  head: Arc<Atomic<Node<T>>>,
}

impl<T> Stack<T> for TreiberStack<T> {
  fn new() -> Self {
    TreiberStack {
      head: Arc::new(Atomic::null()),
    }
  }

  fn push(&mut self, elem: T) {
    let mut n = Owned::new(Node {
      data: elem,
      next: Atomic::null(),
    });
    let guard = epoch::pin();

    loop {
      let head = self.head.load(Ordering::Relaxed, &guard);
      n.next.store_shared(head, Ordering::Relaxed);
      match self.head.cas_and_ref(head, n, Ordering::Release, &guard) {
        Ok(_) => {
          return
        },
        Err(owned) => {
          n = owned;
        },
      }
    }
  }

  fn pop(&mut self) -> Option<T> {
    let guard = epoch::pin();

    loop {
      match self.head.load(Ordering::Acquire, &guard) {
        None => return None,
        Some(head) => {
          let n = head.next.load(Ordering::Relaxed, &guard);
          if self.head.cas_shared(Some(head), n, Ordering::Release) {
            unsafe {
              guard.unlinked(head);
              return Some(ptr::read(&(*head).data))
            }
          }
        },
      }
    }
  }

  fn is_empty(&self) -> bool {
    let guard = epoch::pin();
    self.head.load(Ordering::Relaxed, &guard).is_none()
  }

  fn size(&self) -> usize {
    let guard = epoch::pin();
    let mut count: usize = 0;

    let mut n = self.head.load(Ordering::Relaxed, &guard);
    while n.is_some() {
      count += 1;
      n = n.unwrap().next.load(Ordering::Relaxed, &guard);
    }

    count
  }
}

impl<T> Clone for TreiberStack<T> {
  fn clone(&self) -> Self {
    Self {
      head: self.head.clone(),
    }
  }
}

impl<T> ConcurrentStack<T> for TreiberStack<T> 
where T: Send + Sync {}