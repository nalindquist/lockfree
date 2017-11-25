use std::ptr;
use std::mem;
use std::sync::Arc;
use std::sync::atomic::Ordering;
use crossbeam::epoch::{self, Atomic, Owned};
use super::*;

struct MSNode<T> {
  data: T,
  next: Atomic<MSNode<T>>,
}

/// A lock-free `ConcurrentQueue<T>` based on the Michael-Scott algorithm.
pub struct MSQueue<T> {
  head: Arc<Atomic<MSNode<T>>>,
  tail: Arc<Atomic<MSNode<T>>>,
}

impl<T> Queue<T> for MSQueue<T> {
  fn new() -> Self {
    let n : Owned<MSNode<T>>;
    unsafe {
      n = Owned::new(MSNode {
        data: mem::uninitialized(),
        next: Atomic::null(),
      });
    }
    let q = Self {
      head: Arc::new(Atomic::null()),
      tail: Arc::new(Atomic::null()),
    };

    let guard = epoch::pin();
    let n = q.head.store_and_ref(n, Ordering::Relaxed, &guard);
    q.tail.store_shared(Some(n), Ordering::Relaxed);

    q
  }

  fn enq(&mut self, elem: T) {
    let mut n = Owned::new(MSNode {
      data: elem,
      next: Atomic::null(),
    });
    let guard = epoch::pin();

    loop {
      let last = self.tail.load(Ordering::Relaxed, &guard).unwrap();

      match last.next.load(Ordering::Relaxed, &guard) {
        None => {
          match last.next.cas_and_ref(None, n, Ordering::Release, &guard) {
            Ok(n) => {
              self.tail.cas_shared(Some(last), Some(n), Ordering::Release);
              return;
            }
            Err(owned) => {
              n = owned;
            }
          }
        }
        Some(next) => {
          self.tail.cas_shared(Some(last), Some(next), Ordering::Release);
        }
      }
    }
  }

  fn deq(&mut self) -> Option<T> {
    let guard = epoch::pin();

    loop {
      let first = self.head.load(Ordering::Acquire, &guard).unwrap();
      let last = self.tail.load(Ordering::Relaxed, &guard).unwrap();
      let next = first.next.load(Ordering::Relaxed, &guard);

      if first.as_raw() == last.as_raw() {
        match next {
          None => {
            return None;
          }
          Some(next) => {
            self.tail.cas_shared(Some(last), Some(next), Ordering::Release);
          }
        }
      } else {
        match next {
          None => {
            panic!("deq: null next ptr");
          }
          Some(next) => {
            if self.head.cas_shared(Some(first), Some(next), Ordering::Release) {
              unsafe {
                guard.unlinked(first);
                return Some(ptr::read(&(*next).data));
              }
            }
          }
        }
      }
    }
  }

  fn is_empty(&self) -> bool {
    let guard = epoch::pin();
    let n = self.head.load(Ordering::Relaxed, &guard).unwrap();
    n.next.load(Ordering::Relaxed, &guard).is_none()
  }

  fn size(&self) -> usize {
    let guard = epoch::pin();
    let mut count: usize = 0;

    let n = self.head.load(Ordering::Relaxed, &guard).unwrap();
    let mut n = n.next.load(Ordering::Relaxed, &guard);
    while n.is_some() {
      count += 1;
      n = n.unwrap().next.load(Ordering::Relaxed, &guard);
    }

    count
  }
}

impl<T> Clone for MSQueue<T> {
  fn clone(&self) -> Self {
    MSQueue {
      head: self.head.clone(),
      tail: self.tail.clone(),
    }
  }
}

unsafe impl<T> Send for MSQueue<T>
where T: Send {}

unsafe impl<T> Sync for MSQueue<T>
where T: Sync {}

impl<T> ConcurrentQueue<T> for MSQueue<T> 
where T: Send + Sync {}