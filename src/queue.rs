use std::rc::Rc;
use std::cell::RefCell;
use std::sync::{Mutex, Arc};
use std::sync::atomic::Ordering;
use std::ptr;
use std::mem;

use crossbeam::epoch::{self, Atomic, Owned};


///////////////////////////////////////////////////////////////////////////////
//// Trait Definitions
///////////////////////////////////////////////////////////////////////////////

pub trait Queue<T> {
  fn new() -> Self;
  fn enq(&mut self, elem: T);
  fn deq(&mut self) -> Option<T>;
  fn is_empty(&self) -> bool;
  fn size(&self) -> usize;
}

pub trait ConcurrentQueue<T>: Queue<T> + Clone + Send + Sync {}


///////////////////////////////////////////////////////////////////////////////
//// ListQueue
///////////////////////////////////////////////////////////////////////////////

type Link<T> = Option<Rc<RefCell<Node<T>>>>;

struct Node<T> {
  elem: T,
  next: Link<T>,
}

pub struct ListQueue<T> {
  head: Link<T>,
  tail: Link<T>,
  count: usize,
}

impl<T> Queue<T> for ListQueue<T> {
  fn new() -> Self {
    Self {
      head: None,
      tail: None,
      count: 0,
    }
  }

  fn enq(&mut self, elem: T) {
    let new_node = Rc::new(RefCell::new(Node {
      elem: elem,
      next: None,
    }));

    self.tail.take().map_or_else(
      || {
        self.head = Some(Rc::clone(&new_node));
      },
      |node| {
        node.borrow_mut().next = Some(Rc::clone(&new_node));
      });
    self.tail = Some(Rc::clone(&new_node)); 

    self.count += 1;
  }

  fn deq(&mut self) -> Option<T> {
    self.head.take().map(|node| {
      self.head = node.borrow().next.as_ref().map_or_else(
        || {
          self.tail = None;
          None
        },
        |next| {
          Some(Rc::clone(next))
        });
      self.count -= 1;
      Rc::try_unwrap(node).ok().unwrap().into_inner().elem
    })
  }

  fn is_empty(&self) -> bool {
    self.count == 0
  }

  fn size(&self) -> usize {
    self.count
  }
}


///////////////////////////////////////////////////////////////////////////////
//// CoarseLockQueue
///////////////////////////////////////////////////////////////////////////////

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


///////////////////////////////////////////////////////////////////////////////
//// MSQueue
///////////////////////////////////////////////////////////////////////////////

struct MSNode<T> {
  data: T,
  next: Atomic<MSNode<T>>,
}

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
      let last = self.tail.load(Ordering::SeqCst, &guard).unwrap();

      match last.next.load(Ordering::SeqCst, &guard) {
        None => {
          match last.next.cas_and_ref(None, n, Ordering::SeqCst, &guard) {
            Ok(n) => {
              self.tail.cas_shared(Some(last), Some(n), Ordering::SeqCst);
              return;
            }
            Err(owned) => {
              n = owned;
            }
          }
        }
        Some(next) => {
          self.tail.cas_shared(Some(last), Some(next), Ordering::SeqCst);
        }
      }
      // match self.tail.load(Ordering::SeqCst, &guard) {
      //   None => {
      //     match self.head.cas_and_ref(None, n, Ordering::SeqCst, &guard) {
      //       Ok(n) => {
      //         self.tail.cas_shared(None, Some(n), Ordering::SeqCst);
      //         return;
      //       },
      //       Err(owned) => {
      //         n = owned;
      //         let head = self.head.load(Ordering::SeqCst, &guard);
      //         self.tail.cas_shared(None, head, Ordering::SeqCst);
      //       }
      //     }
      //   },
      //   Some(last) => {
      //     match last.next.load(Ordering::SeqCst, &guard) {
      //       None => {
      //         match last.next.cas_and_ref(None, n, Ordering::SeqCst, &guard) {
      //           Ok(n) => {
      //             self.tail.cas_shared(Some(last), Some(n), Ordering::SeqCst);
      //             return;
      //           },
      //           Err(owned) => {
      //             n = owned;
      //           }
      //         }
      //       }
      //       Some(next) => {
      //         self.tail.cas_shared(Some(last), Some(next), Ordering::SeqCst);
      //       }
      //     }
      //   }
      // }
    }
  }

  fn deq(&mut self) -> Option<T> {
    let guard = epoch::pin();

    loop {
      let first = self.head.load(Ordering::SeqCst, &guard).unwrap();
      let last = self.tail.load(Ordering::SeqCst, &guard).unwrap();
      let next = first.next.load(Ordering::SeqCst, &guard);

      if first.as_raw() == last.as_raw() {
        match next {
          None => {
            return None;
          }
          Some(next) => {
            self.tail.cas_shared(Some(last), Some(next), Ordering::SeqCst);
          }
        }
      } else {
        match next {
          None => {
            panic!("deq: null next ptr");
          }
          Some(next) => {
            if self.head.cas_shared(Some(first), Some(next), Ordering::SeqCst) {
              unsafe {
                guard.unlinked(first);
                return Some(ptr::read(&(*next).data));
              }
            }
          }
        }
      }
      // match self.head.load(Ordering::SeqCst, &guard) {
      //   None => return None,
      //   Some(head) => {
      //     match head.next.load(Ordering::SeqCst, &guard) {
      //       None => {
      //         match self.tail.cas(Some(head), None, Ordering::SeqCst) {
      //           Ok(_) => {
      //             self.head.cas_shared(Some(head), None, Ordering::SeqCst);
      //             unsafe {
      //               guard.unlinked(head);
      //               return Some(ptr::read(head.data))
      //             }
      //           }
      //           Err(_) => {
      //             self.head.cas_shared(Some(head), None, Ordering::SeqCst);
      //           }
      //         }
      //       }
      //       Some(next) => {
      //         if self.head.cas_shared(Some(head), Some(next), Ordering::SeqCst) {
      //           unsafe {
      //             guard.unlinked(head);
      //             return Some(ptr::read(head.data))
      //           }
      //         }
      //       }
      //     }
      //   }
      // }
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
