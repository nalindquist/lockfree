use std::sync::{Mutex, Arc};
use std::sync::atomic::Ordering;
use std::ptr;

use crossbeam::epoch::{self, Atomic, Owned};


///////////////////////////////////////////////////////////////////////////////
//// Trait Definitions
///////////////////////////////////////////////////////////////////////////////

pub trait Stack<T> {
  fn new() -> Self;
  fn push(&mut self, elem: T);
  fn pop(&mut self) -> Option<T>;
  fn is_empty(&self) -> bool;
  fn size(&self) -> usize;
}

pub trait ConcurrentStack<T>: Stack<T> + Clone + Send + Sync {}


///////////////////////////////////////////////////////////////////////////////
//// ArrayStack
///////////////////////////////////////////////////////////////////////////////

pub struct ArrayStack<T> {
  elems: Vec<T>,
}

impl<T> Stack<T> for ArrayStack<T> {
  fn new() -> Self {
    Self {
      elems: Vec::new(),
    }
  }

  fn push(&mut self, elem: T) {
    self.elems.push(elem)
  }

  fn pop(&mut self) -> Option<T> {
    self.elems.pop()
  }

  fn is_empty(&self) -> bool {
    self.elems.len() == 0
  }

  fn size(&self) -> usize {
    self.elems.len()
  }
}


///////////////////////////////////////////////////////////////////////////////
//// ListStack
///////////////////////////////////////////////////////////////////////////////

type Link<T> = Option<Box<Node<T>>>;

struct Node<T> {
  elem: T,
  next: Link<T>,
}

pub struct ListStack<T> {
  head: Link<T>,
  count: usize,
}

impl<T> Stack<T> for ListStack<T> {
  fn new() -> Self {
    Self {
      head: None,
      count: 0,
    }
  }

  fn push(&mut self, elem: T) {
    let new_node = Box::new(Node {
      elem: elem,
      next: self.head.take(),
    });

    self.head = Some(new_node);
    self.count += 1;
  }

  fn pop(&mut self) -> Option<T> {
    self.head.take().map(|node| {
      let node = *node;
      self.head = node.next;
      self.count -= 1;
      node.elem
    })
  }

  fn is_empty(&self) -> bool {
    self.head.is_none()
  }

  fn size(&self) -> usize {
    self.count
  }
}


///////////////////////////////////////////////////////////////////////////////
//// CoarseLockStack
///////////////////////////////////////////////////////////////////////////////

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


///////////////////////////////////////////////////////////////////////////////
//// TreiberStack
///////////////////////////////////////////////////////////////////////////////

struct TreiberNode<T> {
  data: T,
  next: Atomic<TreiberNode<T>>,
}

pub struct TreiberStack<T> {
  head: Arc<Atomic<TreiberNode<T>>>,
}

impl<T> Stack<T> for TreiberStack<T> {
  fn new() -> Self {
    TreiberStack {
      head: Arc::new(Atomic::null()),
    }
  }

  fn push(&mut self, elem: T) {
    let mut n = Owned::new(TreiberNode {
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
    TreiberStack {
      head: self.head.clone(),
    }
  }
}

impl<T> ConcurrentStack<T> for TreiberStack<T> 
where T: Send + Sync {}
