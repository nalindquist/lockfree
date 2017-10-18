use std::rc::Rc;
use std::cell::RefCell;
use std::sync::{Mutex, Arc};
// use std::sync::atomic::Ordering;
// use std::ptr;

//use crossbeam::epoch::{self, Atomic, Owned};


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

unsafe impl<T> Send for ListQueue<T>
where T: Send {}

impl<T> ConcurrentQueue<T> for CoarseLockQueue<T> 
where T: Send + Sync {}
