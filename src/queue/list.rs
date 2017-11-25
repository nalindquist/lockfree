use std::rc::Rc;
use std::cell::RefCell;
use super::*;

type Link<T> = Option<Rc<RefCell<Node<T>>>>;

struct Node<T> {
  elem: T,
  next: Link<T>,
}

/// A list-based sequential `Queue<T>`.
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