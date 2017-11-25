use super::*;

type Link<T> = Option<Box<Node<T>>>;

struct Node<T> {
  elem: T,
  next: Link<T>,
}

/// A list-based `Stack<T>`.
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
