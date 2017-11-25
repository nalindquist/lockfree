use super::*;

/// A simple array-based `Stack<T>`. Uses Rust's `Vec<T>`.
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