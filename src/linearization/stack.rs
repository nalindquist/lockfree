use super::*;

/// Represents an operation performed by a `Stack<T>`.
#[derive(Debug)]
#[derive(Copy)]
#[derive(Clone)]
pub enum StackOp<T> 
where T: Copy + Clone + Debug {
  Push(T),
  Pop(Option<T>),
}

impl<T> Op for StackOp<T> 
where T: Copy + Clone + Debug {}

/// An implementation of `Linearization` for a `Stack<T>`.
#[derive(Clone)]
pub struct StackLinearization<T> 
where T: Copy + Clone + Debug {
  current: Vec<T>,
  old: Vec<T>,
  path: Vec<Action<StackOp<T>>>,
}

impl<T> Linearization for StackLinearization<T>
where T: Copy + Clone + Eq + Debug {
  type P = StackOp<T>;

  fn new() -> Self {
    Self {
      current: Vec::new(),
      old: Vec::new(),
      path: Vec::new(),
    }
  }

  fn push(&mut self, a: Action<Self::P>) {
    match a.get_op() {
      StackOp::Push(v) => {
        self.current.push(v);
      }
      StackOp::Pop(_) => {
        match self.current.pop() {
          None => {},
          Some(v) => self.old.push(v)
        }
      }
    }

    self.path.push(a);
  }

  fn pop(&mut self) {
    match self.path.pop() {
      None => {},
      Some(a) => {
        match a.get_op() {
          StackOp::Push(_) => {
            self.current.pop();
          }
          StackOp::Pop(r) => {
            match r {
              None => {},
              Some(_) => self.current.push(self.old.pop().unwrap()),
            }
          }
        }
      }
    }
  }

  fn peek(&self) -> &Action<Self::P> {
    &self.path[self.path.len() - 1]
  }

  fn contains(&self, a: &Action<Self::P>) -> bool {
    self.path.contains(a)
  }

  fn count(&self) -> usize {
    self.path.len()
  }

  fn is_consistent_with(&self, a: &Action<Self::P>) -> bool {
    match a.get_op() {
      StackOp::Push(_) => true,
      StackOp::Pop(r) => {
        match r {
          None => self.current.len() == 0,
          Some(v) => {
            self.current.len() > 0 && 
            self.current[self.current.len() - 1] == v
          },
        }
      }
    }
  }

  fn get_history(&self) -> Vec<Action<Self::P>> {
    self.path.clone()
  }
}
