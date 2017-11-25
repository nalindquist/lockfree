use super::*;

/// Represents an operation performed by a `PQueue<T>`.
#[derive(Debug)]
#[derive(Copy)]
#[derive(Clone)]
pub enum PQueueOp<T> 
where T: Copy + Clone + Debug {
  Insert(T, bool),
  RemoveMin(Option<T>),
}

impl<T> Op for PQueueOp<T>
where T: Copy + Clone + Debug {}

/// An implementation of `Linearization` for a `PQueue<T>`.
#[derive(Clone)]
pub struct PQueueLinearization<T> 
where T: Copy + Clone + Debug + Ord + Eq {
  state: Vec<T>,
  path: Vec<Action<PQueueOp<T>>>,
}

impl<T> Linearization for PQueueLinearization<T>
where T: Copy + Clone + Debug + Ord + Eq {
  type P = PQueueOp<T>;

  fn new() -> Self {
    Self {
      state: Vec::new(),
      path: Vec::new(),
    }
  }

  fn push(&mut self, a: Action<Self::P>) {
    match a.get_op() {
      PQueueOp::Insert(i, c) => {
        if c {
          self.state.push(i);
        }
      }
      PQueueOp::RemoveMin(_) => {
        if self.state.len() > 0 {
          self.state.sort();
          self.state.remove(0);
        }
      }
    }

    self.path.push(a);
  }

  fn pop(&mut self) {
    self.path.pop().map(|a| {
      match a.get_op() {
        PQueueOp::Insert(i, c) => {
          if c {
            let p = self.state.iter().position(|e| *e == i);
            assert!(p.is_some());
            self.state.remove(p.unwrap());
          }
        }
        PQueueOp::RemoveMin(r) => {
          match r {
            None => {
              assert!(self.state.is_empty());
            }
            Some(i) => {
              self.state.push(i);
            }
          }
        }
      }
    });
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
      PQueueOp::Insert(i, c) => {
        let p = self.state.iter().position(|e| *e == i);
        match p {
          None => {
            c
          }
          Some(_) => {
            !c
          }
        }
      }
      PQueueOp::RemoveMin(r) => {
        r.map_or_else(
          || {
            self.state.is_empty()
          },
          |i| {
            let mut state = self.state.clone();
            state.sort();
            !state.is_empty() && state[0] == i
          })
      }
    }
  }

  fn get_history(&self) -> Vec<Action<Self::P>> {
    self.path.clone()
  }
}
