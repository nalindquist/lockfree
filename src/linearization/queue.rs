use std::collections::VecDeque;
use super::*;

/// Represents an operation performed by a `Queue<T>`.
#[derive(Debug)]
#[derive(Copy)]
#[derive(Clone)]
pub enum QueueOp<T> 
where T: Copy + Clone + Debug {
  Enq(T),
  Deq(Option<T>),
}

impl<T> Op for QueueOp<T>
where T: Copy + Clone + Debug {}

/// An implementation of `Linearization` for a `Queue<T>`.
#[derive(Clone)]
pub struct QueueLinearization<T> 
where T: Copy + Clone + Debug {
  state: VecDeque<T>,
  path: Vec<Action<QueueOp<T>>>,
}

impl<T> Linearization for QueueLinearization<T>
where T: Copy + Clone + Eq + Debug {
  type P = QueueOp<T>;

  fn new() -> Self {
    Self {
      state: VecDeque::new(),
      path: Vec::new(),
    }
  }

  fn push(&mut self, a: Action<Self::P>) {
    match a.get_op() {
      QueueOp::Enq(v) => {
        self.state.push_back(v);
      }
      QueueOp::Deq(_) => {
        self.state.pop_front();
      }
    }

    self.path.push(a);
  }

  fn pop(&mut self) {
    self.path.pop().map(|a| {
      match a.get_op() {
        QueueOp::Enq(_) => {
          self.state.pop_back();
        }
        QueueOp::Deq(r) => {
          r.map(|v| {
            self.state.push_front(v);
          });
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
      QueueOp::Enq(_) => true,
      QueueOp::Deq(r) => {
        r.map_or_else(
          || {
            self.state.len() == 0
          },
          |v| {
            self.state.get(0).map_or_else(
              || {
                false
              },
              |actual| {
                *actual == v
              })
          })
      }
    }
  }

  fn get_history(&self) -> Vec<Action<Self::P>> {
    self.path.clone()
  }
}
