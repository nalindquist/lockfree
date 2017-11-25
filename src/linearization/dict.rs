use std::hash::Hash;
use std::collections::HashMap;
use super::*;

/// Represents an operation performed by a `Dict<K,V>`.
#[derive(Debug)]
#[derive(Copy)]
#[derive(Clone)]
pub enum DictOp<K,V> 
where K: Copy + Clone + Debug, V: Copy + Clone + Debug {
  Get(K, Option<V>),
  Put(K, V, Option<V>),
  Remove(K, Option<V>),
}

impl<K,V> Op for DictOp<K,V> 
where K: Copy + Clone + Debug, V: Copy + Clone + Debug {}

/// An implementation of `Linearization` for a `Dict<K,V>`.
#[derive(Clone)]
pub struct DictLinearization<K,V> 
where K: Copy + Clone + Debug + Eq + Hash, V: Copy + Clone + Debug + Eq {
  state: HashMap<K,V>,
  path: Vec<Action<DictOp<K,V>>>,
}

impl<K,V> Linearization for DictLinearization<K,V>
where K: Copy + Clone + Debug + Eq + Hash, V: Copy + Clone + Debug + Eq {
  type P = DictOp<K,V>;

  fn new() -> Self {
    Self {
      state: HashMap::new(),
      path: Vec::new(),
    }
  }

  fn push(&mut self, a: Action<Self::P>) {
    match a.get_op() {
      DictOp::Get(k,r) => {
        assert_eq!(self.state.get(&k), r.as_ref());
      }
      DictOp::Put(k,v,_) => {
        self.state.insert(k,v);
      }
      DictOp::Remove(k,r) => {
        assert_eq!(self.state.get(&k), r.as_ref());
        self.state.remove(&k);
      }
    }

    self.path.push(a);
  }

  fn pop(&mut self) {
    self.path.pop().map(|a| {
      match a.get_op() {
        DictOp::Get(k,r) => {
          assert_eq!(self.state.get(&k), r.as_ref());
        }
        DictOp::Put(k,v,r) => {
          assert_eq!(self.state.get(&k), Some(&v));
          self.state.remove(&k);
          r.map(|v| {
            self.state.insert(k,v);
          });
        }
        DictOp::Remove(k,r) => {
          assert_eq!(self.state.get(&k), None);
          r.map(|v| {
            self.state.insert(k,v);
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
      DictOp::Get(k,r) => {
        self.state.get(&k) == r.as_ref()
      }
      DictOp::Put(k,_,r) => {
        self.state.get(&k) == r.as_ref()
      }
      DictOp::Remove(k,r) => {
        self.state.get(&k) == r.as_ref()
      }
    }
  }

  fn get_history(&self) -> Vec<Action<Self::P>> {
    self.path.clone()
  }
}
