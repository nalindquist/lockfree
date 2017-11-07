///////////////////////////////////////////////////////////////////////////////
//// 
//// Module: linearization
////
//// Credits:
////   DFS-based alg. - https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-579.pdf
////
///////////////////////////////////////////////////////////////////////////////

use std::time::SystemTime;
use std::fmt::Debug;
//use std::fs::File;
//use std::io::Write;
use std::hash::Hash;
use std::collections::{VecDeque, HashMap};


///////////////////////////////////////////////////////////////////////////////
//// Trait Definitions
///////////////////////////////////////////////////////////////////////////////

pub trait Op : Copy + Clone + Debug {}

pub trait Linearization
where Self::P: Op {
  type P;

  fn new() -> Self;
  fn push(&mut self, a: Action<Self::P>);
  fn pop(&mut self);
  fn peek(&self) -> &Action<Self::P>;
  fn contains(&self, a: &Action<Self::P>) -> bool;
  fn count(&self) -> usize;
  fn is_consistent_with(&self, a: &Action<Self::P>) -> bool;
  fn get_history(&self) -> Vec<Action<Self::P>>;

  fn linearize(&mut self, mut log: Vec<Action<Self::P>>) -> Option<Vec<Action<Self::P>>> {
    log.sort_by(|a1, a2| {
      a1.get_start().cmp(&a2.get_start())
    });

    self.dfs(&log)
  }

  fn dfs(&mut self, log: &Vec<Action<Self::P>>) -> Option<Vec<Action<Self::P>>> {
    let mut alists = Vec::new();
    let mut actions = self.gen(log);
    let mut i = 0;
    //let mut f = File::create("path.txt").unwrap();

    loop {
      if self.pred(log) {
        return Some(self.get_history());
      } else if i < actions.len() {
        let a = actions[i];

        if !self.contains(&a) {
          //println!("PUSH {:?}\n", a.get_id());
          //f.write_all(format!("PUSH {:?}\n", a.get_id()).as_bytes()).unwrap();
          self.push(a);
          alists.push((actions, i + 1));
          actions = self.gen(log);
          i = 0;
        } else {
          i += 1;
        }
      } else if self.count() == 0 {
        break;
      } else {
        //println!("POP");
        //f.write_all(format!("POP\n").as_bytes()).unwrap();
        self.pop();

        let pair = alists.pop().unwrap();
        actions = pair.0;
        i = pair.1;
      }
    }

    None
  }

  fn pred(&self, log: &Vec<Action<Self::P>>) -> bool {
    self.count() == log.len()
  }

  fn gen(&self, log: &Vec<Action<Self::P>>) -> Vec<Action<Self::P>> {
    let mut actions = Vec::new();

    let i_first = log.iter().position(|a| {
        self.count() == 0 ||
          (a.get_stop() >= self.peek().get_start() &&
           !self.contains(&a))
      });

    if let Some(i) = i_first {
      let mut first_stop_time = log[i].get_stop();

      let mut j = i;
      while j < log.len() {
        let a = log[j];

        if a.get_start() <= first_stop_time {
          if !self.contains(&a) {
            if a.get_stop() < first_stop_time {
              first_stop_time = a.get_stop();
            }
            if self.is_consistent_with(&a) {
              actions.push(a);
            }
          }
        } else {
          break;
        }

        j += 1;
      }
    }

    actions
  }
}


///////////////////////////////////////////////////////////////////////////////
//// Action
///////////////////////////////////////////////////////////////////////////////

pub type ActionID = (usize, usize);

#[derive(Debug)]
#[derive(Copy)]
#[derive(Clone)]
pub struct Action<P>
where P: Op {
  id: ActionID,
  op: P,
  start: SystemTime,
  stop: SystemTime,
}

impl<P> Action<P>
where P: Op {
  pub fn new(id: ActionID, op: P, start: SystemTime, stop: SystemTime) -> Self {
    Self {
      id: id,
      op: op,
      start: start,
      stop: stop,
    }
  }

  pub fn get_id(&self) -> ActionID {
    self.id
  }

  pub fn get_start(&self) -> SystemTime {
    self.start
  }

  pub fn get_stop(&self) -> SystemTime {
    self.stop
  }
}

impl<P> PartialEq for Action<P>
where P: Op {
  fn eq(&self, other: &Self) -> bool {
    self.get_id() == other.get_id()
  }
}


///////////////////////////////////////////////////////////////////////////////
//// Stack Linearization
///////////////////////////////////////////////////////////////////////////////

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
    match a.op {
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
        match a.op {
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
    match a.op {
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


///////////////////////////////////////////////////////////////////////////////
//// Queue Linearization
///////////////////////////////////////////////////////////////////////////////

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
    match a.op {
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
      match a.op {
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
    match a.op {
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


///////////////////////////////////////////////////////////////////////////////
//// Dictionary Linearization
///////////////////////////////////////////////////////////////////////////////

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
    match a.op {
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
      match a.op {
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
    match a.op {
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
