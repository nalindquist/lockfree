use std::time::SystemTime;
use std::fs::File;
use std::io::Write;
use std::fmt::Debug;
use std::collections::VecDeque;


///////////////////////////////////////////////////////////////////////////////
//// Trait Definitions
///////////////////////////////////////////////////////////////////////////////

pub trait Action: PartialEq + Copy + Clone + Debug {
  fn get_id(&self) -> (usize, usize);
  fn get_start_time(&self) -> SystemTime;
  fn get_stop_time(&self) -> SystemTime;
}

pub trait Linearization
where Self::A: Action {
  type A;

  fn new() -> Self;
  fn push(&mut self, a: Self::A);
  fn pop(&mut self);
  fn peek(&self) -> &Self::A;
  fn contains(&self, a: &Self::A) -> bool;
  fn count(&self) -> usize;
  fn is_consistent_with(&self, a: &Self::A) -> bool;
  fn get_history(&self) -> Vec<Self::A>;

  fn linearize(&mut self, mut log: Vec<Self::A>) -> Option<Vec<Self::A>> {
    log.sort_by(|a1, a2| {
      a1.get_start_time().cmp(&a2.get_start_time())
    });

    self.dfs(&log)
  }

  fn dfs(&mut self, log: &Vec<Self::A>) -> Option<Vec<Self::A>> {
    let mut alists = Vec::new();
    let mut actions = self.gen(log);
    let mut i = 0;

    loop {
      if self.pred(log) {
        return Some(self.get_history());
      } else if i < actions.len() {
        let a = actions[i];

        if !self.contains(&a) {
          // println!("ID: {:?}", a.get_id());
          // println!("Count: {}", self.count());

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
        //println!("Pop");

        self.pop();

        let pair = alists.pop().unwrap();
        actions = pair.0;
        i = pair.1;

        // if i < actions.len() {
        //   println!("Prev ID: {:?}", self.peek().get_id());
        //   for a in actions.iter() {
        //     println!("Post ID:     {:?}", a.get_id());
        //   }
        // }
      }
    }

    None
  }

  fn pred(&self, log: &Vec<Self::A>) -> bool {
    self.count() == log.len()
  }

  fn gen(&self, log: &Vec<Self::A>) -> Vec<Self::A> {
    let mut actions = Vec::new();

    let i_first = log.iter().position(|a| {
        self.count() == 0 ||
          (a.get_stop_time() >= self.peek().get_start_time() &&
           !self.contains(&a))
      });

    if let Some(i) = i_first {
      let mut first_stop_time = log[i].get_stop_time();

      let mut j = i;
      while j < log.len() {
        let a = log[j];

        if a.get_start_time() <= first_stop_time {
          if !self.contains(&a) {
            if a.get_stop_time() < first_stop_time {
              first_stop_time = a.get_stop_time();
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
//// Utilities
///////////////////////////////////////////////////////////////////////////////

pub fn write_log<A: Action>(mut log: Vec<A>, name: &str) {
  log.sort_by(|a1, a2| {
    a1.get_start_time().cmp(&a2.get_start_time())
  });

  let mut f = File::create(name).unwrap();
  for a in log.iter() {
    f.write_all(format!("{:?}\n", a).as_bytes()).unwrap();
  }
}

pub fn write_history<A: Action>(history: &Vec<A>, name: &str) {
  let mut f = File::create(name).unwrap();

  for a in history.iter() {
    f.write_all(format!("{:?}\n", a).as_bytes()).unwrap();
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

#[derive(Debug)]
#[derive(Copy)]
#[derive(Clone)]
pub struct StackAction<T>
where T: Copy + Clone + Debug {
  id: (usize, usize),
  op: StackOp<T>,
  start_time: SystemTime,
  stop_time: SystemTime,
}

impl<T> StackAction<T>
where T: Copy + Clone + Debug {
  pub fn new(
    id: (usize, usize), 
    op: StackOp<T>, 
    start_time: SystemTime, 
    stop_time: SystemTime) -> Self {
    Self {
      id: id,
      op: op,
      start_time: start_time,
      stop_time: stop_time,
    }
  }
}

impl<T> PartialEq for StackAction<T>
where T: Copy + Clone + Debug {
  fn eq(&self, other: &Self) -> bool {
    self.get_id() == other.get_id()
  }
}

impl<T> Action for StackAction<T>
where T: Copy + Clone + Debug {
  fn get_id(&self) -> (usize, usize) {
    self.id
  }

  fn get_start_time(&self) -> SystemTime {
    self.start_time
  }

  fn get_stop_time(&self) -> SystemTime {
    self.stop_time
  }
}

#[derive(Clone)]
pub struct StackLinearization<T> 
where T: Copy + Clone + Debug {
  current: Vec<T>,
  old: Vec<T>,
  path: Vec<StackAction<T>>,
}

impl<T> Linearization for StackLinearization<T>
where T: Copy + Clone + Eq + Debug {
  type A = StackAction<T>;

  fn new() -> Self {
    Self {
      current: Vec::new(),
      old: Vec::new(),
      path: Vec::new(),
    }
  }

  fn push(&mut self, a: Self::A) {
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

  fn peek(&self) -> &Self::A {
    &self.path[self.path.len() - 1]
  }

  fn contains(&self, a: &Self::A) -> bool {
    self.path.contains(a)
  }

  fn count(&self) -> usize {
    self.path.len()
  }

  fn is_consistent_with(&self, a: &Self::A) -> bool {
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

  fn get_history(&self) -> Vec<Self::A> {
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

#[derive(Debug)]
#[derive(Copy)]
#[derive(Clone)]
pub struct QueueAction<T>
where T: Copy + Clone + Debug {
  id: (usize, usize),
  op: QueueOp<T>,
  start_time: SystemTime,
  stop_time: SystemTime,
}

impl<T> QueueAction<T>
where T: Copy + Clone + Debug {
  pub fn new(
    id: (usize, usize), 
    op: QueueOp<T>, 
    start_time: SystemTime, 
    stop_time: SystemTime) -> Self {
    Self {
      id: id,
      op: op,
      start_time: start_time,
      stop_time: stop_time,
    }
  }
}

impl<T> PartialEq for QueueAction<T>
where T: Copy + Clone + Debug {
  fn eq(&self, other: &Self) -> bool {
    self.get_id() == other.get_id()
  }
}

impl<T> Action for QueueAction<T>
where T: Copy + Clone + Debug {
  fn get_id(&self) -> (usize, usize) {
    self.id
  }

  fn get_start_time(&self) -> SystemTime {
    self.start_time
  }

  fn get_stop_time(&self) -> SystemTime {
    self.stop_time
  }
}

#[derive(Clone)]
pub struct QueueLinearization<T> 
where T: Copy + Clone + Debug {
  state: VecDeque<T>,
  path: Vec<QueueAction<T>>,
}

impl<T> Linearization for QueueLinearization<T>
where T: Copy + Clone + Eq + Debug {
  type A = QueueAction<T>;

  fn new() -> Self {
    Self {
      state: VecDeque::new(),
      path: Vec::new(),
    }
  }

  fn push(&mut self, a: Self::A) {
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

  fn peek(&self) -> &Self::A {
    &self.path[self.path.len() - 1]
  }

  fn contains(&self, a: &Self::A) -> bool {
    self.path.contains(a)
  }

  fn count(&self) -> usize {
    self.path.len()
  }

  fn is_consistent_with(&self, a: &Self::A) -> bool {
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

  fn get_history(&self) -> Vec<Self::A> {
    self.path.clone()
  }
}