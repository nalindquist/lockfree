//! Linearization of concurrent histories
//!
//! This module provides facilities to construct linearizations of a
//! concurrent log, used for testing the correctness of a concurrent
//! data structure. 
//!
//! The primary trait in the module is the `Linearization` trait,
//! which must be implemented for every abstract data type. A
//! `Linearization` takes a concurrent log, represented as a sequence
//! of `Action` objects, and performs a depth-first search to find
//! a valid linearization. The depth-first search algorithm is based
//! on a [thesis](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-579.pdf)
//! by Karl Fraser.

mod action;
mod stack;
mod queue;
mod dict;
mod pqueue;

pub use self::action::Action;
pub use self::stack::{StackOp, StackLinearization};
pub use self::queue::{QueueOp, QueueLinearization};
pub use self::dict::{DictOp, DictLinearization};
pub use self::pqueue::{PQueueOp, PQueueLinearization};

use std::fmt::Debug;

/// Represents an operation performed by an abstract data type.
pub trait Op : Copy + Clone + Debug {}

/// A linearization for a sequence of `Action` objects.
pub trait Linearization
where Self::P: Op {
  type P;

  /// Creates a new, empty linearization.
  fn new() -> Self;

  /// Pushes the given action onto the search path.
  fn push(&mut self, a: Action<Self::P>);

  /// Pops the latest action from the search path.
  fn pop(&mut self);

  /// Returns the latest action on the search path.
  fn peek(&self) -> &Action<Self::P>;

  /// Tests if the search path contains the given action.
  fn contains(&self, a: &Action<Self::P>) -> bool;

  /// Returns the number of actions in the search path.
  fn count(&self) -> usize;

  /// Determines if the current linearization is consistent with the given
  /// action (i.e. if the action can be pushed onto the search path).
  fn is_consistent_with(&self, a: &Action<Self::P>) -> bool;

  /// Returns the linearized history produced by this linearization.
  fn get_history(&self) -> Vec<Action<Self::P>>;

  /// Linearizes the given concurrent log, if possible.
  fn linearize(&mut self, mut log: Vec<Action<Self::P>>) -> Option<Vec<Action<Self::P>>> {
    log.sort_by(|a1, a2| {
      a1.get_start().cmp(&a2.get_start())
    });

    self.dfs(&log)
  }

  /// Performs a depth-first search for a valid linearization on the given
  /// log.
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

  /// Returns true if the search has been completed successfully.
  fn pred(&self, log: &Vec<Action<Self::P>>) -> bool {
    self.count() == log.len()
  }

  /// Generates a list of all actions consistent with the current
  /// search path.
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


#[cfg(test)]
mod linearization_tests {
  use std::thread;
  use std::time::{Instant, Duration};
  use super::*;  

  #[test]
  fn empty_linearization_test() {
    let log = Vec::new();

    let mut slin : StackLinearization<i32> = StackLinearization::new();
    let history = slin.linearize(log).expect(
      "No valid linearization found.");

    assert_eq!(history.len(), 0);
  }

  #[test]
  fn no_overlap_linearization_test() {
    let d = Duration::from_millis(10);
    let n = 10;
    let mut actions = Vec::new();

    for i in 0..n {
      let t1 = Instant::now();
      thread::sleep(d);
      let t2 = Instant::now();
      thread::sleep(d);

      actions.push(Action::new(
        (0, i),
        StackOp::Push(1),
        t1,
        t2));
    }

    let mut log1 = Vec::new();
    let mut log2 = Vec::new();
    for i in 0..n {
      log1.push(actions[i]);
      log2.push(actions[n-i-1]);
    }

    let mut slin1 = StackLinearization::new();
    let history1 = slin1.linearize(log1).expect(
      "No valid linearization found.");

    assert_eq!(history1.len(), n);
    for i in 0..n {
      assert_eq!(history1[i].get_id(), (0, i));
    }

    let mut slin2 = StackLinearization::new();
    let history2 = slin2.linearize(log2).expect(
      "No valid linearization found.");

    assert_eq!(history2.len(), n);
    for i in 0..n {
      assert_eq!(history2[i].get_id(), (0, i));
    }
  }

  #[test]
  fn overlap_linearization_test() {
    let d = Duration::from_millis(10);
    let mut log = Vec::new();

    let t1 = Instant::now();
    thread::sleep(d);
    let t2 = Instant::now();
    thread::sleep(d);
    let t3 = Instant::now();
    thread::sleep(d);
    let t4 = Instant::now();
    thread::sleep(d);

    log.push(Action::new(
      (0, 0),
      StackOp::Pop(Some(1)),
      t1,
      t3));
    log.push(Action::new(
      (1, 0),
      StackOp::Push(1),
      t2,
      t4));

    let mut slin = StackLinearization::new();
    let history = slin.linearize(log).expect(
      "No valid linearization found.");

    assert_eq!(history[0].get_id(), (1, 0));
    assert_eq!(history[1].get_id(), (0, 0));
  }

  #[test]
  fn identical_time_linearization_test() {
    let d = Duration::from_millis(10);
    let n = 10;
    let mut actions = Vec::new();

    let t1 = Instant::now();
    thread::sleep(d);
    let t2 = Instant::now();

    for i in 0..n {
      let op: StackOp<usize>;

      if i % 2 == 0 {
        op = StackOp::Push(i);
      } else {
        op = StackOp::Pop(Some(i-1));
      }

      actions.push(Action::new(
        (i, 0),
        op,
        t1,
        t2));
    }

    let mut log = Vec::new();
    for i in 0..n {
      log.push(actions[(n-i-1)]);
    }

    let mut slin = StackLinearization::new();
    let history = slin.linearize(log).expect(
      "No valid linearization found.");

    assert_eq!(history.len(), n);
    for i in 0..n {
      if i % 2 == 0 {
        let i_push = history.iter().position(|a| {
          a.get_id() == (i, 0)
        }).unwrap();
        let i_pop = history.iter().position(|a| {
          a.get_id() == (i+1, 0)
        }).unwrap();
        assert!(i_push < i_pop);
      }
    }
  }

  #[test]
  fn invalid_no_overlap_linearization_test() {
    let d = Duration::from_millis(10);
    let mut log = Vec::new();

    let t1 = Instant::now();
    thread::sleep(d);
    let t2 = Instant::now();
    thread::sleep(d);
    let t3 = Instant::now();
    thread::sleep(d);
    let t4 = Instant::now();
    thread::sleep(d);

    log.push(Action::new(
      (0, 0),
      StackOp::Pop(Some(1)),
      t1,
      t2));
    log.push(Action::new(
      (1, 0),
      StackOp::Push(1),
      t3,
      t4));

    let mut slin = StackLinearization::new();
    assert_eq!(slin.linearize(log), None);
  }

  #[test]
  fn invalid_overlap_linearization_test() {
    let d = Duration::from_millis(10);
    let mut log = Vec::new();

    let t1 = Instant::now();
    thread::sleep(d);
    let t2 = Instant::now();
    thread::sleep(d);
    let t3 = Instant::now();
    thread::sleep(d);
    let t4 = Instant::now();
    thread::sleep(d);

    log.push(Action::new(
      (0, 0),
      StackOp::Pop(Some(1)),
      t1,
      t3));
    log.push(Action::new(
      (1, 0),
      StackOp::Push(2),
      t2,
      t4));

    let mut slin = StackLinearization::new();
    assert_eq!(slin.linearize(log), None);
  }
}
