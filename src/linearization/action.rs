use std::time::Instant;
use super::*;

/// Describes the ID of an `Action` as a (thread ID, operation no.) pair.
pub type ActionID = (usize, usize);

/// Represents an abstract data type performing some `Op` at some time.
#[derive(Debug)]
#[derive(Copy)]
#[derive(Clone)]
pub struct Action<P>
where P: Op {
  id: ActionID,
  op: P,
  start: Instant,
  stop: Instant,
}

impl<P> Action<P>
where P: Op {
  pub fn new(id: ActionID, op: P, start: Instant, stop: Instant) -> Self {
    Self {
      id: id,
      op: op,
      start: start,
      stop: stop,
    }
  }

  pub fn get_op(&self) -> P {
    self.op
  }

  pub fn get_id(&self) -> ActionID {
    self.id
  }

  pub fn get_start(&self) -> Instant {
    self.start
  }

  pub fn get_stop(&self) -> Instant {
    self.stop
  }
}

impl<P> PartialEq for Action<P>
where P: Op {
  fn eq(&self, other: &Self) -> bool {
    self.get_id() == other.get_id()
  }
}
