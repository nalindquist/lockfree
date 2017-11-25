//! Stack implementations
//!
//! This module provides two examples of sequential stacks: an array-based
//! `ArrayStack` and a linked-list-based `ListStack`. The `ListStack` is
//! is based on [this blog post](http://cglab.ca/~abeinges/blah/too-many-lists/book/).
//!
//! This module also provides two examples of concurrent stacks. The
//! `CoarseLockStack` just uses a single mutex around a `ListStack`, while
//! the `TreiberStack` is a lock-free stack. The `TreiberStack` is based
//! on a [blog post](https://aturon.github.io/blog/2015/08/27/epoch/) written
//! by Aaron Turon. 

mod array;
mod list;
mod coarse_lock_list;
mod treiber;

pub use self::array::ArrayStack;
pub use self::list::ListStack;
pub use self::coarse_lock_list::CoarseLockStack;
pub use self::treiber::TreiberStack;

/// The `Stack<T>` abstract data type.
pub trait Stack<T> {
  /// Creates a new, empty `Stack<T>`.
  fn new() -> Self;

  /// Pushes an element onto the stack.
  fn push(&mut self, elem: T);

  /// Pops an element from the stack, if there is one.
  fn pop(&mut self) -> Option<T>;

  /// Predicate that tests if the stack is empty.
  fn is_empty(&self) -> bool;

  /// Returns the number of elements in the stack.
  fn size(&self) -> usize;
}

/// The specification for a thread-safe `Stack`.
pub trait ConcurrentStack<T>: Stack<T> + Clone + Send + Sync {}


#[cfg(test)]
mod stack_tests {
  use std::time::Instant;
  use rand::ThreadRng;
  use ::linearization::*;
  use ::testing::*;
  use super::*;

  #[derive(Copy)]
  #[derive(Clone)]
  enum StackTestOp {
    Push,
    Pop,
  }

  impl TestOp for StackTestOp {}

  struct StackTester<S> {
    stack: S,
    ops: Vec<(StackTestOp, f64)>,
  }

  impl<S> StackTester<S>
  where S: Stack<i32> {
    pub fn new(stack: S, p_pop: f64) -> Self {
      Self {
        stack: stack,
        ops: vec![(StackTestOp::Push, 1.0 - p_pop),
                  (StackTestOp::Pop,  p_pop)],
      }
    }
  }

  impl<S> Tester for StackTester<S>
  where S: Stack<i32> {
    fn execute_op(&mut self, rng: &mut ThreadRng) {
      match choose_op(rng, &self.ops) {
        StackTestOp::Push => {
          self.stack.push(42);
        }
        StackTestOp::Pop => {
          self.stack.pop();
        }
      }
    }
  }

  #[derive(Clone)]
  struct ConcurrentStackTester<S>
  where S: ConcurrentStack<i32> {
    stack: S,
    ops: Vec<(StackTestOp, f64)>,
  }

  impl<S> ConcurrentStackTester<S>
  where S: ConcurrentStack<i32> {
    pub fn new(stack: S, p_pop: f64) -> Self {
      Self {
        stack: stack,
        ops: vec![(StackTestOp::Push, 1.0 - p_pop),
                  (StackTestOp::Pop,  p_pop)],
      }
    }
  }

  impl<S> ConcurrentTester for ConcurrentStackTester<S>
  where S: ConcurrentStack<i32> {
    type L = StackLinearization<i32>;

    fn execute_op(&mut self, rng: &mut ThreadRng) {
      match choose_op(rng, &self.ops) {
        StackTestOp::Push => {
          self.stack.push(42);
        }
        StackTestOp::Pop => {
          self.stack.pop();
        }
      }
    }

    fn record_op(&mut self, rng: &mut ThreadRng, tid: usize, i: usize) -> Action<<Self::L as Linearization>::P> {
      let start: Instant;
      let stop: Instant;
      let op: StackOp<i32>;

      match choose_op(rng, &self.ops) {
        StackTestOp::Push => {
          let args = gen_args(rng, 1);
          start = Instant::now();
          self.stack.push(args[0]);
          stop = Instant::now();
          op = StackOp::Push(args[0]);
        }
        StackTestOp::Pop => {
          start = Instant::now();
          let r = self.stack.pop();
          stop = Instant::now();
          op = StackOp::Pop(r);
        }
      }

      Action::new((tid, i), op, start, stop)
    }

    fn lin(&self) -> Self::L {
      StackLinearization::new()
    }
  }

  fn test_stack_correctness<S: Stack<i32>>(mut stack: S) {
    assert_eq!(stack.pop(), None);
    assert!(stack.is_empty());

    stack.push(4);

    assert_eq!(stack.size(), 1);
    assert!(!stack.is_empty());

    stack.push(1);

    assert_eq!(stack.size(), 2);
    assert!(!stack.is_empty());

    assert_eq!(stack.pop(), Some(1));

    assert_eq!(stack.size(), 1);
    assert!(!stack.is_empty());

    assert_eq!(stack.pop(), Some(4));

    assert_eq!(stack.size(), 0);
    assert!(stack.is_empty());

    assert_eq!(stack.pop(), None);

    stack.push(3);

    assert_eq!(stack.size(), 1);
    assert!(!stack.is_empty());
  }

  fn test_stack_speed<S: Stack<i32>>(stack: S, t_secs: f64, p_pop: f64) {
    let tester = StackTester::new(stack, p_pop);
    test_throughput(tester, t_secs);
  }

  fn test_stack_concurrent_correctness<S: ConcurrentStack<i32>>(
    stack: S, t_secs: f64, p_pop: f64, n_threads: usize) {
    let tester = ConcurrentStackTester::new(stack, p_pop);
    test_concurrent_correctness(tester, t_secs, n_threads);
  }

  fn test_stack_concurrent_speed<S: ConcurrentStack<i32>>(
    stack: S, t_secs: f64, p_pop: f64, n_threads: usize) {
    let tester = ConcurrentStackTester::new(stack, p_pop);
    test_concurrent_throughput(tester, t_secs, n_threads);
  }

  #[test]
  fn array_stack_correctness() {
    test_stack_correctness(ArrayStack::new());
  }

  #[test]
  fn array_stack_speed() {
    test_stack_speed(ArrayStack::new(), 1.0, 0.5);
  }

  #[test]
  fn list_stack_correctness() {
    test_stack_correctness(ListStack::new());
  }

  #[test]
  fn list_stack_speed() {
    test_stack_speed(ListStack::new(), 1.0, 0.5);
  }

  #[test]
  fn coarse_lock_stack_correctness() {
    test_stack_correctness(CoarseLockStack::new());
  } 

  #[test]
  fn coarse_lock_stack_correctness_concurrent() {
    for _ in 0..10 {
      test_stack_concurrent_correctness(
        CoarseLockStack::new(), 0.0001, 0.8, 10);
    }
  }

  #[test]
  fn coarse_lock_stack_speed() {
    test_stack_speed(CoarseLockStack::new(), 1.0, 0.5);
  }

  #[test]
  fn coarse_lock_stack_speed_concurrent() {
    test_stack_concurrent_speed(
      CoarseLockStack::new(), 1.0, 0.5, 10);
  }

  #[test]
  fn treiber_stack_correctness() {
    test_stack_correctness(TreiberStack::new());
  }

  #[test]
  fn treiber_stack_correctness_concurrent() {
    for _ in 0..10 {
      test_stack_concurrent_correctness(
        TreiberStack::new(), 0.0001, 0.8, 10);
    }
  }

  #[test]
  fn treiber_stack_speed() {
    test_stack_speed(TreiberStack::new(), 1.0, 0.5);
  }

  #[test]
  fn treiber_stack_speed_concurrent() {
    test_stack_concurrent_speed(
      TreiberStack::new(), 1.0, 0.5, 10);
  }
}
