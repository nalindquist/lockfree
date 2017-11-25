extern crate crossbeam;
extern crate rand;

pub mod stack;
pub mod queue;
pub mod dict;
pub mod pqueue;
pub mod linearization;

#[cfg(test)]
mod testing {
  use super::linearization::*;
  use std::time::{Duration, Instant};
  use std::fs::File;
  use std::io::Write;
  use rand::{self, Rng, ThreadRng};
  use crossbeam;

  pub trait TestOp: Copy {}

  pub trait Tester {
    fn execute_op(&mut self, rng: &mut ThreadRng);
  }

  pub trait ConcurrentTester: Clone + Send + Sync
  where Self::L: Linearization {
    type L;

    fn execute_op(&mut self, rng: &mut ThreadRng);
    fn record_op(&mut self, rng: &mut ThreadRng, tid: usize, i: usize) -> Action<<Self::L as Linearization>::P>;
    fn lin(&self) -> Self::L;
  }

  pub fn duration_to_ns(d: Duration) -> f64 {
    (d.as_secs() as f64) * 1_000_000_000.0 +
      (d.subsec_nanos() as f64)
  }

  pub fn secs_to_duration(t: f64) -> Duration {
    Duration::new(
      t as u64,
      ((t - ((t as u64) as f64)) * 1_000_000_000.0) as u32)
  }

  pub fn write_log<P: Op>(mut log: Vec<Action<P>>, name: &str) {
    log.sort_by(|a1, a2| {
      a1.get_start().cmp(&a2.get_start())
    });

    let mut f = File::create(name).unwrap();
    for a in log.iter() {
      f.write_all(format!("{:?}\n", a).as_bytes()).unwrap();
    }
  }

  pub fn write_history<P: Op>(history: &Vec<Action<P>>, name: &str) {
    let mut f = File::create(name).unwrap();

    for a in history.iter() {
      f.write_all(format!("{:?}\n", a).as_bytes()).unwrap();
    }
  }

  pub fn choose_op<P: TestOp>(rng: &mut ThreadRng, ops: &Vec<(P, f64)>) -> P {
    let f = rng.next_f64();
    let mut acc = 0.0;

    for pair in ops.iter() {
      acc += pair.1;
      if acc > f {
        return pair.0
      }
    }

    panic!("Unable to select operation.");
  }

  pub fn gen_args(rng: &mut ThreadRng, n: usize) -> Vec<i32> {
    let mut v = Vec::new();
    for _ in 0..n {
      v.push(rng.gen());
    }
    v
  }

  pub fn test_throughput<T: Tester>(mut tester: T, t_secs: f64) {
    let mut rng = rand::thread_rng();
    let mut n_ops = 0;
    let duration = secs_to_duration(t_secs);
    let start_time = Instant::now();

    let elapsed = loop {
      tester.execute_op(&mut rng);
      n_ops += 1;

      let d = start_time.elapsed();
      if d >= duration {
        break d
      }
    };

    let ns_elapsed = duration_to_ns(elapsed);
    let ns_per_op = ns_elapsed/(n_ops as f64);

    println!("");
    println!("Time elapsed (s): {}", ns_elapsed / 1_000_000_000.0);
    println!("Ops completed:    {}", n_ops);
    println!("Time per op (ns): {}", ns_per_op);
  }

  pub fn test_concurrent_correctness<T>(tester: T, t_secs: f64, n_threads: usize)
  where T: ConcurrentTester, <T::L as Linearization>::P: Send + Sync {
    let mut handles = Vec::new();
    let mut log = Vec::new();

    crossbeam::scope(|scope| {
      for tid in 0..n_threads {
        let mut tester = tester.clone();

        let h = scope.spawn(move || {
          let mut rng = rand::thread_rng();
          let mut log = Vec::new();
          let mut i = 0;
          let duration = secs_to_duration(t_secs);
          let start_time = Instant::now();

          loop {
            let a = tester.record_op(&mut rng, tid, i);
            log.push(a);
            i += 1;

            let d = start_time.elapsed();
            if d >= duration {
              break;
            }
          }

          log
        });

        handles.push(h);
      }
    });

    for h in handles {
      for entry in h.join() {
        log.push(entry);
      }
    }

    write_log(log.clone(), "log.txt");

    let history = tester.lin().linearize(log).expect(
      "No valid linearization found.");

    write_history(&history, "history.txt");
  }

  pub fn test_concurrent_throughput<T>(tester: T, t_secs: f64, n_threads: usize)
  where T: ConcurrentTester, <T::L as Linearization>::P: Send + Sync {
    let mut handles = Vec::new();

    crossbeam::scope(|scope| {
      for _ in 0..n_threads {
        let mut tester = tester.clone();

        let h = scope.spawn(move || {
          let mut rng = rand::thread_rng();
          let mut n_ops = 0;
          let duration = secs_to_duration(t_secs);
          let start_time = Instant::now();

          let elapsed = loop {
            tester.execute_op(&mut rng);
            n_ops += 1;

            let d = start_time.elapsed();
            if d >= duration {
              break d
            }
          };

          (elapsed, n_ops)
        });

        handles.push(h);
      }
    });

    let mut ns_elapsed = 0.0;
    let mut op_total = 0;
    for h in handles {
      let (elapsed, n_ops) = h.join();
      ns_elapsed += duration_to_ns(elapsed);
      op_total += n_ops;
    }
    let ns_per_op = ns_elapsed/(op_total as f64);

    println!("");
    println!("Time elapsed (s): {}", ns_elapsed / 1_000_000_000.0);
    println!("Ops completed:    {}", op_total);
    println!("Time per op (ns): {}", ns_per_op);
  }
}
