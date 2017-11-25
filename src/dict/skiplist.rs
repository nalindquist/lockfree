use std::rc::Rc;
use std::cell::RefCell;
use std::mem;
use rand::{self, Rng, ThreadRng};
use super::*;

type Link<K,V> = Option<Rc<RefCell<Node<K,V>>>>;

struct Node<K,V> {
  key: K,
  value: V,
  next: Vec<Link<K,V>>,
}

/// A `Dict<K,V>` implemented using a skiplist.
pub struct SkiplistDict<K,V> {
  head: Rc<RefCell<Node<K,V>>>,
  count: usize,
  rng: ThreadRng,
}

impl<K,V> SkiplistDict<K,V>
where K: Eq + Ord, V: Clone {
  fn find(&self, k: &K) -> (Vec<Link<K,V>>, Vec<Link<K,V>>, Link<K,V>) {
    let mut preds = Vec::new();
    let mut succs = Vec::new();
    let mut node = None;

    let n = self.head.borrow().next.len();
    let mut i = (n-1) as i32;
    let mut curr = Rc::clone(&self.head);
    while i >= 0 {
      let mut search = true;
      while search {
        let copy = Rc::clone(&curr);
        search = copy.borrow().next[i as usize].as_ref().map_or_else(
          || {
            false
          },
          |p| {
            if *k > p.borrow().key {
              curr = Rc::clone(p);
              true
            } else {
              false
            }
          });
      }

      let succ = curr.borrow().next[i as usize].as_ref().map_or_else(
        || {
          None
        },
        |p| {
          if *k == p.borrow().key {
            p.borrow().next[i as usize].as_ref().map_or_else(
              || {
                None
              },
              |p| {
                Some(Rc::clone(p))
              })
          } else {
            Some(Rc::clone(p))
          }
        });

      preds.push(Some(Rc::clone(&curr)));
      succs.push(succ);

      i -= 1;
    }

    curr.borrow().next[0].as_ref().map(|p| {
      if *k == p.borrow().key {
        node = Some(Rc::clone(p));
      }
    });

    (preds, succs, node)
  }

  fn gen_levels(&mut self) -> usize {
    let mut n = 1;
    let p = 0.5;

    while self.rng.next_f64() < p {
      n += 1;
    }

    n
  }
}

impl<K,V> Dict<K,V> for SkiplistDict<K,V>
where K: Eq + Ord, V: Clone {
  fn new() -> Self {
    let head: Node<K,V>;
    unsafe {
      head = Node {
        key: mem::uninitialized(),
        value: mem::uninitialized(),
        next: Vec::new(),
      }
    }

    let l = Self {
      head: Rc::new(RefCell::new(head)),
      count: 0,
      rng: rand::thread_rng(),
    };
    l.head.borrow_mut().next.push(None);
    l
  }

  fn get(&self, k: &K) -> Option<V> {
    let (_, _, node) = self.find(k);
    node.map(|p| {
      p.borrow().value.clone()
    })
  }

  fn put(&mut self, k: K, v: V) -> Option<V> {
    let (mut preds, mut succs, node) = self.find(&k);

    match node {
      None => {
        let new_node = Rc::new(RefCell::new(Node {
          key: k,
          value: v,
          next: Vec::new(),
        }));
        let new_levels = self.gen_levels();
        let n = self.head.borrow().next.len();

        for i in 0..new_levels {
          if i < n {
            let pred = preds.pop().unwrap().unwrap();
            let succ = succs.pop().unwrap();
            pred.borrow_mut().next[i] = Some(Rc::clone(&new_node));
            new_node.borrow_mut().next.push(succ.map(|p| {
              Rc::clone(&p)
            }));
          } else {
            self.head.borrow_mut().next.push(Some(Rc::clone(&new_node)));
            new_node.borrow_mut().next.push(None);
          }
        }

        self.count += 1;

        None
      }
      Some(p) => {
        let old = p.borrow_mut().value.clone();
        p.borrow_mut().value = v;
        Some(old)
      }
    }
  }

  fn remove(&mut self, k: &K) -> Option<V> {
    let (mut preds, mut succs, node) = self.find(&k);

    match node {
      None => {
        None
      }
      Some(p) => {
        for i in 0..preds.len() {
          let pred = preds.pop().unwrap().unwrap();
          let succ = succs.pop().unwrap();
          pred.borrow_mut().next[i] = succ;
        }

        self.count -= 1;

        Some(p.borrow().value.clone())
      }
    }
  }

  fn is_empty(&self) -> bool {
    self.count == 0
  }

  fn size(&self) -> usize {
    self.count
  }
}
