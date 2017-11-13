///////////////////////////////////////////////////////////////////////////////
//// 
//// Module: dict
////
///////////////////////////////////////////////////////////////////////////////

use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::{Mutex, Arc};
use std::sync::atomic::{Ordering, AtomicPtr};
use std::mem;
use rand::{self, Rng, ThreadRng};
use crossbeam::epoch::{self, MarkableAtomic, Owned};


///////////////////////////////////////////////////////////////////////////////
//// Trait Definitions
///////////////////////////////////////////////////////////////////////////////

pub trait Dict<K,V> {
  fn new() -> Self;
  fn get(&self, k: &K) -> Option<V>;
  fn put(&mut self, k: K, v: V) -> Option<V>;
  fn remove(&mut self, k: &K) -> Option<V>;
  fn is_empty(&self) -> bool;
  fn size(&self) -> usize;
}

pub trait ConcurrentDict<K,V>: Dict<K,V> + Clone + Send + Sync {}


///////////////////////////////////////////////////////////////////////////////
//// HtDict
///////////////////////////////////////////////////////////////////////////////

pub struct HtDict<K,V> {
  ht: HashMap<K,V>,
}

impl<K,V> Dict<K,V> for HtDict<K,V>
where K: Eq + Hash, V: Clone {
  fn new() -> Self {
    Self {
      ht: HashMap::new()
    }
  }

  fn get(&self, k: &K) -> Option<V> {
    self.ht.get(k).map(|v| {
      v.clone()
    })
  }

  fn put(&mut self, k: K, v: V) -> Option<V> {
    self.ht.insert(k, v)
  }

  fn remove(&mut self, k: &K) -> Option<V> {
    self.ht.remove(k)
  }

  fn is_empty(&self) -> bool {
    self.ht.is_empty()
  }

  fn size(&self) -> usize {
    self.ht.keys().count()
  }
}


///////////////////////////////////////////////////////////////////////////////
//// Skiplist
///////////////////////////////////////////////////////////////////////////////

type Link<K,V> = Option<Rc<RefCell<Node<K,V>>>>;

struct Node<K,V> {
  key: K,
  value: V,
  next: Vec<Link<K,V>>,
}

pub struct Skiplist<K,V> {
  head: Rc<RefCell<Node<K,V>>>,
  count: usize,
  rng: ThreadRng,
}

impl<K,V> Skiplist<K,V>
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
    let mut n = 0;
    let mut max = 1.0;

    while self.rng.next_f64() <= max {
      n += 1;
      max /= 2.0;
    }

    n
  }
}

impl<K,V> Dict<K,V> for Skiplist<K,V>
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


///////////////////////////////////////////////////////////////////////////////
//// CoarseLockHtDict
///////////////////////////////////////////////////////////////////////////////

pub struct CoarseLockHtDict<K,V> {
  arc: Arc<Mutex<HtDict<K,V>>>,
}

impl<K,V> Dict<K,V> for CoarseLockHtDict<K,V>
where K: Eq + Hash, V: Clone {
  fn new() -> Self {
    Self {
      arc: Arc::new(Mutex::new(HtDict::new())),
    }
  }

  fn get(&self, k: &K) -> Option<V> {
    self.arc.lock().unwrap().get(k)
  }

  fn put(&mut self, k: K, v: V) -> Option<V> {
    self.arc.lock().unwrap().put(k, v)
  }

  fn remove(&mut self, k: &K) -> Option<V> {
    self.arc.lock().unwrap().remove(k)
  }

  fn is_empty(&self) -> bool {
    self.arc.lock().unwrap().is_empty()
  }

  fn size(&self) -> usize {
    self.arc.lock().unwrap().size()
  }
}

impl<K,V> Clone for CoarseLockHtDict<K,V>
where K: Eq + Hash, V: Clone {
  fn clone(&self) -> Self {
    Self {
      arc: self.arc.clone(),
    }
  }
}

impl<K,V> ConcurrentDict<K,V> for CoarseLockHtDict<K,V>
where K: Eq + Hash + Send + Sync, V: Clone + Send + Sync {}


///////////////////////////////////////////////////////////////////////////////
//// LockfreeSkiplist
///////////////////////////////////////////////////////////////////////////////

// TODOS:
// 1. Advancing past marked node in get()
// 2. Physical deletion in find()
// 3. Safe update of value in put()

const MAX_LEVELS: usize = 6;

fn get_toplevel() -> usize {
  let mut n = 0;
  let mut max = 1.0;

  while rand::thread_rng().next_f64() <= max && n < MAX_LEVELS {
    n += 1;
    max /= 2.0;
  }

  n
}

fn null_vec<K,V>() -> Vec<MarkablePtr<K,V>> {
  let mut v = Vec::new();
  for _ in 0..MAX_LEVELS {
    v.push(MarkableAtomic::null());
  }
  v
}

type MarkablePtr<K,V> = MarkableAtomic<LockfreeNode<K,V>>;

struct LockfreeNode<K,V> {
  key: K,
  value: AtomicPtr<V>,
  is_tail: bool,
  next: Vec<MarkablePtr<K,V>>,
}

impl<K,V> LockfreeNode<K,V>
where K: Eq + Ord, V: Clone {
  fn new_sentinel(is_tail: bool) -> Self {
    let next = null_vec();

    unsafe {
      LockfreeNode {
        key: mem::uninitialized(),
        value: mem::uninitialized(),
        is_tail: is_tail,
        next: next,
      }
    }
  }

  pub fn new_head() -> Self {
    Self::new_sentinel(false)
  }

  pub fn new_tail() -> Self {
    Self::new_sentinel(true)
  }

  pub fn new(k: K, v: V, levels: usize) -> Self {
    let mut next = Vec::new();
    for _ in 0..levels {
      next.push(MarkableAtomic::null());
    }

    LockfreeNode {
      key: k,
      value: AtomicPtr::new(Box::into_raw(Box::new(v))),
      is_tail: false,
      next: next,
    }
  }

  pub fn toplevel(&self) -> usize {
    self.next.len()
  }
}

pub struct LockfreeSkiplist<K,V> {
  head: Arc<MarkablePtr<K,V>>,
  tail: Arc<MarkablePtr<K,V>>,
}

impl<K,V> LockfreeSkiplist<K,V>
where K: Eq + Ord, V: Clone {
  fn find(&mut self, k: &K) 
          -> (MarkablePtr<K,V>, Vec<MarkablePtr<K,V>>, Vec<MarkablePtr<K,V>>) 
  {
    let guard = epoch::pin();
    let mut preds = null_vec();
    let mut succs = null_vec();

    // return here every time a CAS fails
    'retry: loop {
      let mut pred = self.head
                       .load_shared(Ordering::SeqCst, &guard)
                       .unwrap();
      let mut i = ((*pred).next.len() - 1) as i32;
      let mut curr = (*pred).next[i as usize]
                       .load_shared(Ordering::SeqCst, &guard)
                       .unwrap();
      let mut succ;
      let mut mark;
      let mut pair;

      // proceed down through each level
      while i >= 0 {
        curr = (*pred).next[i as usize]
                 .load_shared(Ordering::SeqCst, &guard)
                 .unwrap();
        

        // advance curr until curr is not less than key
        loop {
          pair = (*curr).next[i as usize]
                   .load(Ordering::SeqCst, &guard);
          succ = pair.0;
          mark = pair.1;

          // physical deletion of marked nodes 
          while mark {
            let ok = (*pred).next[i as usize]
                       .cas_shared(Some(curr), succ,
                                   false, false,
                                   Ordering::SeqCst);
            if !ok {
              continue 'retry;
            }

            // when is it safe to release memory?

            curr = (*pred).next[i as usize]
                     .load_shared(Ordering::SeqCst, &guard)
                     .unwrap();
            pair = (*curr).next[i as usize]
                     .load(Ordering::SeqCst, &guard);
            succ = pair.0;
            mark = pair.1;
          }

          if !(*curr).is_tail && (*curr).key < *k {
            pred = curr;
            curr = succ.unwrap();
          } else {
            break;
          }
        }

        // curr is not less than key, record pred and succ nodes
        let pred_ptr = MarkableAtomic::null();
        pred_ptr.store_shared(Some(pred), false, Ordering::SeqCst);
        let succ_ptr = MarkableAtomic::null();
        succ_ptr.store_shared(Some(curr), false, Ordering::SeqCst);
        preds[i as usize] = pred_ptr;
        succs[i as usize] = succ_ptr;

        // to next level
        i -= 1;
      }

      // bottom level reached
      let p = MarkableAtomic::null();
      if !(*curr).is_tail && (*curr).key == *k {
        p.store_shared(Some(curr), false, Ordering::SeqCst);
      }
      return (p, preds, succs); 
    }
  }
}

impl<K,V> Dict<K,V> for LockfreeSkiplist<K,V>
where K: Eq + Ord, V: Clone {
  fn new() -> Self {
    let guard = epoch::pin();

    let head = LockfreeNode::new_head();
    let tail_atomic = MarkableAtomic::new(LockfreeNode::new_tail(), false);

    let tail_shared = tail_atomic.load_shared(Ordering::Relaxed, &guard);
    for i in 0..MAX_LEVELS {
      head.next[i].store_shared(tail_shared, false, Ordering::Relaxed);
    }

    Self {
      head: Arc::new(MarkableAtomic::new(head, false)),
      tail: Arc::new(tail_atomic),
    }
  }

  fn get(&self, k: &K) -> Option<V> {
    let guard = epoch::pin();

    let mut pred = self.head.load_shared(Ordering::SeqCst, &guard)
                            .unwrap();
    let mut i = ((*pred).next.len() - 1) as i32;
    let mut curr = (*pred).next[i as usize]
                     .load_shared(Ordering::SeqCst, &guard)
                     .unwrap();
    let mut succ;
    let mut mark;

    // proceed down through all levels, starting at top
    while i >= 0 {
      curr = (*pred).next[i as usize]
               .load_shared(Ordering::SeqCst, &guard)
               .unwrap();

      // advance until curr is not less than key
      loop {
        let pair = (*curr).next[i as usize]
                     .load(Ordering::SeqCst, &guard);
        succ = pair.0;
        mark = pair.1;

        // skip marked nodes
        while mark {
          curr = succ.unwrap();
          let pair = (*curr).next[i as usize]
                       .load(Ordering::SeqCst, &guard);
          succ = pair.0;
          mark = pair.1;
        }

        if !(*curr).is_tail && (*curr).key < *k {
          pred = curr;
          curr = succ.unwrap();
        } else {
          break;
        }
      }

      i -= 1;
    }

    if !(*curr).is_tail && (*curr).key == *k {
      let p = (*curr).value.load(Ordering::SeqCst);
      unsafe { Some((*p).clone()) }
    } else {
      None
    }
  }

  fn put(&mut self, k: K, v: V) -> Option<V> {
    let guard = epoch::pin();
    let new_top = get_toplevel();
    let mut node = Owned::new(LockfreeNode::new(k, v.clone(), new_top));

    // return here for retry
    loop {
      let (p, mut preds, mut succs) = self.find(&(*node).key);

      // check if node exists
      let curr = p.load_shared(Ordering::SeqCst, &guard);
      if curr.is_some() {
        let curr = curr.unwrap();
        let p = (*curr).value.load(Ordering::SeqCst);
        let newp = Box::into_raw(Box::new(v.clone()));
        if (*curr).value.compare_and_swap(p, newp, Ordering::SeqCst) != p {
          continue; // retry
        }
        unsafe { return Some((*p).clone()) };
      }

      // set next pointers in new node
      for i in 0..new_top {
        let succ = succs[i].load_shared(Ordering::SeqCst, &guard);
        node.next[i].store_shared(succ, false, Ordering::SeqCst);
      }

      // attempt CAS at bottom level
      let pred = preds[0].load_shared(Ordering::SeqCst, &guard)
                         .unwrap();
      let succ = succs[0].load_shared(Ordering::SeqCst, &guard);
      match (*pred).next[0].cas_and_ref(succ, node,
                                        false, false,
                                        Ordering::SeqCst, &guard) {
        Ok(node) => {
          // node is now in list, do CAS on ith level
          for i in 1..new_top {
            loop {
              let pred = preds[i].load_shared(Ordering::SeqCst, &guard)
                                 .unwrap();
              let succ = succs[i].load_shared(Ordering::SeqCst, &guard);
              if (*pred).next[i].cas_shared(succ, Some(node),
                                            false, false,
                                            Ordering::SeqCst) {
                break; // success on ith level
              }

              // retry find
              let triple = self.find(&(*node).key);
              preds = triple.1;
              succs = triple.2;
            }
          }

          // all levels updated
          return None;
        }
        Err(owned) => {
          node = owned;
          continue; // retry
        }
      }

    }
  }

  fn remove(&mut self, k: &K) -> Option<V> {
    let guard = epoch::pin();

    loop {
      let (p, _, succs) = self.find(k);

      // check if node exists
      let curr = p.load_shared(Ordering::SeqCst, &guard);
      if curr.is_none() {
        return None;
      }
      let curr = curr.unwrap();

      let victim = succs[0].load_shared(Ordering::SeqCst, &guard)
                           .unwrap();
      let mut succ;
      let mut mark;

      // mark each level, starting from top
      for i in (1..victim.toplevel()).rev() {
        let pair = (*victim).next[i].load(Ordering::SeqCst, &guard);
        succ = pair.0;
        mark = pair.1;

        while !mark {
          (*victim).next[i].mark(succ, false, true, Ordering::SeqCst);
          let pair = (*victim).next[i].load(Ordering::SeqCst, &guard);
          succ = pair.0;
          mark = pair.1;
        }
      }

      // mark bottom level
      succ = (*victim).next[0].load_shared(Ordering::SeqCst, &guard);
      loop {
        let ok = (*victim).next[0].mark(succ, false, true, Ordering::SeqCst);
        let pair = (*victim).next[0].load(Ordering::SeqCst, &guard);
        succ = pair.0;
        mark = pair.1;

        if ok {
          // mark succeeded, do physical deletion
          self.find(&k);
          let p = (*curr).value.load(Ordering::SeqCst);
          unsafe { return Some((*p).clone()); }
        } else if mark {
          // someone beat us to it
          return None; 
        }
      }
    }
  }

  fn is_empty(&self) -> bool {
    let guard = epoch::pin();

    let head = self.head.load_shared(Ordering::SeqCst, &guard)
                        .unwrap();
    let first = (*head).next[0].load_shared(Ordering::SeqCst, &guard)
                               .unwrap();
    
    (*first).is_tail
  }

  fn size(&self) -> usize {
    let guard = epoch::pin();

    let head = self.head.load_shared(Ordering::SeqCst, &guard)
                        .unwrap();
    let mut curr = (*head).next[0].load_shared(Ordering::SeqCst, &guard)
                                  .unwrap();
    let mut count = 0;

    while !(*curr).is_tail {
      count += 1;
      curr = (*curr).next[0].load_shared(Ordering::SeqCst, &guard)
                            .unwrap();
    }

    count
  }
}

impl<K,V> Clone for LockfreeSkiplist<K,V>
where K: Eq + Ord, V: Clone {
  fn clone(&self) -> Self {
    Self {
      head: self.head.clone(),
      tail: self.tail.clone(),
    }
  }
}

impl<K,V> ConcurrentDict<K,V> for LockfreeSkiplist<K,V>
where K: Eq + Ord + Send + Sync, V: Clone + Send + Sync {}
