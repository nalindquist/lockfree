use std::sync::Arc;
use std::sync::atomic::{Ordering, AtomicPtr};
use std::mem;
use rand::{self, Rng};
use crossbeam::epoch::{self, MarkableAtomic, Shared, Owned, Guard};
use super::*;


//////////////////////////////////////////////////////////////////////////////
//// Utilities
//////////////////////////////////////////////////////////////////////////////

const MAX_LEVELS: usize = 6;

fn get_toplevel() -> usize {
  let mut n = 1;
  let p = 0.5;

  while rand::thread_rng().next_f64() < p && n < MAX_LEVELS {
    n += 1;
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


//////////////////////////////////////////////////////////////////////////////
//// Node Representation
//////////////////////////////////////////////////////////////////////////////

type MarkablePtr<K,V> = MarkableAtomic<Node<K,V>>;
type SharedPtr<'a,K,V> = Option<Shared<'a, Node<K,V>>>;

struct Node<K,V> {
  key: K,
  value: AtomicPtr<V>,
  is_tail: bool,
  next: Vec<MarkablePtr<K,V>>,
}

impl<K,V> Node<K,V>
where K: Eq + Ord, V: Clone {
  fn new_sentinel(is_tail: bool) -> Self {
    let next = null_vec();

    unsafe {
      Node {
        key: mem::uninitialized(),
        value: mem::uninitialized(),
        is_tail: is_tail,
        next: next,
      }
    }
  }

  fn new_head() -> Self {
    Self::new_sentinel(false)
  }

  fn new_tail() -> Self {
    Self::new_sentinel(true)
  }

  fn new(k: K, v: V, levels: usize) -> Self {
    let mut next = Vec::new();
    for _ in 0..levels {
      next.push(MarkableAtomic::null());
    }

    Node {
      key: k,
      value: AtomicPtr::new(Box::into_raw(Box::new(v))),
      is_tail: false,
      next: next,
    }
  }

  fn toplevel(&self) -> usize {
    self.next.len()
  }
}


//////////////////////////////////////////////////////////////////////////////
//// Dictionary Implementation
//////////////////////////////////////////////////////////////////////////////

/// A `ConcurrentDict<K,V>` implemented using a lock-free skiplist.
pub struct ConcurrentSkiplistDict<K,V> {
  head: Arc<MarkablePtr<K,V>>,
}

impl<K,V> ConcurrentSkiplistDict<K,V>
where K: Eq + Ord, V: Clone {
  fn find<'a>(&mut self, k: &K, guard: &'a Guard) 
          -> (SharedPtr<'a,K,V>, Vec<SharedPtr<'a,K,V>>, Vec<SharedPtr<'a,K,V>>)
  {
    let mut preds = Vec::new();
    let mut succs = Vec::new();

    // return here every time a CAS fails
    'retry: loop {
      let mut pred = self.head
                       .load_shared(Ordering::SeqCst, guard)
                       .unwrap();
      let n = (*pred).toplevel();
      let mut curr = (*pred).next[n-1]
                       .load_shared(Ordering::SeqCst, guard)
                       .unwrap();
      let mut succ;
      let mut mark;
      let mut pair;

      // proceed down through each level
      for i in (0..n).rev() {
        curr = (*pred).next[i]
                 .load_shared(Ordering::SeqCst, guard)
                 .unwrap();

        // advance curr until curr is not less than key
        loop {
          pair = (*curr).next[i]
                   .load(Ordering::SeqCst, guard);
          succ = pair.0;
          mark = pair.1;

          // physical deletion of marked nodes 
          while mark {
            let ok = (*pred).next[i]
                       .cas_shared(Some(curr), succ,
                                   false, false,
                                   Ordering::SeqCst);
            if !ok {
              continue 'retry;
            }

            curr = (*pred).next[i]
                     .load_shared(Ordering::SeqCst, guard)
                     .unwrap();
            pair = (*curr).next[i]
                     .load(Ordering::SeqCst, guard);
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
        preds.push(Some(pred));
        succs.push(Some(curr));
      }

      // bottom level reached
      let mut p = None;
      if !(*curr).is_tail && (*curr).key == *k {
        p = Some(curr);
      }
      preds.reverse();
      succs.reverse();
      return (p, preds, succs); 
    }
  }
}

impl<K,V> Dict<K,V> for ConcurrentSkiplistDict<K,V>
where K: Eq + Ord, V: Clone {
  fn new() -> Self {
    let guard = epoch::pin();

    let head = Node::new_head();
    let tail_atomic = MarkableAtomic::new(Node::new_tail(), false);

    let tail_shared = tail_atomic.load_shared(Ordering::Relaxed, &guard);
    for i in 0..MAX_LEVELS {
      head.next[i].store_shared(tail_shared, false, Ordering::Relaxed);
    }

    Self {
      head: Arc::new(MarkableAtomic::new(head, false)),
    }
  }

  fn get(&self, k: &K) -> Option<V> {
    let guard = epoch::pin();

    let mut pred = self.head.load_shared(Ordering::SeqCst, &guard)
                            .unwrap();
    let n = (*pred).toplevel();
    let mut curr = (*pred).next[n-1]
                     .load_shared(Ordering::SeqCst, &guard)
                     .unwrap();
    let mut succ;
    let mut mark;

    // proceed down through all levels, starting at top
    for i in (0..n).rev() {
      curr = (*pred).next[i]
               .load_shared(Ordering::SeqCst, &guard)
               .unwrap();

      // advance until curr is not less than key
      loop {
        let pair = (*curr).next[i]
                     .load(Ordering::SeqCst, &guard);
        succ = pair.0;
        mark = pair.1;

        // skip marked nodes
        while mark {
          curr = succ.unwrap();
          let pair = (*curr).next[i]
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
    let mut node = Owned::new(Node::new(k, v.clone(), new_top));

    // return here for retry
    loop {
      let (p, mut preds, mut succs) = self.find(&(*node).key, &guard);

      // check if node exists
      if p.is_some() {
        let p = p.unwrap();
        let oldp = (*p).value.load(Ordering::SeqCst);
        let newp = Box::into_raw(Box::new(v.clone()));
        if (*p).value.compare_and_swap(oldp, newp, Ordering::SeqCst) != oldp {
          continue; // retry
        }
        unsafe { return Some((*oldp).clone()); }
      }

      // set next pointers in new node
      for i in 0..new_top {
        let succ = succs[i];
        node.next[i].store_shared(succ, false, Ordering::SeqCst);
      }

      // attempt CAS at bottom level
      let pred = preds[0].unwrap();
      let succ = succs[0];
      match (*pred).next[0].cas_and_ref(succ, node,
                                        false, false,
                                        Ordering::SeqCst, &guard) {
        Ok(node) => {
          // node is now in list, do CAS on ith level
          for i in 1..new_top {
            loop {
              let pred = preds[i].unwrap();
              let succ = succs[i];
              if (*pred).next[i].cas_shared(succ, Some(node),
                                            false, false,
                                            Ordering::SeqCst) {
                break; // success on ith level
              }

              // retry find
              let triple = self.find(&(*node).key, &guard);
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
      let (p, _, _) = self.find(k, &guard);

      // check if node exists
      if p.is_none() {
        return None;
      }
      let p = p.unwrap();
      let mut succ;
      let mut mark;

      // mark each level, starting from top
      for i in (1..p.toplevel()).rev() {
        let pair = (*p).next[i].load(Ordering::SeqCst, &guard);
        succ = pair.0;
        mark = pair.1;

        while !mark {
          (*p).next[i].mark(succ, false, true, Ordering::SeqCst);
          let pair = (*p).next[i].load(Ordering::SeqCst, &guard);
          succ = pair.0;
          mark = pair.1;
        }
      }

      // mark bottom level
      succ = (*p).next[0].load_shared(Ordering::SeqCst, &guard);
      loop {
        let ok = (*p).next[0].mark(succ, false, true, Ordering::SeqCst);
        let pair = (*p).next[0].load(Ordering::SeqCst, &guard);
        succ = pair.0;
        mark = pair.1;

        if ok {
          // mark succeeded, get value
          let vp = (*p).value.load(Ordering::SeqCst);
          let v;
          unsafe { v = (*vp).clone(); }

          // do physical deletion
          self.find(k, &guard);
          //unsafe { guard.unlinked(p); }

          return Some(v);
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

impl<K,V> Clone for ConcurrentSkiplistDict<K,V>
where K: Eq + Ord, V: Clone {
  fn clone(&self) -> Self {
    Self {
      head: self.head.clone(),
    }
  }
}

impl<K,V> ConcurrentDict<K,V> for ConcurrentSkiplistDict<K,V>
where K: Eq + Ord + Send + Sync, V: Clone + Send + Sync {}
