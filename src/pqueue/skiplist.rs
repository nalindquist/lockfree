use std::sync::Arc;
use std::sync::atomic::{Ordering, AtomicBool};
use std::mem;
use std::time::Instant;
use rand::{self, Rng};
use crossbeam::epoch::{self, MarkableAtomic, Owned};
use super::*;


//////////////////////////////////////////////////////////////////////////////
//// Skiplist - Utilities
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

fn null_vec<T>() -> Vec<MarkablePtr<T>> {
  let mut v = Vec::new();
  for _ in 0..MAX_LEVELS {
    v.push(MarkableAtomic::null());
  }
  v
}


//////////////////////////////////////////////////////////////////////////////
//// Skiplist - Node Representation
//////////////////////////////////////////////////////////////////////////////

type MarkablePtr<T> = MarkableAtomic<Node<T>>;

struct Node<T> {
  elem: T,
  removed: AtomicBool,
  time: Instant,
  is_tail: bool,
  next: Vec<MarkablePtr<T>>,
}

impl<T> Node<T> {
  fn new_sentinel(is_tail: bool) -> Self {
    let next = null_vec();

    unsafe {
      Self {
        elem: mem::uninitialized(),
        removed: AtomicBool::new(false),
        time: Instant::now(),
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

  fn new(elem: T, levels: usize) -> Self {
    let mut next = Vec::new();
    for _ in 0..levels {
      next.push(MarkableAtomic::null());
    }

    Self {
      elem: elem,
      removed: AtomicBool::new(false),
      time: Instant::now(),
      is_tail: false,
      next: next,
    }
  }

  fn toplevel(&self) -> usize {
    self.next.len()
  }
}


//////////////////////////////////////////////////////////////////////////////
//// Skiplist - Implementation
//////////////////////////////////////////////////////////////////////////////

struct Skiplist<T> {
  head: Arc<MarkablePtr<T>>,
  tail: Arc<MarkablePtr<T>>,
}

impl<T> Skiplist<T>
where T: Eq + Ord + Clone, {
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
      tail: Arc::new(tail_atomic),
    }
  }

  fn find(&mut self, elem: &T) 
          -> (MarkablePtr<T>, Vec<MarkablePtr<T>>, Vec<MarkablePtr<T>>) 
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
        

        // advance curr until curr is not less than elem
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

            // release memory
            if i == 0 {
              unsafe { guard.unlinked(curr); }
            }

            curr = (*pred).next[i as usize]
                     .load_shared(Ordering::SeqCst, &guard)
                     .unwrap();
            pair = (*curr).next[i as usize]
                     .load(Ordering::SeqCst, &guard);
            succ = pair.0;
            mark = pair.1;
          }

          if !(*curr).is_tail && (*curr).elem < *elem {
            pred = curr;
            curr = succ.unwrap();
          } else {
            break;
          }
        }

        // curr is not less than elem, record pred and succ nodes
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
      if !(*curr).is_tail && (*curr).elem == *elem {
        p.store_shared(Some(curr), false, Ordering::SeqCst);
      }
      return (p, preds, succs); 
    }
  }

  fn insert(&mut self, elem: T) -> bool {
    let guard = epoch::pin();
    let new_top = get_toplevel();
    let mut node = Owned::new(Node::new(elem, new_top));

    // return here for retry
    loop {
      let (p, mut preds, mut succs) = self.find(&(*node).elem);

      // check if node exists
      let curr = p.load_shared(Ordering::SeqCst, &guard);
      if curr.is_some() {
        return false;
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
              let triple = self.find(&(*node).elem);
              preds = triple.1;
              succs = triple.2;
            }
          }

          // all levels updated
          return true;
        }
        Err(owned) => {
          node = owned;
          continue; // retry
        }
      }
    }
  }

  fn remove(&mut self, elem: &T) -> Option<T> {
    let guard = epoch::pin();

    loop {
      let (p, _, succs) = self.find(elem);

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
          self.find(elem);
          return Some((*curr).elem.clone());
        } else if mark {
          // someone beat us to it
          return None; 
        }
      }
    }
  }

  fn is_empty(&self) -> bool {
    self.size() == 0
  }

  fn size(&self) -> usize {
    let guard = epoch::pin();

    let head = self.head.load_shared(Ordering::SeqCst, &guard)
                        .unwrap();
    let mut curr = (*head).next[0].load_shared(Ordering::SeqCst, &guard)
                                  .unwrap();
    let mut count = 0;

    while !(*curr).is_tail {
      if !(*curr).removed.load(Ordering::SeqCst) {
        count += 1;
      }
      curr = (*curr).next[0].load_shared(Ordering::SeqCst, &guard)
                            .unwrap();
    }

    count
  }

  fn mark_min(&mut self) -> Option<T> {
    let guard = epoch::pin();
    let mut curr;

    'retry: loop {
      let start = Instant::now();
      curr = self.head.load_shared(Ordering::SeqCst, &guard)
                      .unwrap();
      curr = curr.next[0]
               .load_shared(Ordering::SeqCst, &guard)
               .unwrap();

      // serach through lowest level
      while !(*curr).is_tail {
        let removed = (*curr).removed.load(Ordering::SeqCst);

        if start <= (*curr).time {
          continue 'retry;
        }
        if !removed {
          if (*curr).removed.compare_and_swap(false, true, Ordering::SeqCst) == false {
            return Some((*curr).elem.clone());
          }
        }

        curr = curr.next[0]
                 .load_shared(Ordering::SeqCst, &guard)
                 .unwrap();
      }

      // no non-removed nodes found
      return None;
    }
  }
}

impl<T> Clone for Skiplist<T> {
  fn clone(&self) -> Self {
    Self {
      head: self.head.clone(),
      tail: self.tail.clone(),
    }
  }
}


//////////////////////////////////////////////////////////////////////////////
//// SkiplistPQueue Implementation
//////////////////////////////////////////////////////////////////////////////

/// A `ConcurrentPQueue<T>` implemented using a lock-free skiplist and
/// timestamps.
pub struct SkiplistPQueue<T> {
  skiplist: Skiplist<T>,
}

impl<T> PQueue<T> for SkiplistPQueue<T> 
where T: Eq + Ord + Clone {
  fn new() -> Self {
    Self {
      skiplist: Skiplist::new(),
    }
  }

  fn insert(&mut self, elem: T) -> bool {
    self.skiplist.insert(elem)
  }

  fn remove_min(&mut self) -> Option<T> {
    let r = self.skiplist.mark_min();
    r.map(|i| {
      self.skiplist.remove(&i);
      i
    })
  }

  fn is_empty(&self) -> bool {
    self.skiplist.is_empty()
  }

  fn size(&self) -> usize {
    self.skiplist.size()
  }
}

impl<T> Clone for SkiplistPQueue<T> {
  fn clone(&self) -> Self {
    Self {
      skiplist: self.skiplist.clone()
    }
  }
}

impl<T> ConcurrentPQueue<T> for SkiplistPQueue<T> 
where T: Eq + Ord + Clone + Send + Sync {}
