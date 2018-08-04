extern crate pairing_heap;
extern crate quickcheck;

use pairing_heap::PairingHeap;
use quickcheck::{Arbitrary, Gen, quickcheck};
use std::collections::BinaryHeap;

use Op::*;

#[derive(Clone, Copy, Debug)]
enum Op<T> {
    Push(T),
    PushPop(T),
    Pop,
    Replace(T),
}

fn push_pop_b<T: Ord>(heap: &mut BinaryHeap<T>, item: T) -> T {
    heap.push(item);
    heap.pop().expect("heap was empty after a call to `push`")
}

fn replace_b<T: Ord>(heap: &mut BinaryHeap<T>, item: T) -> Option<T> {
    let max = heap.pop();
    heap.push(item);
    max
}

impl<T> Op<T> {
    fn execute_b(self, heap: &mut BinaryHeap<T>) -> Option<T> where T: Ord {
        match self {
            Push(item) => { heap.push(item); None }
            PushPop(item) => Some(push_pop_b(heap, item)),
            Pop => heap.pop(),
            Replace(item) => replace_b(heap, item),
        }
    }

    fn execute_p(self, heap: &mut PairingHeap<T>) -> Option<T> where T: Ord {
        match self {
            Push(item) => { heap.push(item); None }
            PushPop(item) => Some(heap.push_pop(item)),
            Pop => heap.pop(),
            Replace(item) => heap.replace(item),
        }
    }
}

impl<T: Arbitrary> Arbitrary for Op<T> {
    fn arbitrary<G: Gen>(gen: &mut G) -> Self {
        match gen.gen_range(0, 10) {
            0 => PushPop(T::arbitrary(gen)),
            1 => Pop,
            2 => Replace(T::arbitrary(gen)),
            _ => Push(T::arbitrary(gen)),
        }
    }

    fn shrink(&self) -> Box<Iterator<Item = Self>> {
        match *self {
            PushPop(ref item) => Box::new(item.shrink().map(PushPop)),
            Push(ref item) => Box::new(item.shrink().map(Push)),
            Pop => Box::new(std::iter::empty()),
            Replace(ref item) => Box::new(item.shrink().map(Replace)),
        }
    }
}

#[test]
fn test_consistent_with_binary_heap() {
    fn t(ops: Vec<Op<i32>>) -> bool {
        let mut b = BinaryHeap::new();
        let mut p = PairingHeap::new();

        for op in ops {
            if op.execute_b(&mut b) != op.execute_p(&mut p) { return false; }
            if b.len() != p.len() { return false; }
        }

        while !b.is_empty() || !p.is_empty() {
            if b.pop() != p.pop() { return false; }
        }

        true
    }

    quickcheck(t as fn(_) -> _);
}

#[test]
fn test_append() {
    fn t(ops1: Vec<Op<i32>>, ops2: Vec<Op<i32>>) -> bool {
        let mut b1 = BinaryHeap::new();
        let mut p1 = PairingHeap::new();

        for op in ops1 {
            op.execute_b(&mut b1);
            op.execute_p(&mut p1);
        }

        let mut b2 = BinaryHeap::new();
        let mut p2 = PairingHeap::new();

        for op in ops2 {
            op.execute_b(&mut b2);
            op.execute_p(&mut p2);
        }

        b1.extend(b2);
        p1.append(&mut p2);

        while !b1.is_empty() || !p1.is_empty() {
            if b1.pop() != p1.pop() { return false; }
        }

        true
    }

    quickcheck(t as fn(_, _) -> _);
}

#[test]
fn test_iter() {
    fn t(ops: Vec<Op<i32>>) -> bool {
        let mut b = BinaryHeap::new();
        let mut p = PairingHeap::new();

        for op in ops {
            op.execute_b(&mut b);
            op.execute_p(&mut p);
        }

        let b_vec = b.into_sorted_vec();

        let mut p_vec: Vec<_> = p.iter().collect();
        p_vec.sort();

        b_vec.iter().eq(p_vec)
    }

    quickcheck(t as fn(_) -> _);
}
