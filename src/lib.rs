//! A priority queue based on a [pairing heap].
//!
//! See [`PairingHeap`](struct.PairingHeap.html) for details.
//!
//! [pairing heap]: https://en.wikipedia.org/wiki/Pairing_heap

#![deny(missing_docs)]

use std::fmt::{self, Debug};
use std::{mem, slice};

#[derive(Clone)]
struct Node<T> {
    item: T,
    children: Vec<Node<T>>,
}

impl<T> Node<T> {
    fn merge(&mut self, mut other: Self) where T: Ord {
        if self.item < other.item {
            mem::swap(self, &mut other);
        }

        self.children.push(other);
    }

    fn reduce(nodes: Vec<Self>) -> Option<Self> where T: Ord {
        fn unwrap<T>(option: Option<T>) -> T {
            match option {
                None => if cfg!(debug) { panic!() } else { unreachable!() },
                Some(t) => t,
            }
        }

        let mut nodes = nodes.into_iter();

        nodes.next().map(|mut root| {
            if nodes.len() % 2 == 1 {
                root.merge(unwrap(nodes.next()));
            }

            while let Some(mut node) = nodes.next() {
                node.merge(unwrap(nodes.next()));
                root.merge(node);
            }

            root
        })
    }

    fn replace_item(&mut self, mut item: T) -> T where T: Ord {
        mem::swap(&mut item, &mut self.item);
        let mut node = self;

        loop {
            let tmp = node;
            let mut it = tmp.children.iter_mut();

            match it.next() {
                None => return item,
                Some(mut max) => {
                    for child in it {
                        if child.item > max.item {
                            max = child;
                        }
                    }

                    if tmp.item > max.item { return item; }
                    mem::swap(&mut tmp.item, &mut max.item);
                    node = max;
                }
            }
        }
    }
}

/// An iterator that drains a `PairingHeap`, yielding its items in arbitrary order.
///
/// Acquire through [`PairingHeap::drain`](struct.PairingHeap.html#method.drain).
pub struct Drain<'a, T: 'a + Ord> {
    heap: &'a mut PairingHeap<T>,
}

impl<'a, T: Ord> Drop for Drain<'a, T> {
    fn drop(&mut self) {
        self.heap.clear();
    }
}

impl<'a, T: Ord> Iterator for Drain<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.heap.pop()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.heap.len, Some(self.heap.len))
    }
}

impl<'a, T: Ord> ExactSizeIterator for Drain<'a, T> {
    fn len(&self) -> usize {
        self.heap.len
    }
}

/// An iterator that yields the items in a `PairingHeap` in arbitrary order.
///
/// Acquire through [`IntoIterator::into_iter`](struct.PairingHeap.html#method.into_iter).
pub struct IntoIter<T: Ord> {
    heap: PairingHeap<T>,
}

impl<T: Ord> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.heap.pop()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.heap.len, Some(self.heap.len))
    }
}

impl<T: Ord> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.heap.len
    }
}

/// An iterator that yields references to the items in a `PairingHeap` in arbitrary order.
///
/// Acquire through [`PairingHeap::iter`](struct.PairingHeap.html#method.iter).
pub struct Iter<'a, T: 'a + Ord> {
    iters: Vec<slice::Iter<'a, Node<T>>>,
    len: usize,
}

impl<'a, T: Ord> Clone for Iter<'a, T> {
    fn clone(&self) -> Self {
        Iter { iters: self.iters.clone(), len: self.len }
    }
}

impl<'a, T: Ord> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            let node = match self.iters.last_mut() {
                None => return None,
                Some(iter) => iter.next(),
            };

            if let Some(node) = node {
                self.iters.push(node.children.iter());
                self.len -= 1;
                return Some(&node.item);
            }

            self.iters.pop();
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T: Ord> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

/// A priority queue based on a pairing heap.
///
/// Like [`BinaryHeap`], `PairingHeap` is an implementation of a priority queue. Unlike
/// `BinaryHeap`, `PairingHeap` provides an `append` method whose runtime is asymptotically
/// optimal, at the cost of greater memory usage, slower iteration, and poor cache locality.
///
/// # Time Complexity
///
/// | Operation                      | Time Complexity        |
/// |--------------------------------|------------------------|
/// | [`append`](#method.append)     | `O(1)`                 |
/// | [`peek`](#method.peek)         | `O(1)`                 |
/// | [`pop`](#method.pop)           | `O(log n)` (amortized) |
/// | [`push`](#method.push)         | `O(1) `                |
/// | [`push_pop`](#method.push_pop) | `O(log n)` (amortized) |
/// | [`replace`](#method.replace)   | `O(log n)` (amortized) |
///
/// [`BinaryHeap`]: https://doc.rust-lang.org/std/collections/struct.BinaryHeap.html
#[derive(Clone)]
pub struct PairingHeap<T: Ord> {
    root: Option<Node<T>>,
    len: usize,
}

impl<T: Ord> PairingHeap<T> {
    /// Returns a new heap.
    pub fn new() -> Self {
        PairingHeap { root: None, len: 0 }
    }

    /// Checks if the heap is empty.
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// Returns the number of items in the heap.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns an iterator that yields references to the items in the heap in arbitrary order.
    pub fn iter(&self) -> Iter<T> {
        Iter {
            iters: self.root.as_ref()
                .map(|root| unsafe { slice::from_raw_parts(root, 1) }.iter())
                .into_iter()
                .collect(),
            len: self.len,
        }
    }

    /// Returns a reference to the greatest item in the heap.
    ///
    /// Returns `None` if the heap is empty.
    pub fn peek(&self) -> Option<&T> {
        self.root.as_ref().map(|root| &root.item)
    }

    /// Pushes the given item onto the heap.
    pub fn push(&mut self, item: T) {
        self.len += 1;
        let node = Node { item: item, children: vec![] };

        match self.root {
            None => self.root = Some(node),
            Some(ref mut root) => root.merge(node),
        }
    }

    /// Moves the given heap's items into the heap, leaving the given heap empty.
    ///
    /// This is equivalent to, but likely to be faster than, the following:
    ///
    /// ```
    /// # let mut heap = pairing_heap::PairingHeap::<i32>::new();
    /// # let mut heap2 = pairing_heap::PairingHeap::new();
    /// heap.extend(heap2.drain());
    /// ```
    pub fn append(&mut self, other: &mut Self) {
        match self.root {
            None => mem::swap(self, other),
            Some(ref mut root) => if let Some(other_root) = other.root.take() {
                root.merge(other_root);
                self.len += mem::replace(&mut other.len, 0);
            },
        }
    }

    /// Pushes the given item onto the heap, then removes the greatest item in the heap and returns
    /// it.
    ///
    /// This method is equivalent to, but likely faster than, the following:
    ///
    /// ```
    /// # let mut heap = pairing_heap::PairingHeap::new();
    /// # let item = 0;
    /// heap.push(item);
    /// let max = heap.pop().unwrap();
    /// ```
    pub fn push_pop(&mut self, item: T) -> T {
        match self.root {
            Some(ref mut root) if item < root.item => root.replace_item(item),
            _ => item,
        }
    }

    /// Removes the greatest item in the heap, then pushes the given item onto the heap.
    ///
    /// Returns the item that was removed, or `None` if the heap was empty.
    ///
    /// This method is equivalent to, but likely faster than, the following:
    ///
    /// ```
    /// # let mut heap = pairing_heap::PairingHeap::new();
    /// # let item = 0;
    /// let max = heap.pop();
    /// heap.push(item);
    /// ```
    pub fn replace(&mut self, item: T) -> Option<T> {
        match self.root {
            None => { self.push(item); None }
            Some(ref mut root) => Some(root.replace_item(item)),
        }
    }

    /// Removes the greatest item in the heap and returns it.
    ///
    /// Returns `None` if the heap was empty.
    ///
    /// If a call to this method is immediately preceded by a call to [`push`], consider using
    /// [`push_pop`] instead. If a call to this method is immediately followed by a call to
    /// [`push`], consider using [`replace`] instead.
    ///
    /// [`push`]: #method.push
    /// [`push_pop`]: #method.push_pop
    /// [`replace`]: #method.replace
    pub fn pop(&mut self) -> Option<T> {
        self.root.take().map(|Node { item, children }| {
            self.len -= 1;
            self.root = Node::reduce(children);
            item
        })
    }

    /// Removes all items from the heap.
    pub fn clear(&mut self) {
        *self = Self::new();
    }

    /// Removes all items from the heap and returns an iterator that yields them in arbitrary
    /// order.
    ///
    /// All items are removed even if the iterator is not exhausted. However, the behavior of
    /// this method is unspecified if the iterator is leaked (e.g. via [`mem::forget`]).
    ///
    /// [`mem::forget`]: https://doc.rust-lang.org/std/mem/fn.forget.html
    pub fn drain(&mut self) -> Drain<T> {
        Drain { heap: self }
    }
}

impl<T: Ord + Debug> Debug for PairingHeap<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<T: Ord> Default for PairingHeap<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Ord> Extend<T> for PairingHeap<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, items: I) {
        for item in items { self.push(item); }
    }
}

impl<T: Ord> std::iter::FromIterator<T> for PairingHeap<T> {
    fn from_iter<I: IntoIterator<Item = T>>(items: I) -> Self {
        let mut heap = Self::new();
        heap.extend(items);
        heap
    }
}

impl<T: Ord> IntoIterator for PairingHeap<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        IntoIter { heap: self }
    }
}

impl<'a, T: Ord> IntoIterator for &'a PairingHeap<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}
