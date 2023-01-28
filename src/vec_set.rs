use std::{
    borrow::Borrow,
    fmt::Debug,
    iter::{Chain, FusedIterator},
    ops::{BitAnd, BitOr, BitXor, Sub},
};

#[derive(Clone, PartialEq, Eq)]
pub struct VecSet<T>(Vec<T>);

impl<T> VecSet<T> {
    pub fn new() -> Self {
        VecSet(Vec::new())
    }

    pub fn with_capacity(capacity: usize) -> Self {
        VecSet(Vec::with_capacity(capacity))
    }

    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    pub fn iter(&self) -> Iter<'_, T> {
        Iter(self.0.iter())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn drain(&mut self) -> Drain<'_, T> {
        Drain(self.0.drain(..))
    }

    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.0.retain(f)
    }

    pub fn clear(&mut self) {
        self.0.clear()
    }

    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional)
    }

    pub fn try_reserve(
        &mut self,
        additional: usize,
    ) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }

    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.0.shrink_to(min_capacity)
    }
}

impl<T: Eq> VecSet<T> {
    pub fn difference<'a>(&'a self, other: &'a VecSet<T>) -> Difference<'a, T> {
        Difference(self.iter(), other)
    }

    pub fn symmetric_difference<'a>(&'a self, other: &'a VecSet<T>) -> SymmetricDifference<'a, T> {
        SymmetricDifference(self.difference(other).chain(other.difference(self)))
    }

    pub fn intersection<'a>(&'a self, other: &'a VecSet<T>) -> Intersection<'a, T> {
        Intersection(self.iter(), other)
    }

    pub fn union<'a>(&'a self, other: &'a VecSet<T>) -> Union<'a, T> {
        Union(self.iter().chain(other.difference(self)))
    }

    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Eq,
    {
        self.get(value).is_some()
    }

    pub fn get<Q: ?Sized>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: Eq,
    {
        self.iter().find(|&v| v.borrow() == value)
    }

    pub fn is_disjoint(&self, other: &VecSet<T>) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| !other.contains(v))
        } else {
            other.iter().all(|v| !self.contains(v))
        }
    }

    pub fn is_subset(&self, other: &VecSet<T>) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| other.contains(v))
        } else {
            false
        }
    }

    pub fn is_superset(&self, other: &VecSet<T>) -> bool {
        other.is_subset(self)
    }

    pub fn insert(&mut self, value: T) -> bool {
        for v in &*self {
            if *v == value {
                return false;
            }
        }
        self.0.push(value);
        true
    }

    pub fn replace(&mut self, value: T) -> Option<T> {
        for v in &mut self.0 {
            if *v == value {
                return Some(std::mem::replace(v, value));
            }
        }
        None
    }

    pub fn remove<Q: ?Sized>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Eq,
    {
        let mut index = None;
        for (i, v) in self.0.iter().enumerate() {
            if v.borrow() == value {
                index = Some(i);
            }
        }
        match index {
            Some(i) => {
                self.0.remove(i);
                true
            }
            None => false,
        }
    }

    pub fn take<Q: ?Sized>(&mut self, value: &Q) -> Option<T>
    where
        T: Borrow<Q>,
        Q: Eq,
    {
        let mut index = None;
        for (i, v) in self.0.iter().enumerate() {
            if v.borrow() == value {
                index = Some(i)
            }
        }
        match index {
            Some(i) => Some(self.0.remove(i)),
            None => None,
        }
    }
}

impl<T: Eq + Clone> BitAnd<&VecSet<T>> for &VecSet<T> {
    type Output = VecSet<T>;
    fn bitand(self, rhs: &VecSet<T>) -> Self::Output {
        self.intersection(rhs).cloned().collect()
    }
}

impl<T: Eq + Clone> BitOr<&VecSet<T>> for &VecSet<T> {
    type Output = VecSet<T>;
    fn bitor(self, rhs: &VecSet<T>) -> Self::Output {
        self.union(rhs).cloned().collect()
    }
}

impl<T: Eq + Clone> BitXor<&VecSet<T>> for &VecSet<T> {
    type Output = VecSet<T>;
    fn bitxor(self, rhs: &VecSet<T>) -> Self::Output {
        self.symmetric_difference(rhs).cloned().collect()
    }
}

impl<T: Debug> Debug for VecSet<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<T> Default for VecSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, T: Eq + Copy> Extend<&'a T> for VecSet<T> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        for value in iter {
            self.insert(*value);
        }
    }
}

impl<T: Eq> Extend<T> for VecSet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for value in iter {
            self.insert(value);
        }
    }
}

impl<T: Eq, const N: usize> From<[T; N]> for VecSet<T> {
    fn from(arr: [T; N]) -> Self {
        let mut set = Self::with_capacity(arr.len());
        set.extend(arr);
        set
    }
}

impl<T: Eq> FromIterator<T> for VecSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut set = Self::with_capacity(iter.size_hint().0);
        set.extend(iter);
        set
    }
}

impl<'a, T> IntoIterator for &'a VecSet<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T> IntoIterator for VecSet<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

impl<T: Eq + Clone> Sub<&VecSet<T>> for &VecSet<T> {
    type Output = VecSet<T>;
    fn sub(self, rhs: &VecSet<T>) -> Self::Output {
        self.difference(rhs).cloned().collect()
    }
}

pub struct Iter<'a, T>(std::slice::Iter<'a, T>);

impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Iter(self.0.clone())
    }
}

impl<T: Debug> Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<T> FusedIterator for Iter<'_, T> {}

pub struct Drain<'a, T>(std::vec::Drain<'a, T>);

impl<T: Debug> Debug for Drain<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl<T> ExactSizeIterator for Drain<'_, T> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<T> Iterator for Drain<'_, T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl<T> FusedIterator for Drain<'_, T> {}

pub struct Difference<'a, T>(Iter<'a, T>, &'a VecSet<T>);

impl<T> Clone for Difference<'_, T> {
    fn clone(&self) -> Self {
        Difference(self.0.clone(), self.1)
    }
}

impl<T: Debug + Eq> Debug for Difference<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, T: Eq> Iterator for Difference<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let value = self.0.next()?;
            if !self.1.contains(value) {
                return Some(value);
            }
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let lhs_len = self.0.len();
        let rhs_len = self.1.len();
        (lhs_len.saturating_sub(rhs_len), Some(lhs_len))
    }
}

impl<T: Eq> FusedIterator for Difference<'_, T> {}

pub struct SymmetricDifference<'a, T>(Chain<Difference<'a, T>, Difference<'a, T>>);

impl<T> Clone for SymmetricDifference<'_, T> {
    fn clone(&self) -> Self {
        SymmetricDifference(self.0.clone())
    }
}

impl<T: Debug + Eq> Debug for SymmetricDifference<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl<'a, T: Eq> Iterator for SymmetricDifference<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<T: Eq> FusedIterator for SymmetricDifference<'_, T> {}

pub struct Intersection<'a, T>(Iter<'a, T>, &'a VecSet<T>);

impl<T> Clone for Intersection<'_, T> {
    fn clone(&self) -> Self {
        Intersection(self.0.clone(), self.1)
    }
}

impl<T: Debug + Eq> Debug for Intersection<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, T: Eq> Iterator for Intersection<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let value = self.0.next()?;
            if self.1.contains(value) {
                return Some(value);
            }
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let lhs_len = self.0.len();
        let rhs_len = self.1.len();
        (0, Some(std::cmp::min(lhs_len, rhs_len)))
    }
}

impl<T: Eq> FusedIterator for Intersection<'_, T> {}

pub struct Union<'a, T>(Chain<Iter<'a, T>, Difference<'a, T>>);

impl<T> Clone for Union<'_, T> {
    fn clone(&self) -> Self {
        Union(self.0.clone())
    }
}

impl<T: Debug + Eq> Debug for Union<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, T: Eq> Iterator for Union<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<T: Eq> FusedIterator for Union<'_, T> {}

pub struct IntoIter<T>(std::vec::IntoIter<T>);

impl<T: Debug> Debug for IntoIter<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<T> FusedIterator for IntoIter<T> {}
