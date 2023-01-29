//! Associative maps, backed by a [`Vec`].

use std::{borrow::Borrow, fmt::Debug, iter::FusedIterator};

/// An associative map.
/// It is a logic error for any key to change such that its equality
/// under the [`Eq`] trait changes while it is in the map.
/// To determine if two keys are “the same”, [`Eq`] is used.
#[derive(Clone, PartialEq, Eq)]
pub struct VecMap<K, V>(Vec<(K, V)>);

impl<K, V> VecMap<K, V> {
    /// Create a new [`VecMap`].
    pub fn new() -> VecMap<K, V> {
        VecMap(Vec::new())
    }

    /// Create a new [`VecMap`] with a given pre-allocated capacity.
    /// May allocate more than requested.
    pub fn with_capacity(capacity: usize) -> VecMap<K, V> {
        VecMap(Vec::with_capacity(capacity))
    }

    /// Get the allocated capacity of the map.
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Get an iterator over the keys as references.
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys(self.iter())
    }

    /// Get an iterator over the keys.
    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys(self.into_iter())
    }

    /// Get an iterator over the values as references.
    pub fn values(&self) -> Values<'_, K, V> {
        Values(self.iter())
    }

    /// Get an iterator over the values as mutable references.
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut(self.iter_mut())
    }

    /// Get an iterator over the values.
    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues(self.into_iter())
    }

    /// Get an iterator over the key-value pairs as tuples of reference.
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter(self.0.iter())
    }

    /// Get an iterator over the key-value pairs as tuples of a reference and a mutable reference.
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut(self.0.iter_mut())
    }

    /// Get the amount of key-value pairs in the map.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Check if the map is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Empty the map and return an iterator over the cleared key-value pairs.
    pub fn drain(&mut self) -> Drain<'_, K, V> {
        Drain(self.0.drain(..))
    }

    /// Remove all key-value pairs that don’t satisfy a given predicate.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        let g = |(key, value): &mut (K, V)| f(key, value);
        self.0.retain_mut(g)
    }

    /// Remove all key-value pairs.
    pub fn clear(&mut self) {
        self.0.clear()
    }

    /// Reserve additional space. May allocate more than requested.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation fails.
    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional)
    }

    /// Like [`reserve`], but returns a [`Result`] instead of panicking.
    ///
    /// [`reserve`]: VecMap::reserve
    pub fn try_reserve(
        &mut self,
        additional: usize,
    ) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    /// Shrink the capacity of the map as much as possible.
    /// May keep more than precisely needed.
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }

    /// Shrink the capacity of the map with a lower limit.
    /// May keep more than precisely needed.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.0.shrink_to(min_capacity)
    }
}

impl<K: Eq, V> VecMap<K, V> {
    /// Returns an [`Entry`] for the given key.
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        match self.keys().position(|k| *k == key) {
            Some(index) => Entry::Occupied(OccupiedEntry {
                index,
                key,
                map: self,
            }),
            None => Entry::Vacant(VacantEntry { key, map: self }),
        }
    }

    /// Get the given key’s value, if it exists.
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        let mut result = None;
        for (key, value) in self {
            if k == key.borrow() {
                result = Some(value);
                break;
            }
        }
        result
    }

    /// Get the given key’s key-value pair, if it exists.
    pub fn get_key_value<Q: ?Sized>(&self, k: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        let mut result = None;
        for (key, value) in self {
            if k == key.borrow() {
                result = Some((key, value));
                break;
            }
        }
        result
    }

    /// Check if the map contains a given key.
    pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        let mut present = false;
        for (key, _) in self {
            if k == key.borrow() {
                present = true;
                break;
            }
        }
        present
    }

    /// Get a mutable reference to the given key’s value, if it exists.
    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        let mut result = None;
        for (key, value) in self {
            if k == key.borrow() {
                result = Some(value);
                break;
            }
        }
        result
    }

    /// Insert a key-value pair into the map.
    /// If the key already exists, the old value is returned.
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        match self.get_mut(&k) {
            Some(value) => Some(std::mem::replace(value, v)),
            None => {
                self.0.push((k, v));
                None
            }
        }
    }

    /// Remove the given key’s key-value pair from the map.
    /// Returns the removed value, if it existed.
    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        let index = self.keys().position(|key| key.borrow() == k)?;
        let (_, value) = self.0.remove(index);
        Some(value)
    }

    /// Remove the given key’s key-value pair from the map.
    /// Returns the removed key-value pair, if it existed.
    pub fn remove_entry<Q: ?Sized>(&mut self, k: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        let index = self.keys().position(|key| key.borrow() == k)?;
        Some(self.0.remove(index))
    }
}

impl<K: Debug, V: Debug> Debug for VecMap<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V> Default for VecMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, K: Eq + Copy, V: Copy> Extend<(&'a K, &'a V)> for VecMap<K, V> {
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0);
        for (key, value) in iter {
            self.insert(*key, *value);
        }
    }
}

impl<K: Eq, V> Extend<(K, V)> for VecMap<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0);
        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

impl<K: Eq, V, const N: usize> From<[(K, V); N]> for VecMap<K, V> {
    fn from(arr: [(K, V); N]) -> Self {
        let mut map = Self::with_capacity(arr.len());
        map.extend(arr);
        map
    }
}

impl<K: Eq, V> FromIterator<(K, V)> for VecMap<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut map = Self::with_capacity(iter.size_hint().0);
        map.extend(iter);
        map
    }
}

impl<K, Q: ?Sized, V> std::ops::Index<&Q> for VecMap<K, V>
where
    K: Borrow<Q> + Eq,
    Q: Eq,
{
    type Output = V;

    /// Get a given key’s corresponding value from the map.
    ///
    /// # Panics
    ///
    /// Panics if the key is not in the map.
    fn index(&self, key: &Q) -> &Self::Output {
        self.get(key).expect("no entry found for key")
    }
}

impl<'a, K, V> IntoIterator for &'a VecMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut VecMap<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<K, V> IntoIterator for VecMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    /// Get an iterator over the key-value pairs.
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

/// An iterator over the keys of a map.
/// Yields the keys as references.
/// Generated by the [`keys`] method.
///
/// [`keys`]: VecMap::keys
pub struct Keys<'a, K, V>(Iter<'a, K, V>);

impl<K, V> Clone for Keys<'_, K, V> {
    fn clone(&self) -> Self {
        Keys(self.0.clone())
    }
}

impl<K: Debug, V> Debug for Keys<'_, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(Clone::clone(self)).finish()
    }
}

impl<K, V> ExactSizeIterator for Keys<'_, K, V> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(key, _)| key)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> FusedIterator for Keys<'_, K, V> {}

/// An iterator over the keys of a map.
/// Yields the keys as values.
/// Generated by the [`into_keys`] method.
///
/// [`into_keys`]: VecMap::into_keys
pub struct IntoKeys<K, V>(IntoIter<K, V>);

impl<K: Debug, V> Debug for IntoKeys<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.0 .0.as_slice().iter().map(|(key, _)| key))
            .finish()
    }
}

impl<K, V> ExactSizeIterator for IntoKeys<K, V> {
    fn len(&self) -> usize {
        self.0 .0.len()
    }
}

impl<K, V> Iterator for IntoKeys<K, V> {
    type Item = K;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(key, _)| key)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> FusedIterator for IntoKeys<K, V> {}

/// An iterator over the values of a map.
/// Yields the values as references.
/// Generated by the [`values`] method.
///
/// [`values`]: VecMap::values
pub struct Values<'a, K, V>(Iter<'a, K, V>);

impl<K, V> Clone for Values<'_, K, V> {
    fn clone(&self) -> Self {
        Values(self.0.clone())
    }
}

impl<K, V: Debug> Debug for Values<'_, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<K, V> ExactSizeIterator for Values<'_, K, V> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, value)| value)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> FusedIterator for Values<'_, K, V> {}

/// An iterator over the values of a map.
/// Yields the values as values.
/// Generated by the [`values_mut`] method.
///
/// [`values_mut`]: VecMap::values_mut
pub struct ValuesMut<'a, K, V>(IterMut<'a, K, V>);

impl<K, V: Debug> Debug for ValuesMut<'_, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.0 .0.as_slice().iter().map(|(_, value)| value))
            .finish()
    }
}

impl<K, V> ExactSizeIterator for ValuesMut<'_, K, V> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, value)| value)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> FusedIterator for ValuesMut<'_, K, V> {}

/// An iterator over the values of a map.
/// Yields the values as values.
/// Generated by the [`into_values`] method.
///
/// [`into_values`]: VecMap::into_values
pub struct IntoValues<K, V>(IntoIter<K, V>);

impl<K, V: Debug> Debug for IntoValues<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.0 .0.as_slice().iter().map(|(_, value)| value))
            .finish()
    }
}

impl<K, V> ExactSizeIterator for IntoValues<K, V> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<K, V> Iterator for IntoValues<K, V> {
    type Item = V;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, value)| value)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> FusedIterator for IntoValues<K, V> {}

/// An iterator over the key-value pairs of a map.
/// Yields the pairs as tuples of references.
/// Generated by the [`iter`] method.
///
/// [`iter`]: VecMap::iter
pub struct Iter<'a, K, V>(std::slice::Iter<'a, (K, V)>);

impl<K, V> Clone for Iter<'_, K, V> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<K: Debug, V: Debug> Debug for Iter<'_, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<K, V> ExactSizeIterator for Iter<'_, K, V> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        let (key, value) = self.0.next()?;
        Some((key, value))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> FusedIterator for Iter<'_, K, V> {}

/// An iterator over the key-value pairs of a map.
/// Yields the pairs as tuples of values.
/// Generated by the [`into_iter`] method.
///
/// [`into_iter`]: IntoIterator::into_iter
pub struct IntoIter<K, V>(std::vec::IntoIter<(K, V)>);

impl<K: Debug, V: Debug> Debug for IntoIter<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.0.as_slice().iter()).finish()
    }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> FusedIterator for IntoIter<K, V> {}

/// An iterator over the key-value pairs of a map.
/// Yields the pairs as tuples of a reference and a mutable reference.
/// Generated by the [`iter_mut`] method.
///
/// [`iter_mut`]: VecMap::iter_mut
pub struct IterMut<'a, K, V>(std::slice::IterMut<'a, (K, V)>);

impl<K: Debug, V: Debug> Debug for IterMut<'_, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.0.as_slice().iter()).finish()
    }
}

impl<K, V> ExactSizeIterator for IterMut<'_, K, V> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        let (key, value) = self.0.next()?;
        Some((key, value))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> FusedIterator for IterMut<'_, K, V> {}

/// An iterator over the removed key-value pairs of a map.
/// Yields the pairs as tuples of values.
/// Generated by the [`drain`] method.
///
/// [`drain`]: VecMap::drain
pub struct Drain<'a, K, V>(std::vec::Drain<'a, (K, V)>);

impl<K: Debug, V: Debug> Debug for Drain<'_, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.0.as_slice().iter()).finish()
    }
}

impl<K, V> ExactSizeIterator for Drain<'_, K, V> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<K, V> Iterator for Drain<'_, K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> FusedIterator for Drain<'_, K, V> {}

/// A view into a single key-value pair of a map.
/// Generated by the [`entry`] method.
///
/// [`entry`]: VecMap::entry
#[derive(Debug)]
pub enum Entry<'a, K, V> {
    /// The given key was already in the map.
    Occupied(OccupiedEntry<'a, K, V>),

    /// The given key was not in the map.
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V> {
    /// Insert a value under the entry’s key if the entry is vacant.
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(o) => o.into_mut(),
            Entry::Vacant(v) => v.insert(default),
        }
    }

    /// Like [`or_insert`], but takes a closure that is only called if the entry is vacant.
    ///
    /// [`or_insert`]: Entry::or_insert
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(o) => o.into_mut(),
            Entry::Vacant(v) => v.insert(default()),
        }
    }

    /// Like [`or_insert_with`], but the closure takes the entry’s key as an argument.
    ///
    /// [`or_insert_with`]: Entry::or_insert_with
    pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(o) => o.into_mut(),
            Entry::Vacant(v) => {
                let default = default(&v.key);
                v.insert(default)
            }
        }
    }

    /// Get a reference to the entry’s key.
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(o) => o.key(),
            Entry::Vacant(v) => v.key(),
        }
    }

    /// Modify the entry’s value if the entry is occupied.
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(mut o) => {
                let value = o.get_mut();
                f(value);
                Entry::Occupied(o)
            }
            Entry::Vacant(v) => Entry::Vacant(v),
        }
    }
}

impl<'a, K, V: Default> Entry<'a, K, V> {
    /// Insert the default value under the entry’s key if the key is vacant.
    pub fn or_default(self) -> &'a mut V {
        self.or_insert(Default::default())
    }
}

/// An occupied [`Entry`].
pub struct OccupiedEntry<'a, K, V> {
    index: usize,
    key: K,
    map: &'a mut VecMap<K, V>,
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    /// Get a reference to the entry’s key.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Remove the key-value pair at the entry’s key.
    pub fn remove_entry(self) -> (K, V) {
        self.map.0.remove(self.index)
    }

    /// Get a reference to the value at the entry’s key.
    pub fn get(&self) -> &V {
        &self.map.0[self.index].1
    }

    /// Get a mutable reference to the value at the entry’s key.
    pub fn get_mut(&mut self) -> &mut V {
        &mut self.map.0[self.index].1
    }

    /// Get a mutable reference to the value at the entry’s key that lives as long as the map.
    pub fn into_mut(self) -> &'a mut V {
        &mut self.map.0[self.index].1
    }

    /// Replace the value at the entry’s key with a new value.
    pub fn insert(&mut self, value: V) -> V {
        std::mem::replace(&mut self.map.0[self.index].1, value)
    }

    /// Remove the key-value pair at the entry’s key.
    pub fn remove(self) -> V {
        self.map.0.remove(self.index).1
    }
}

impl<K: Debug, V: Debug> Debug for OccupiedEntry<'_, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("OccupiedEntry")
            .field(self.key())
            .field(self.get())
            .finish()
    }
}

/// A vacant [`Entry`].
pub struct VacantEntry<'a, K, V> {
    key: K,
    map: &'a mut VecMap<K, V>,
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    /// Get a reference to the entry’s key.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Get the entry’s key.
    pub fn into_key(self) -> K {
        self.key
    }

    /// Insert a value under the entry’s key.
    pub fn insert(self, value: V) -> &'a mut V {
        self.map.0.push((self.key, value));
        &mut self.map.0.last_mut().unwrap().1
    }
}

impl<K: Debug, V> Debug for VacantEntry<'_, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("VacantEntry").field(self.key()).finish()
    }
}
