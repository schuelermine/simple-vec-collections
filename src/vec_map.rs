use std::{borrow::Borrow, fmt::Debug, iter::FusedIterator};

#[derive(Clone, Default, PartialEq, Eq)]
pub struct VecMap<K, V>(Vec<(K, V)>);

impl<K, V> VecMap<K, V> {
    pub fn new() -> VecMap<K, V> {
        VecMap(Vec::new())
    }

    pub fn with_capacity(capacity: usize) -> VecMap<K, V> {
        VecMap(Vec::with_capacity(capacity))
    }

    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys(self.iter())
    }

    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys(self.into_iter())
    }

    pub fn values(&self) -> Values<'_, K, V> {
        Values(self.iter())
    }

    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut(self.iter_mut())
    }

    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues(self.into_iter())
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter(self.0.iter())
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut(self.0.iter_mut())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn drain(&mut self) -> Drain<'_, K, V> {
        Drain(self.0.drain(..))
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        let g = |(key, value): &mut (K, V)| f(key, value);
        self.0.retain_mut(g)
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

impl<K, V> VecMap<K, V>
where
    K: Eq,
{
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        match self.0.iter().position(|(k, _)| *k == key) {
            Some(index) => Entry::Occupied(OccupiedEntry {
                index,
                key,
                map: self,
            }),
            None => Entry::Vacant(VacantEntry { key, map: self }),
        }
    }

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

    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        let mut result = None;
        for (key, value) in self {
            if k == (*key).borrow() {
                result = Some(value);
                break;
            }
        }
        result
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        match self.get_mut(&k) {
            Some(value) => Some(std::mem::replace(value, v)),
            None => {
                self.0.push((k, v));
                None
            }
        }
    }

    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        let index = self.0.iter().position(|(key, _)| key.borrow() == k)?;
        let (_, value) = self.0.remove(index);
        Some(value)
    }

    pub fn remove_entry<Q: ?Sized>(&mut self, k: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        let index = self.0.iter().position(|(key, _)| key.borrow() == k)?;
        Some(self.0.remove(index))
    }
}

impl<K: Debug, V: Debug> Debug for VecMap<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<'a, K, V> Extend<(&'a K, &'a V)> for VecMap<K, V>
where
    K: Eq + Copy,
    V: Copy,
{
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0);
        for (key, value) in iter {
            self.insert(*key, *value);
        }
    }
}

impl<K, V> Extend<(K, V)> for VecMap<K, V>
where
    K: Eq,
{
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0);
        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

impl<K, V, const N: usize> From<[(K, V); N]> for VecMap<K, V>
where
    K: Eq,
{
    fn from(arr: [(K, V); N]) -> Self {
        let mut map = Self::with_capacity(arr.len());
        for (key, value) in arr {
            map.insert(key, value);
        }
        map
    }
}

impl<K, V> FromIterator<(K, V)> for VecMap<K, V>
where
    K: Eq,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut map = Self::with_capacity(iter.size_hint().0);
        for (key, value) in iter {
            map.insert(key, value);
        }
        map
    }
}

impl<K, Q: ?Sized, V> std::ops::Index<&Q> for VecMap<K, V>
where
    K: Borrow<Q> + Eq,
    Q: Eq,
{
    type Output = V;
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
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

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
}

impl<K, V> FusedIterator for Keys<'_, K, V> {}

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
}

impl<K, V> FusedIterator for IntoKeys<K, V> {}

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
}

impl<K, V> FusedIterator for Values<'_, K, V> {}

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
}

impl<K, V> FusedIterator for ValuesMut<'_, K, V> {}

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
}

impl<K, V> FusedIterator for IntoValues<K, V> {}

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
}

impl<K, V> FusedIterator for Iter<'_, K, V> {}

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
}

impl<K, V> FusedIterator for IntoIter<K, V> {}

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
}

impl<K, V> FusedIterator for IterMut<'_, K, V> {}

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
}

impl<K, V> FusedIterator for Drain<'_, K, V> {}

#[derive(Debug)]
pub enum Entry<'a, K, V> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V> {
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(o) => o.into_mut(),
            Entry::Vacant(v) => v.insert(default),
        }
    }

    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(o) => o.into_mut(),
            Entry::Vacant(v) => v.insert(default()),
        }
    }

    pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(o) => o.into_mut(),
            Entry::Vacant(v) => {
                let default = default(&v.key);
                v.insert(default)
            }
        }
    }

    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(o) => o.key(),
            Entry::Vacant(v) => v.key(),
        }
    }

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
    pub fn or_default(self) -> &'a mut V {
        self.or_insert(Default::default())
    }
}

pub struct OccupiedEntry<'a, K, V> {
    index: usize,
    key: K,
    map: &'a mut VecMap<K, V>,
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    pub fn key(&self) -> &K {
        &self.key
    }

    pub fn remove_entry(self) -> (K, V) {
        self.map.0.remove(self.index)
    }

    pub fn get(&self) -> &V {
        &self.map.0[self.index].1
    }

    pub fn get_mut(&mut self) -> &mut V {
        &mut self.map.0[self.index].1
    }

    pub fn into_mut(self) -> &'a mut V {
        &mut self.map.0[self.index].1
    }

    pub fn insert(&mut self, value: V) -> V {
        std::mem::replace(&mut self.map.0[self.index].1, value)
    }

    pub fn remove(self) -> V {
        self.map.0.remove(self.index).1
    }
}

impl<K: Debug, V> Debug for OccupiedEntry<'_, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("OccupiedEntry").field(self.key()).finish()
    }
}

pub struct VacantEntry<'a, K, V> {
    key: K,
    map: &'a mut VecMap<K, V>,
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    pub fn key(&self) -> &K {
        &self.key
    }

    pub fn into_key(self) -> K {
        self.key
    }

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
