use std::marker::PhantomData;

#[derive(Derivative)]
#[derivative(Copy, Clone, Debug, PartialEq)]
pub struct Key<K>(
    usize,
    #[derivative(Debug="ignore")]
    PhantomData<fn(&K) -> ()>
);

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq)]
pub struct Store<K, T> {
    items: Vec<T>,
    #[derivative(Debug="ignore")]
    key_phantom: PhantomData<fn(&K) -> ()>,
}

impl<K, T> Store<K, T> {
    pub fn new() -> Self {
        Store {
            items: Vec::new(),
            key_phantom: PhantomData,
        }
    }

    pub fn insert(&mut self, v: T) -> Key<K> {
        self.items.push(v);
        Key(self.items.len() - 1, PhantomData)
    }

    pub fn get(&self, key: Key<K>) -> &T {
        let idx = key.0;
        self.items.get(idx).expect("Store::get called with an invalid key")
    }
}
