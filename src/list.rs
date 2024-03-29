
// singly linked list implementation
// https://rust-unofficial.github.io/too-many-lists/index.html
// https://github.com/rust-unofficial/too-many-lists/blob/master/lists/src/second.rs

pub struct List<T> { head: Link<T>, }

type Link<T> = Option<Box<Node<T>>>;
struct Node<T> { elem: T, next: Link<T>, }

//type Link<T> = Option<Rc<RefCell<Box<Node<T>>>>>;
//struct Node<T> { elem: Rc<T>, prev: Link<T>, next: Link<T>, }

impl<T> Default for List<T> { fn default() -> Self { Self::new() } }

impl<T> List<T> {
    pub fn new() -> Self { List { head: None } }

    pub fn push(&mut self, elem: T) {
        self.head = Some(Box::new(Node { elem, next: self.head.take(), }));
    }

    pub fn pop(&mut self) -> Option<T> {
        self.head.take().map(|node| { self.head = node.next;  node.elem })
    }

    pub fn peek(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.elem)
    }

    pub fn peek_mut(&mut self) -> Option<&mut T> {
        self.head.as_mut().map(|node| &mut node.elem)
    }

    pub fn iter(&self) -> Iter<'_, T> { Iter { next: self.head.as_deref() } }

    pub fn iter_mut(&mut self) -> IterMut<'_, T> { IterMut { next: self.head.as_deref_mut() } }
}

impl<T> IntoIterator for List<T> {
    type IntoIter = IntoIter<T>;    type Item = T;
    fn into_iter(self) -> Self::IntoIter { IntoIter(self) }
}

impl<T> Drop for List<T> {
    fn drop(&mut self) {
        let mut cur_link = self.head.take();
        while let Some(mut boxed_node) = cur_link {
            cur_link = boxed_node.next.take();
        }
    }
}

pub struct IntoIter<T>(List<T>);

impl<T> Iterator for IntoIter<T> {  type Item = T;
    // access fields of a tuple struct numerically
    fn next(&mut self) -> Option<Self::Item> { self.0.pop() }
}

pub struct Iter<'a, T> { next: Option<&'a Node<T>>, }

impl<'a, T> Iterator for Iter<'a, T> {
    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|node| { self.next = node.next.as_deref(); &node.elem })
    }   type Item = &'a T;
}

pub struct IterMut<'a, T> { next: Option<&'a mut Node<T>>, }

impl<'a, T> Iterator for IterMut<'a, T> {
    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().map(|node| {
            self.next = node.next.as_deref_mut(); &mut node.elem })
    }   type Item = &'a mut T;
}

#[cfg(test)] mod tests {    use super::List;

    #[test] fn basics() {
        let mut list: List<i32> = Default::default();

        // Check empty list behaves right
        assert_eq!(list.pop(), None);

        // Populate list
        list.push(1);
        list.push(2);
        list.push(3);

        // Check normal removal
        assert_eq!(list.pop(), Some(3));
        assert_eq!(list.pop(), Some(2));

        // Push some more just to make sure nothing's corrupted
        list.push(4);
        list.push(5);

        // Check normal removal
        assert_eq!(list.pop(), Some(5));
        assert_eq!(list.pop(), Some(4));

        // Check exhaustion
        assert_eq!(list.pop(), Some(1));
        assert_eq!(list.pop(), None);
    }

    #[test] fn peek() {
        let mut list = List::new();
        assert_eq!(list.peek(), None);
        assert_eq!(list.peek_mut(), None);
        list.push(1); list.push(2); list.push(3);

        assert_eq!(list.peek(), Some(&3));
        assert_eq!(list.peek_mut(), Some(&mut 3));

        if let Some(value) = list.peek_mut() { *value = 42 }

        assert_eq!(list.peek(), Some(&42));
        assert_eq!(list.pop(), Some(42));
    }

    #[test] fn into_iter() {
        let mut list = List::new();
        list.push(1); list.push(2); list.push(3);

        let mut iter = list.into_iter();
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), None);
    }

    #[test] fn iter() {
        let mut list = List::new();
        list.push(1); list.push(2); list.push(3);

        let mut iter = list.iter();
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&1));
    }

    #[test] fn iter_mut() {
        let mut list = List::new();
        list.push(1); list.push(2); list.push(3);

        let mut iter = list.iter_mut();
        assert_eq!(iter.next(), Some(&mut 3));
        assert_eq!(iter.next(), Some(&mut 2));
        assert_eq!(iter.next(), Some(&mut 1));
    }
}
