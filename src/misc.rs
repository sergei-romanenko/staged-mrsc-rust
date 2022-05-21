// Miscellaneous

use iter_comprehensions::vec as vec_map;
use itertools::Itertools;
use std::rc::Rc;

//
// Cartesian product
//

pub fn cartesian<X: Clone>(xss: &Vec<Vec<X>>) -> Vec<Vec<X>> {
    if xss.is_empty() {
        vec![vec![]]
    } else {
        let yss = xss.iter().multi_cartesian_product();
        vec_map!(vec_map!(y.clone(); y in ys); ys in yss)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum History<T> {
    Nil,
    Cons(T, Rc<History<T>>),
}

use History::{Cons, Nil};

impl<T: Clone> History<T> {
    pub fn new() -> History<T> {
        Nil
    }

    pub fn cons(&self, x: T) -> History<T> {
        match *self {
            Cons(ref h, ref t) => Cons(x, Rc::new(Cons(h.clone(), t.clone()))),
            Nil => Cons(x, Rc::new(Nil)),
        }
    }

    pub fn length(&self) -> usize {
        match &self {
            Nil => 0,
            Cons(_, t) => 1 + t.length(),
        }
    }

    pub fn any(&self, p: impl Fn(&T) -> bool) -> bool {
        let mut list = self.clone();
        loop {
            match &list {
                Nil => return false,
                Cons(h, t) => {
                    if p(h) {
                        return true;
                    }
                    list = (**t).clone();
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_list_ok() {
        let l1: History<usize> = History::new();
        let l2 = l1.cons(3).cons(2).cons(1);

        assert_eq!(
            l2,
            Cons(1, Rc::new(Cons(2, Rc::new(Cons(3, Rc::new(Nil))))))
        );

        assert!(l2.any(|&t| t == 2));
        assert!(!l2.any(|&t| t == 5));
    }
}
