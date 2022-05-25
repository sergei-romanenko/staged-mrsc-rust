use crate::big_step_sc::*;
use crate::misc::{cartesian, History};

use iter_comprehensions::vec as vec_map;
use itertools::zip;
use std::cmp::{Ordering, PartialOrd};
use std::marker::PhantomData;
use std::ops::{Add, Sub};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NW {
    N(isize),
    W(),
}

use NW::{N, W};

impl Add<NW> for NW {
    type Output = NW;

    fn add(self, nw: NW) -> NW {
        match (self, nw) {
            (N(i), N(j)) => N(i + j),
            (N(_), W()) => W(),
            (W(), _) => W(),
        }
    }
}

impl Add<isize> for NW {
    type Output = NW;

    fn add(self, j: isize) -> NW {
        match self {
            N(i) => N(i + j),
            W() => W(),
        }
    }
}

impl Sub<NW> for NW {
    type Output = NW;

    fn sub(self, nw: NW) -> NW {
        match (self, nw) {
            (N(i), N(j)) => N(i - j),
            (N(_), W()) => W(),
            (W(), _) => W(),
        }
    }
}

impl Sub<isize> for NW {
    type Output = NW;

    fn sub(self, j: isize) -> NW {
        match self {
            N(i) => N(i - j),
            W() => W(),
        }
    }
}

impl PartialOrd<isize> for NW {
    fn partial_cmp(&self, j: &isize) -> Option<Ordering> {
        match self {
            N(i) => Some(if i < j {
                Ordering::Less
            } else if i > j {
                Ordering::Greater
            } else {
                Ordering::Equal
            }),
            W() => Some(Ordering::Equal),
        }
    }
}

impl PartialEq<isize> for NW {
    fn eq(&self, j: &isize) -> bool {
        match self {
            N(i) => (i == j),
            W() => true,
        }
    }
}

fn is_in(nwi: &NW, nwj: &NW) -> bool {
    match (nwi, nwj) {
        (N(i), N(j)) => i == j,
        (_, W()) => true,
        (W(), N(_)) => false,
    }
}

pub trait CountersWorld {
    fn start() -> Vec<NW>;
    fn rules(c: &Vec<NW>) -> Vec<(bool, Vec<NW>)>;
    fn is_unsafe(c: &Vec<NW>) -> bool;
}

pub struct CountersScWorld<CW: CountersWorld> {
    cw: PhantomData<CW>,
    max_nw: isize,
    max_depth: usize,
}

impl<CW: CountersWorld> CountersScWorld<CW> {
    pub fn new(
        _cw: CW,
        max_nw: isize,
        max_depth: usize,
    ) -> CountersScWorld<CW> {
        CountersScWorld {
            cw: PhantomData,
            max_nw: max_nw,
            max_depth: max_depth,
        }
    }
}

fn is_too_big_nw(nw: NW, max_nw: isize) -> bool {
    match nw {
        W() => false,
        N(i) => i >= max_nw,
    }
}

fn is_too_big(c: &Vec<NW>, max_nw: isize) -> bool {
    c.iter().any(|&nw| is_too_big_nw(nw, max_nw))
}

fn drive<CW: CountersWorld>(c: &Vec<NW>) -> Vec<Vec<NW>> {
    vec_map!(pr.1; pr in CW::rules(c), pr.0)
}

fn rebuild1(nw: &NW) -> Vec<NW> {
    match nw {
        N(_) => vec![nw.clone(), W()],
        W() => vec![W()],
    }
}

fn rebuild(c: &Vec<NW>) -> Vec<Vec<Vec<NW>>> {
    let cs = cartesian(&vec_map!(rebuild1(nw); nw in c));
    vec_map!(vec![c1]; c1 in cs, &c1 != c)
}

impl<CW: CountersWorld> ScWorld for CountersScWorld<CW> {
    type C = Vec<NW>;

    fn is_dangerous(&self, h: &History<Self::C>) -> bool {
        h.any(|c| is_too_big(c, self.max_nw)) || h.length() >= self.max_depth
    }

    fn is_foldable_to(&self, c1: &Self::C, c2: &Self::C) -> bool {
        zip(c1, c2).all(|(nw1, nw2)| is_in(nw1, nw2))
    }

    fn develop(&self, c: &Self::C) -> Vec<Vec<Self::C>> {
        [vec![drive::<CW>(c)], rebuild(c)].concat()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::graph::*;
    use std::rc::Rc;

    #[test]
    fn test_nw_add() {
        assert_eq!(N(1) + N(2), N(3));
        assert_eq!(N(3) + W(), W());
        assert_eq!(N(3) + 25, N(28));
    }

    #[test]
    fn test_nw_cmp() {
        assert!(N(2) >= 1);
        assert!(N(2) >= 2);
        assert!(!(N(1) >= 2));
        assert!(W() >= 1);
        assert!(N(2) == N(2));
        assert!(N(2) == 2);
        assert!(W() == 2);
    }

    #[test]
    fn test_is_in() {
        assert!(is_in(&N(2), &N(2)));
        assert!(!(is_in(&N(2), &N(3))));
        assert!(is_in(&N(2), &W()));
        assert!(is_in(&W(), &W()));
        assert!(!(is_in(&W(), &N(3))));
    }

    struct TestCW;

    impl CountersWorld for TestCW {
        fn start() -> Vec<NW> {
            vec![N(2), N(0)]
        }

        fn rules(ij: &Vec<NW>) -> Vec<(bool, Vec<NW>)> {
            let (i, j) = (ij[0], ij[1]);
            vec![(i >= 1, vec![i - 1, j + 1]), (j >= 1, vec![i + 1, j - 1])]
        }

        fn is_unsafe(_: &Vec<NW>) -> bool {
            false
        }
    }

    fn mg() -> Rc<Graph<Vec<NW>>> {
        forth(
            &vec![N(2), N(0)],
            &[forth(
                &vec![W(), W()],
                &[back(&vec![W(), W()]), back(&vec![W(), W()])],
            )],
        )
    }

    #[test]
    fn test_counters_sc_world() {
        let s = CountersScWorld::new(TestCW, 3, 10);
        let start_conf = TestCW::start();
        let gs = naive_mrsc(&s, start_conf.clone());
        let l = lazy_mrsc(&s, start_conf);
        assert_eq!(unroll(&l), gs);
        let ml = cl_min_size(&l);
        assert_eq!(&unroll(&ml)[0], &mg());
    }
}
