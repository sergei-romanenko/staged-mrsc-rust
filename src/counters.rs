use crate::big_step_sc::*;
use crate::misc::{cartesian, History};

use iter_comprehensions::vec as vec_map;
use itertools::zip;
use std::cmp::{Ordering, PartialOrd};
use std::convert::From;
use std::fmt;
use std::marker::PhantomData;
use std::ops::{Add, Sub};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NW {
    N(isize),
    W(),
}

use NW::{N, W};

impl fmt::Display for NW {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            N(i) => write!(f, "{}", i),
            W() => write!(f, "ω"),
        }
    }
}

impl From<isize> for NW {
    fn from(item: isize) -> Self {
        N(item)
    }
}

#[allow(non_camel_case_types)]
pub struct ω;

impl From<ω> for NW {
    fn from(_: ω) -> Self {
        W()
    }
}

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

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct NWC(pub Vec<NW>);

pub fn mk_nwc(nws: &[NW]) -> NWC {
    NWC(nws.to_vec())
}

#[macro_export]
macro_rules! nwc {
    ($($e:expr),*) => {
        mk_nwc(&[$({let _nw:NW = $e.into(); _nw}),*])
    };
}

impl fmt::Display for NWC {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let nws = vec_map!(format!("{}", nw); nw in self.0.clone());
        write!(f, "({})", nws.join(","))
    }
}

pub trait CountersWorld {
    fn start() -> NWC;
    fn rules(c: &NWC) -> Vec<(bool, NWC)>;
    fn is_unsafe(c: &NWC) -> bool;
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

fn is_too_big(c: &NWC, max_nw: isize) -> bool {
    c.0.iter().any(|&nw| is_too_big_nw(nw, max_nw))
}

fn drive<CW: CountersWorld>(c: &NWC) -> Vec<NWC> {
    vec_map!(pr.1; pr in CW::rules(c), pr.0)
}

fn rebuild1(nw: &NW) -> Vec<NW> {
    match nw {
        N(_) => vec![nw.clone(), W()],
        W() => vec![W()],
    }
}

fn rebuild(c: &NWC) -> Vec<Vec<NWC>> {
    let nwss: Vec<Vec<NW>> = cartesian(&vec_map!(rebuild1(nw); nw in &c.0));
    let cs = vec_map!(mk_nwc(&nws); nws in nwss);
    vec_map!(vec![c1]; c1 in cs, &c1 != c)
}

impl<CW: CountersWorld> ScWorld for CountersScWorld<CW> {
    type C = NWC;

    fn is_dangerous(&self, h: &History<Self::C>) -> bool {
        h.any(|c| is_too_big(c, self.max_nw)) || h.length() >= self.max_depth
    }

    fn is_foldable_to(&self, c1: &Self::C, c2: &Self::C) -> bool {
        zip(&c1.0, &c2.0).all(|(nw1, nw2)| is_in(nw1, nw2))
    }

    fn develop(&self, c: &Self::C) -> Vec<Vec<Self::C>> {
        [vec![drive::<CW>(c)], rebuild(c)].concat()
    }
}

#[macro_export]
macro_rules! mk_r_params {
    (@mk_tail $c:ident, $k:ident, $($i:ident),*) => {
        $(
            #[allow(unused_variables)]
            let $i = $c.0[$k]; $k += 1;
        )*
    };
    ($c:ident, $($i:tt)*) => {
        let mut _k = 0;
        mk_r_params!(@mk_tail $c, _k, $($i)*)
    };
}

#[macro_export]
macro_rules! counter_system {
    (
        Name $name:ident;
        Params($($params:tt)*);
        Start($($start:tt)*);
        Unsafe($unsafe:expr);
        Rules{
            $($p:expr => $($e:expr),*;)*
        };
    ) => {
        #[derive(Debug)]
        struct $name;
        impl CountersWorld for $name {
            fn start() -> NWC {
                nwc!($($start)*)
            }
            fn is_unsafe(_c: &NWC) -> bool {
                mk_r_params!(_c, $($params)*);
                $unsafe
            }

            fn rules(_c: &NWC) -> Vec<(bool, NWC)> {
                mk_r_params!(_c, $($params)*);

                vec![
                    $(($p, nwc!($($e),*)),)*
                ]
            }
        }
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

    #[test]
    fn test_into_nw() {
        let nw25 = NW::from(25);
        assert_eq!(nw25, N(25));
        let nw30 = {
            let _tmp: NW = 30.into();
            _tmp
        };
        assert_eq!(nw30, N(30));
        let w1 = NW::from(ω);
        assert_eq!(w1, W());
        let w2 = {
            let _tmp: NW = ω.into();
            _tmp
        };
        assert_eq!(w2, W());
    }

    #[test]
    fn test_nwc() {
        let i = N(10);
        assert_eq!(
            format!("{:?}", nwc!(25 + 1, ω, i + 1)),
            "NWC([N(26), W, N(11)])"
        );
        assert_eq!(format!("{:?}", nwc!()), "NWC([])");
    }

    #[test]
    fn test_display_nwc() {
        assert_eq!(nwc!(1, ω, 2).to_string(), "(1,ω,2)");
        assert_eq!(nwc!().to_string(), "()");
    }

    struct TestCW2;

    impl CountersWorld for TestCW2 {
        fn start() -> NWC {
            nwc!(2, 0)
        }

        fn rules(_c: &NWC) -> Vec<(bool, NWC)> {
            mk_r_params!(_c, i, j);

            vec![
                (i >= 1, nwc!(i - 1, j + 1)), //
                (j >= 1, nwc!(i + 1, j - 1)), //
            ]
        }

        fn is_unsafe(_: &NWC) -> bool {
            false
        }
    }

    counter_system! {
        Name TestCW;
        Params(i,j);
        Start(2, 0);
        Unsafe(false);
        Rules{
            i >= 1 => i - 1, j + 1;
            j >= 1 => i + 1, j - 1;
        };
    }

    fn mg() -> Rc<Graph<NWC>> {
        forth(
            &nwc!(2, 0),
            &[forth(&nwc!(ω, ω), &[back(&nwc!(ω, ω)), back(&nwc!(ω, ω))])],
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
