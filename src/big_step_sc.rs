// ### Schemes of different types of big-step supercompilation

// A variation of the scheme presented in the paper
//
// Ilya G. Klyuchnikov, Sergei A. Romanenko. Formalizing and Implementing
// Multi-Result Supercompilation.
// In Third International Valentin Turchin Workshop on Metacomputation
// (Proceedings of the Third International Valentin Turchin Workshop on
// Metacomputation. Pereslavl-Zalessky, Russia, July 5-9, 2012).
// A.V. Klimov and S.A. Romanenko, Ed. - Pereslavl-Zalessky: Ailamazyan
// University of Pereslavl, 2012, 260 p. ISBN 978-5-901795-28-6, pages
// 142-164.

// Now we formulate an idealized model of big-step multi-result
// supercompilation.
//
// The knowledge about the input language a supercompiler deals with
// is represented by a "world of supercompilation", which is a trait
// that specifies the following.
//
// * `C` is the type of "configurations". Note that configurations are
//   not required to be just expressions with free variables! In general,
//   they may represent sets of states in any form/language and as well may
//   contain any _additional_ information.
//
// * `is_foldable_to` is a "foldability relation". is_foldable_to(c, c') means
//   that c is foldable to c'.
//   (In such cases c' is usually said to be " more general than c".)
//
// * `develop` is a function that gives a number of possible decompositions of
//   a configuration. Let `c` be a configuration and `cs` a list of
//   configurations such that `cs ∈ develop(c)`. Then `c` can be "reduced to"
//   (or "decomposed into") configurations in `cs`.
//
//   Suppose that driving is deterministic and, given a configuration `c`,
//   produces a list of configurations `drive(c)`. Suppose that rebuilding
//   (generalization, application of lemmas) is non-deterministic and
//   `rebuild(c)` is the list of configurations that can be produced by
//   rebuilding. Then (in this special case) `develop` is implemented
//   as follows:
//
//       develop(c) = List(drive(c)) ::: rebuild(c).map(List(_))
//
// * `History` is a list of configuration that have been produced
//   in order to reach the current configuration.
//
// * `is_dangerous` is a "whistle" that is used to ensure termination of
//   supercompilation. `is_dangerous(h)` means that the history has become
//   "too large".
//
// * `is_foldable_to_history(c, h)` means that `c` is foldable to a configuration
//   in the history `h`.

use crate::graph::*;
use crate::misc::{cartesian, History};

use iter_comprehensions::{map, vec as vec_map};
use itertools::Itertools;
use std::rc::Rc;

pub trait ScWorld {
    type C: Clone;

    fn is_dangerous(&self, h: &History<Self::C>) -> bool;

    fn is_foldable_to(&self, c1: &Self::C, c2: &Self::C) -> bool;

    fn develop(&self, c: &Self::C) -> Vec<Vec<Self::C>>;

    fn is_foldable_to_history(
        &self,
        c: &Self::C,
        h: &History<Self::C>,
    ) -> bool {
        h.any(|c2| self.is_foldable_to(c, c2))
    }
}

// Big-step multi-result supercompilation
// (The naive version builds Cartesian products immediately.)

fn naive_mrsc_loop<S>(s: &S, h: &History<S::C>, c: S::C) -> Gs<S::C>
where
    S: ScWorld,
{
    if s.is_foldable_to_history(&c, &h) {
        return vec![back(&c)];
    } else if s.is_dangerous(&h) {
        return vec![];
    } else {
        let css = s.develop(&c);
        let h1 = h.cons(c.clone());
        let gsss = map!(cartesian(&vec_map!(naive_mrsc_loop(s, &h1, c1); c1 in cs));
                cs in css);
        return vec_map!(forth(&c, &gs); gs in Itertools::concat(gsss));
    }
}

pub fn naive_mrsc<S>(s: &S, c0: S::C) -> Gs<S::C>
where
    S: ScWorld,
{
    naive_mrsc_loop(s, &History::new(), c0)
}

// "Lazy" multi-result supercompilation.
// (Cartesian products are not immediately built.)
//
// lazy_mrsc is essentially a "staged" version of naive-mrsc
// with get-graphs being an "interpreter" that evaluates the "program"
// returned by lazy_mrsc.

fn lazy_mrsc_loop<S>(s: &S, h: &History<S::C>, c: S::C) -> Rc<LazyGraph<S::C>>
where
    S: ScWorld,
{
    if s.is_foldable_to_history(&c, &h) {
        stop(&c)
    } else if s.is_dangerous(&h) {
        empty()
    } else {
        let css = s.develop(&c);
        let h1 = h.cons(c.clone());
        let ls: Vec<Ls<S::C>> = vec_map!(vec_map!(lazy_mrsc_loop(s, &h1, c1); c1 in cs);
        cs in css);
        build(&c, &ls)
    }
}

pub fn lazy_mrsc<S>(s: &S, c0: S::C) -> Rc<LazyGraph<S::C>>
where
    S: ScWorld,
{
    lazy_mrsc_loop(s, &History::new(), c0)
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::rc::Rc;

    fn gs3() -> Vec<Rc<Graph<isize>>> {
        vec![
            forth(&0, &[forth(&1, &[forth(&2, &[back(&0), back(&1)])])]),
            forth(&0, &[forth(&1, &[forth(&2, &[back(&1)])])]),
            forth(
                &0,
                &[forth(&1, &[forth(&2, &[forth(&3, &[back(&0), back(&2)])])])],
            ),
            forth(&0, &[forth(&1, &[forth(&2, &[forth(&3, &[back(&2)])])])]),
        ]
    }

    fn naive_mrsc_isize(c: isize) -> Gs<isize> {
        naive_mrsc(&0isize, c)
    }

    fn lazy_mrsc_isize(c: isize) -> Rc<LazyGraph<isize>> {
        lazy_mrsc(&0isize, c)
    }

    #[test]
    fn test_naive_mrsc() {
        assert_eq!(naive_mrsc_isize(0), gs3())
    }

    #[test]
    fn test_unroll_lazy_mrsc() {
        assert_eq!(unroll(&lazy_mrsc_isize(0)), gs3());
    }

    #[test]
    fn test_min_size_cl() {
        assert_eq!(
            unroll(&cl_min_size(&lazy_mrsc_isize(0))),
            [forth(&0, &[forth(&1, &[forth(&2, &[back(&1)])])])]
        );
    }
}
