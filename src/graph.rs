//
// Graphs of configurations
//

use crate::misc::cartesian;

use iter_comprehensions::{map, sum as vec_sum, vec as vec_map};
use itertools::Itertools;
use std::fmt;
use std::rc::Rc;

// A `Graph[C]` is supposed to represent a residual program.
// Technically, a `Graph[C]` is a tree, with `back` nodes being
// references to parent nodes.
//
// A graph's nodes contain configurations. Here we abstract away
// from the concrete structure of configurations.
// In this model the arrows in the graph carry no information,
// because this information can be kept in nodes.
// (Hence, this information is supposed to be encoded inside
// "configurations".)
//
// To simplify the machinery, back-nodes in this model of
// supercompilation do not contain explicit references
// to parent nodes. Hence, `Back(c)` means that `c` is foldable
// to a parent configuration (perhaps, to several ones).
//
// * Back-nodes are produced by folding a configuration to another
//  configuration in the history.
// * Forth-nodes are produced by
//    + decomposing a configuration into a number of other configurations
//      (e.g. by driving or taking apart a let-expression), or
//    + by rewriting a configuration by another one (e.g. by generalization,
//      introducing a let-expression or applying a lemma during
//      two-level supercompilation).

// Graph

#[derive(Clone, PartialEq, Debug)]
pub enum Graph<C> {
  Back(C),
  Forth(C, Gs<C>),
}

pub type Gs<C> = Vec<Rc<Graph<C>>>;

use Graph::{Back, Forth};

pub fn back<C: Clone>(c: &C) -> Rc<Graph<C>> {
  Rc::new(Back(c.clone()))
}

pub fn forth<C: Clone>(c: &C, gs: &[Rc<Graph<C>>]) -> Rc<Graph<C>> {
  Rc::new(Forth(c.clone(), vec_map!(Rc::clone(g); g in gs)))
}

// GraphPrettyPrinter

fn graph_pretty_printer_loop<C: fmt::Display>(
  g: &Graph<C>,
  indent: usize,
) -> String {
  let mut sb: Vec<String> = Vec::new();
  let ind = " ".repeat(indent);
  match g {
    Back(c) => {
      sb.push(format!("{}{}{}{}", ind, "|__", c, "*"));
    }
    Forth(c, gs) => {
      sb.push(format!("{}{}{}", ind, "|__", c));
      for g1 in gs {
        sb.push(format!("{}{}{}", "\n  ", ind, "|"));
        sb.push(format!(
          "{}{}",
          "\n",
          graph_pretty_printer_loop(g1, indent + 2)
        ));
      }
    }
  }
  sb.join("")
}

pub fn graph_pretty_printer<C: fmt::Display>(g: &Graph<C>) -> String {
  graph_pretty_printer_loop(g, 0)
}

//
// Lazy graphs of configurations
//

// A `LazyGraph a` represents a finite set of graphs
// of configurations (whose type is `Graph a`).
//
// "Lazy" graphs of configurations will be produced
// by the "lazy" (staged) version of multi-result
// supercompilation.

// LazyGraph

#[derive(Clone, PartialEq, Debug)]
pub enum LazyGraph<C> {
  Empty(),
  Stop(C),
  Build(C, Vec<Ls<C>>),
}

pub type Ls<C> = Vec<Rc<LazyGraph<C>>>;

use LazyGraph::{Build, Empty, Stop};

pub fn empty<C: Clone>() -> Rc<LazyGraph<C>> {
  Rc::new(Empty())
}

pub fn stop<C: Clone>(c: &C) -> Rc<LazyGraph<C>> {
  Rc::new(Stop(c.clone()))
}

pub fn build<C: Clone>(c: &C, lss: &[Ls<C>]) -> Rc<LazyGraph<C>> {
  Rc::new(Build(
    c.clone(),
    vec_map!(vec_map!(Rc::clone(l); l in ls); ls in lss),
  ))
}

// The semantics of a `LazyGraph a` is formally defined by
// the interpreter `unroll` that generates a list of `Graph a` from
// the `LazyGraph a` by executing commands recorded in the `LazyGraph a`.

pub fn unroll<C: Clone>(l: &LazyGraph<C>) -> Gs<C> {
  match l {
    Empty() => Vec::new(),
    Stop(c) => vec![back(c)],
    Build(c, lss) => {
      let gss = Itertools::concat(
        map!(cartesian(&vec_map!(unroll(l); l in ls)); ls in lss),
      );
      vec_map!(forth(c, &gs); gs in gss)
    }
  }
}

// Usually, we are not interested in the whole bag `unroll(l)`.
// The goal is to find "the best" or "most interesting" graphs.
// Hence, there should be developed some techniques of extracting
// useful information from a `LazyGraph[C]` without evaluating
// `unroll(l)` directly.

// This can be formulated in the following form.
// Suppose that a function `select` filters bags of graphs,
// removing "bad" graphs, so that
//     select (unroll l)
// generates the bag of "good" graphs.
// Let us find a function `extract` such that
//     extract(l) == select(unroll(l))
// In many cases, `extract` may be more efficient (by several orders
// of magnitude) than the composition `select . unroll`.
// Sometimes, `extract` can be formulated in terms of "cleaners" of
// lazy graphs. Let `clean` be a function that transforms lazy graphs,
// such that
//     unroll(clean(l)) ⊆ unroll(l)
// Then `extract` can be constructed in the following way:
//     extract(l) == unroll(clean(l))
// Theoretically speaking, `clean` is the result of "promoting" `select`:
//     (select compose unroll)(l) == (unroll compose clean)(l)
// The nice property of cleaners is that they are composable:
// given `clean1` and `clean2`, `clean2 compose clean1` is also a cleaner.

//
// Some filters
//

// Removing graphs that contain "bad" configurations.
// Configurations represent states of a computation process.
// Some of these states may be "bad" with respect to the problem
// that is to be solved by means of supercompilation.

fn bad_graph<C>(bad: fn(&C) -> bool, g: &Graph<C>) -> bool {
  match g {
    Back(c) => bad(c),
    Forth(c, gs) => bad(c) || gs.iter().any(|g| bad_graph(bad, g)),
  }
}

// This filter removes the graphs containing "bad" configurations.

pub fn fl_bad_conf<C>(bad: fn(&C) -> bool, gs: Gs<C>) -> Gs<C> {
  vec_map!(g; g in gs, !bad_graph(bad, &g))
}

//
// Some cleaners
//

// `cl_empty` removes subtrees that represent empty sets of graphs.

pub fn cl_empty<C: Clone>(l: &LazyGraph<C>) -> Rc<LazyGraph<C>> {
  match l {
    Empty() => empty(),
    Stop(c) => stop(c),
    Build(c, lss) => cl_empty_build(c, &cl_empty_lss(lss)),
  }
}

fn cl_empty_build<C: Clone>(c: &C, lss: &[Ls<C>]) -> Rc<LazyGraph<C>> {
  if lss.is_empty() {
    empty()
  } else {
    build(c, lss)
  }
}

fn cl_empty_lss<C: Clone>(lss: &Vec<Ls<C>>) -> Vec<Ls<C>> {
  lss.into_iter().filter_map(|ls| cl_empty_ls(ls)).collect()
}

fn cl_empty_ls<C: Clone>(ls: &Ls<C>) -> Option<Ls<C>> {
  let ls1 = vec_map!(cl_empty(l); l in ls);
  if ls1.clone().into_iter().any(|l| is_lg_empty(&l)) {
    None
  } else {
    Some(ls1)
  }
}

fn is_lg_empty<C>(l: &LazyGraph<C>) -> bool {
  match l {
    Empty() => true,
    _ => false,
  }
}

// Removing graphs that contain "bad" configurations.
// The cleaner `cl_bad_conf` corresponds to the filter `fl_bad_conf`.
// `cl_bad_conf` exploits the fact that "badness" is monotonic,
// in the sense that a single "bad" configuration spoils the whole
// graph.

fn cl_bad_conf<C: Clone>(
  bad: fn(&C) -> bool,
  l: &LazyGraph<C>,
) -> Rc<LazyGraph<C>> {
  match l {
    Empty() => empty(),
    Stop(c) => {
      if bad(c) {
        empty()
      } else {
        stop(c)
      }
    }
    Build(c, lss) => {
      if bad(c) {
        empty()
      } else {
        build(
          c,
          &vec_map!(vec_map!(cl_bad_conf(bad, l); l in ls); ls in lss),
        )
      }
    }
  }
}

//
// The graph returned by `cl_bad_conf` may be cleaned by `cl_empty`.
//

pub fn cl_empty_and_bad<C: Clone>(
  bad: fn(&C) -> bool,
  l: &LazyGraph<C>,
) -> Rc<LazyGraph<C>> {
  cl_empty(&cl_bad_conf(bad, l))
}

//
// Extracting a graph of minimal size (if any).
//

pub fn graph_size<C>(g: &Graph<C>) -> usize {
  match g {
    Back(_) => 1,
    Forth(_, gs) => 1 + vec_sum!(graph_size(g1); g1 in gs),
  }
}

// Now we define a cleaner `cl_min_size` that produces a lazy graph
// representing the smallest graph (or the empty set of graphs).

// We use a trick: ∞ is represented by Long.MaxValue in
// (Long.MaxValue , Empty).

pub fn cl_min_size<C: Clone>(l: &LazyGraph<C>) -> Rc<LazyGraph<C>> {
  sel_min_size(l).1
}

fn sel_min_size<C: Clone>(l: &LazyGraph<C>) -> (usize, Rc<LazyGraph<C>>) {
  match l {
    Empty() => (usize::MAX, empty()),
    Stop(c) => (1, stop(c)),
    Build(c, lss) => match sel_min_size2(lss) {
      (usize::MAX, _) => (usize::MAX, empty()),
      (k, ls) => (1 + k, build(c, &[ls])),
    },
  }
}

fn select_min2<T: Clone>(kx1: (usize, T), kx2: (usize, T)) -> (usize, T) {
  if kx1.0 <= kx2.0 {
    kx1
  } else {
    kx2
  }
}

fn sel_min_size2<C: Clone>(lss: &[Ls<C>]) -> (usize, Ls<C>) {
  let mut acc = (usize::MAX, Vec::<Rc<LazyGraph<C>>>::new());
  for ls in lss {
    acc = select_min2(sel_min_size_and(ls), acc);
  }
  acc
}

fn sel_min_size_and<C: Clone>(ls: &[Rc<LazyGraph<C>>]) -> (usize, Ls<C>) {
  let mut k = 0usize;
  let mut ls1 = Vec::<Rc<LazyGraph<C>>>::new();
  for l in ls {
    let (k1, l1) = sel_min_size(l);
    k = add_min_size(k, k1);
    ls1.push(l1);
  }
  (k, ls1)
}

fn add_min_size(x1: usize, x2: usize) -> usize {
  if x1 == usize::MAX || x2 == usize::MAX {
    usize::MAX
  } else {
    x1 + x2
  }
}

//
// `cl_min_size` is sound:
//
//  Let cl_min_size(l) == (k , l'). Then
//     unroll(l') ⊆ unroll(l)
//     k == graph_size (hd (unroll(l')))

#[cfg(test)]
mod tests {
  use super::*;

  type IGraph = Graph<isize>;
  type ILazyGraph = LazyGraph<isize>;

  fn bad_i(c: &isize) -> bool {
    *c < 0
  }

  fn g1() -> Rc<IGraph> {
    forth(&1, &[back(&1), forth(&2, &[back(&1), back(&2)])])
  }

  #[test]
  fn test_graph_pretty_printer() {
    assert_eq!(
      graph_pretty_printer(&g1()),
      "|__1\n  |\n  |__1*\n  |\n  |__2\n    |\n    |__1*\n    |\n    |__2*"
    );
  }

  #[test]
  fn test_cartesian() {
    let xs = vec![1, 2];
    let ys = vec![10, 20, 30];
    let zs = vec![100, 200];
    let vss = vec![xs.clone(), ys.clone(), zs.clone()];
    let rss = [
      [1, 10, 100],
      [1, 10, 200],
      [1, 20, 100],
      [1, 20, 200],
      [1, 30, 100],
      [1, 30, 200],
      [2, 10, 100],
      [2, 10, 200],
      [2, 20, 100],
      [2, 20, 200],
      [2, 30, 100],
      [2, 30, 200],
    ];
    let xs0zs = vec![xs.clone(), vec![], zs.clone()];
    let zzs: Vec<Vec<isize>> = vec![];

    assert_eq!(cartesian(&vss), &rss);
    assert_eq!(cartesian(&xs0zs), &[[0]; 0]);
    assert_eq!(cartesian(&zzs), &[[0; 0]; 1]);
  }

  fn g_bad_forth() -> Rc<IGraph> {
    forth(&1, &[back(&1), forth(&-2, &[back(&3), back(&4)])])
  }

  fn g_bad_back() -> Rc<IGraph> {
    forth(&1, &[back(&1), forth(&2, &[back(&3), back(&-4)])])
  }

  fn l2() -> Rc<ILazyGraph> {
    build(
      &1,
      &[
        vec![build(&2, &[vec![stop(&1), stop(&2)]])],
        vec![build(&3, &[vec![stop(&3), stop(&1)]])],
      ],
    )
  }

  fn gs2() -> Vec<Rc<IGraph>> {
    vec![
      forth(&1, &[forth(&2, &[back(&1), back(&2)])]),
      forth(&1, &[forth(&3, &[back(&3), back(&1)])]),
    ]
  }

  fn l_empty() -> Rc<ILazyGraph> {
    build(
      &1,
      &[vec![stop(&2)], vec![build(&3, &[vec![stop(&4), empty()]])]],
    )
  }

  #[test]
  fn test_unroll() {
    assert_eq!(unroll(&l2()), gs2());
  }

  #[test]
  fn test_bad_graph() {
    assert!(!bad_graph(bad_i, &g1()));
    assert!(bad_graph(bad_i, &g_bad_forth()));
    assert!(bad_graph(bad_i, &g_bad_back()));
  }

  #[test]
  fn test_cl_empty() {
    assert_eq!(cl_empty(&l_empty()), build(&1, &[vec![stop(&2)]]));
  }

  fn l_bad_stop() -> Rc<ILazyGraph> {
    build(
      &1,
      &[vec![stop(&1), build(&2, &[vec![stop(&3), stop(&-4)]])]],
    )
  }

  fn l_bad_build() -> Rc<ILazyGraph> {
    build(
      &1,
      &[vec![stop(&1), build(&-2, &[vec![stop(&3), stop(&4)]])]],
    )
  }

  #[test]
  fn test_cl_bad_conf() {
    assert_eq!(
      cl_bad_conf(bad_i, &l_bad_stop()),
      build(&1, &[vec![stop(&1), build(&2, &[vec![stop(&3), empty()]])]])
    );
    assert_eq!(
      cl_bad_conf(bad_i, &l_bad_build()),
      build(&1, &[vec![stop(&1), empty()]])
    );
  }

  #[test]
  fn test_cl_empty_and_bad() {
    assert_eq!(cl_empty_and_bad(bad_i, &l_bad_stop()), empty());
    assert_eq!(cl_empty_and_bad(bad_i, &l_bad_build()), empty());
  }

  #[test]
  fn test_graph_size() {
    assert_eq!(graph_size(&g1()), 5);
  }

  fn l3() -> Rc<ILazyGraph> {
    build(
      &1,
      &[
        vec![build(&2, &[vec![stop(&1), stop(&2)]])],
        vec![build(&3, &[vec![stop(&4)]])],
      ],
    )
  }

  #[test]
  fn test_cl_min_size() {
    assert_eq!(
      cl_min_size(&l3()),
      build(&1, &[vec![build(&3, &[vec![stop(&4)]])]])
    )
  }

  #[test]
  fn test_cl_min_size_unroll() {
    let min_l = cl_min_size(&l3());
    let min_g = unroll(&min_l)[0].clone();
    assert_eq!(min_g, forth(&1, &[forth(&3, &[back(&4)])]));
  }
}
