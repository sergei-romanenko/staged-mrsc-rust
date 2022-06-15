/*
export
    build_graph8, cl8_bad_conf,
    prune
*/

//
// Lazy infinite graphs of configurations
//

// A `LazyGraph8[C]` represents a (potentially) infinite set of graphs
// of configurations (whose type is `Graph[C]`).
//
// "Lazy" infinite graphs of configurations will be produced
// by the "lazy" (staged) version of multi-result
// supercompilation.

/* using DataStructures
using StagedMRSC.Graphs
import StagedMRSC.BigStepSc:
    conf_type, is_foldable_to, is_dangerous, is_foldable_to_history, develop
*/

use crate::big_step_sc::ScWorld;
use crate::graph::*;
use crate::misc::*;

use iter_comprehensions::{map, vec as vec_map};
use lazy_st::*;
use std::cell::RefCell;
use std::rc::Rc;

//
// Infinite trees/graphs
// LazyGraph8
//

/*
abstract type LazyGraph8{C} end

mutable struct Empty8{C} <: LazyGraph8{C} end

mutable struct Stop8{C} <: LazyGraph8{C}
    c::C
end

mutable struct Build8{C} <: LazyGraph8{C}
    c::C
    _lss
end

function get_lss(g::Build8{C}) where {C}
    if g._lss isa Function
        g._lss = g._lss()
    end
    g._lss
end
*/

/*
enum LazyVal<T> {
    LvFnOnce(Box<dyn FnOnce() -> T>),
    LvVal(T),
}

fn get_lazy_val<T:Clone>(x : &RefCell<LazyVal<T>>) -> T {
    let mut cell = x.borrow_mut();
    match *cell {
        LazyVal::LvFnOnce(f) => {
            let v = f();
            *cell = LazyVal::LvVal(v);
            v
        },
        LazyVal::LvVal(v) => v,
    }
}

fn mk_lazy_val<T>(f: Box<dyn FnOnce() -> T>) -> LazyVal<T> {
    LazyVal::LvFnOnce(f)
}
*/

// #[derive(Clone)]
pub enum LazyGraph8<C: Clone> {
  Empty8(),
  Stop8(C),
  Build8(C, Rc<Lazy<Vec<L8s<C>>>>),
}

pub type L8s<C> = Vec<Rc<LazyGraph8<C>>>;

use LazyGraph8::{Build8, Empty8, Stop8};

pub fn empty8<C: Clone>() -> Rc<LazyGraph8<C>> {
  Rc::new(Empty8())
}

pub fn stop8<C: Clone>(c: &C) -> Rc<LazyGraph8<C>> {
  Rc::new(Stop8(c.clone()))
}

pub fn build8<C: Clone>(c: &C, l8ss: &Rc<Lazy<Vec<L8s<C>>>>) -> Rc<LazyGraph8<C>> {
  Rc::new(Build8(c.clone(), Rc::clone(l8ss)))
}

// build_graph8

/*
function build_graph8_loop(w, h, c)
    C = conf_type(w)
    if is_foldable_to_history(w, c, h)
        Stop8{C}(c)
    else
        function lss8()
            [[build_graph8_loop(w, cons(c, h), c1) for c1 in cs]
             for cs in develop(w, c)]
        end
        Build8{C}(c, lss8)
    end
end
*/

fn build_graph8_loop<S>(
  s: &'static S,
  h: &History<S::C>,
  c: &S::C,
) -> Rc<LazyGraph8<S::C>>
where
  S: ScWorld,
{
  if s.is_foldable_to_history(c, h) {
    stop8(c)
  } else if s.is_dangerous(h) {
    empty8()
  } else {
    let css = s.develop(c);
    let h1 = h.cons(c.clone());
    let l8ss: Rc<Lazy<Vec<L8s<S::C>>>> = Rc::new(lazy!(
      vec_map!(vec_map!(build_graph8_loop(s, &h1, &c1); c1 in cs); cs in css)
    ));
    build8(&c, &l8ss)
  }
}

/*
function build_graph8(w, c0)
    C = conf_type(w)
    build_graph8_loop(w, nil(C), c0)
end
*/

pub fn build_graph8<S>(s: &'static S, c0: &S::C) -> Rc<LazyGraph8<S::C>>
where
  S: ScWorld,
{
  build_graph8_loop(s, &History::new(), c0)
}

// prune_graph8

/*
function prune_graph8_loop(w, h, l::Empty8)
    C = conf_type(w)
    Empty{C}()
end

function prune_graph8_loop(w, h, l::Stop8)
    C = conf_type(w)
    Stop{C}(l.c)
end

function prune_graph8_loop(w, h, l::Build8)
    C = conf_type(w)
    if is_dangerous(w, h)
        Empty{C}()
    else
        lss = [[prune_graph8_loop(w, cons(l.c, h), l1) for l1 in ls]
               for ls in l.lss]
        Build{C}(l.c, lss)
    end
end
*/

fn prune_graph8_loop<S>(
  s: &S,
  h: &History<S::C>,
  l: &Rc<LazyGraph8<S::C>>,
) -> Rc<LazyGraph<S::C>>
where
  S: ScWorld,
{
  match &**l {
    Empty8() => empty(),
    Stop8(c) => stop(c),
    Build8(c, l8ss) => {
      if s.is_dangerous(h) {
        empty()
      } else {
        let h1 = h.cons(c.clone());
        let lss = vec_map!(vec_map!(prune_graph8_loop(s, &h1, &l1); l1 in ls);
                    ls in (*l8ss).clone());
        build(&c, &lss)
      }
    }
  }
}

/*
function prune_graph8(w, l0)
    C = conf_type(w)
    prune_graph8_loop(w, nil(C), l0)
end
*/

pub fn prune_graph8<S>(
  s: &S,
  l0: &Rc<LazyGraph8<S::C>>,
) -> Rc<LazyGraph<S::C>>
where
  S: ScWorld,
{
  prune_graph8_loop(s, &History::new(), l0)
}

//
// Now that we have decomposed `lazy_mrsc`
//     lazy_mrsc ≗ prune_graph8 ∘ build_graph8
// we can push some cleaners over `prune_graph8`.
//
// Suppose `clean∞` is a graph8 cleaner such that
//     clean ∘ prune_graph8 ≗ prune_graph8 ∘ clean∞
// then
//     clean ∘ lazy_mrsc ≗
//       clean ∘ (prune_graph8 ∘ build_graph8) ≗
//       (prune_graph8 ∘ clean∞) ∘ build_graph8
//       prune_graph8 ∘ (clean∞ ∘ build_graph8)
//
// The good thing is that `build_graph8` and `clean∞` work in a lazy way,
// generating subtrees by demand. Hence, evaluating
//     unroll( prune-graph8 ∘ (clean∞ (build-graph8 c)) )
// may be less time and space consuming than evaluating
//     unroll( clean (lazy-mrsc c) )
//

// cl8_bad_conf

/*
function cl8_bad_conf(bad, l::Empty8{C})::LazyGraph8{C} where {C}
    l
end

function cl8_bad_conf(bad, l::Stop8{C})::LazyGraph8{C} where {C}
    bad(l.c) ? Empty8{C}() : l
end

function cl8_bad_conf(bad, l::Build8{C})::LazyGraph8{C} where {C}
    if bad(l.c)
        Empty8{C}()
    else
        function lss()
            [[cl8_bad_conf(bad, l1) for l1 in ls] for ls in get_lss(l)]
        end
        Build8{C}(l.c, lss)
    end
end
*/

fn cl8_bad_conf<C : 'static + Clone>(
    bad: fn(&C) -> bool,
    l: &'static Rc<LazyGraph8<C>>,
) -> Rc<LazyGraph8<C>>
{
    match &**l {
        Empty8() => empty8(),
        Stop8(c) => {
            if bad(c) {
                empty8()
            } else {
                stop8(c)
            }
        }
        Build8(c, l8ss) => {
            let l8ss1: Rc<Lazy<Vec<L8s<C>>>> = Rc::new(lazy!(
                vec_map!(vec_map!(cl8_bad_conf(bad, &l1); l1 in ls);
                    ls in *l8ss)
            ));
            build8(&c, &l8ss1)
        }
    }
}

/*
cl8_bad_conf(bad) = l -> cl8_bad_conf(bad, l)
*/

//
// A graph8 can be cleaned to remove some empty alternatives.
//
// Note that the cleaning is not perfect, because `cl8_empty` has to pass
// the productivity check.
// So, `build(c, [])` is not (recursively) replaced with `Empty8()`. as is done
// by `cl_empty`.
//

// cl8_empty

/*
cl8_empty(l::Empty{C}) where {C} = l
cl8_empty(l::Stop{C}) where {C} = l

function cl8_empty(l::Build8{C})::LazyGraph{C} where {C}
    function lss()
        lss1 = [[cl8_empty(l1) for l1 in ls] for ls in get_lss(l)]
        [ls for ls in lss1 if !(Empty8{C}() in ls)]
    end
    Build8{C}(l.c, lss)
end
*/

/*
pub fn cl8_empty<S>(
    s: &'static S,
    l: &LazyGraph8<S::C>,
) -> Rc<LazyGraph<S::C>>
where
    S: ScWorld,
{
    match l {
        Empty8() => empty(),
        Stop8(c) => empty(),
        Build8(c, l8ss) => {
            let l8ss1 = [[cl8_empty(l1); l1 in ls] for ls in get_lss(l)];
            let l8lss2 = [ls for ls in lss1 if !(Empty8{C}() in ls)];
            build8(&c, &l8ss2)
        }
    }
}
*/

// An optimized version of `prune_graph8`.
// The difference is that empty subtrees are removed
// "on the fly".

// prune

/*
function prune_loop(w, h, ::Empty8)
    C = conf_type(w)
    Empty{C}()
end

function prune_loop(w, h, l::Stop8)
    C = conf_type(w)
    Stop{C}(l.c)
end

function prune_loop(w, h, l::Build8)
    C = conf_type(w)
    if is_dangerous(w, h)
        return Empty{C}()
    else
        lss1 = [ls for ls in get_lss(l) if !(Empty8{C}() in ls)]
        lss2 = [[prune_loop(w, cons(l.c, h), l1) for l1 in ls]
                for ls in lss1]
        return Build{C}(l.c, lss2)
    end
end
*/

/*
function prune(w, l0)
    C = conf_type(w)
    prune_loop(w, nil(C), l0)
end
*/

#[cfg(test)]
mod tests {
  use super::*;
}
