//
// Counting without generation
//
//
// The main idea of staged supercompilation consists in
// replacing the analysis of residual graphs with the analysis
// of the program that generates the graphs.
//
// Gathering statistics about graphs is just a special case of
// such analysis. For example, it is possible to count the number of
// residual graphs that would be produced without actually generating
// the graphs.
//
// Technically, we can define a function `length_unroll(c)` that analyses
// lazy graphs such that
//   length_unroll(l) == length(unroll(l))

use crate::graph::*;

use LazyGraph::*;

pub fn length_unroll<C>(l: &LazyGraph<C>) -> usize {
    match &*l {
        Empty() => 0,
        Stop(_) => 1,
        Build(_, lss) => {
            let mut s = 0;
            for ls in lss {
                let mut m = 1;
                for l1 in ls {
                    m *= length_unroll(l1);
                }
                s += m;
            }
            s
        }
    }
}

//
// Counting nodes in collections of graphs
//
// Let us find a function `size_unroll(l)`, such that
//   size_unroll(l) == (unroll(l).length , unroll(l).map(graph_size).sum)
//

pub fn size_unroll<C>(l: &LazyGraph<C>) -> (usize, usize) {
    match &*l {
        Empty() => (0, 0),
        Stop(_) => (1, 1),
        Build(_, lss) => {
            let mut k = 0;
            let mut n = 0;
            for ls in lss {
                let (k1, n1) = size_unroll_ls(&ls);
                (k, n) = (k + k1, n + k1 + n1);
            }
            (k, n)
        }
    }
}

fn size_unroll_ls<C>(ls: &Ls<C>) -> (usize, usize) {
    let mut k = 1;
    let mut n = 0;
    for l in ls {
        let (k1, n1) = size_unroll(l);
        (k, n) = (k * k1, k * n1 + k1 * n);
    }
    (k, n)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::big_step_sc::*;
    use iter_comprehensions::sum;
    use std::rc::Rc;

    fn lazy_mrsc_isize(c: isize) -> Rc<LazyGraph<isize>> {
        lazy_mrsc(&0isize, c)
    }

    #[test]
    fn test_statistics_length_unroll() {
        let l = lazy_mrsc_isize(0isize);
        let gs = unroll(&l);

        assert_eq!(length_unroll(&l), gs.len());
        assert_eq!(
            size_unroll(&l),
            (gs.len(), (sum!(graph_size(&g); g in gs)))
        );
    }
}
