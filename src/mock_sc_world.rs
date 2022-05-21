use crate::big_step_sc::*;
use crate::misc::*;

fn drive(c: &isize) -> Vec<Vec<isize>> {
    if c < &2 {
        vec![]
    } else {
        vec![vec![0, c - 1], vec![c - 1]]
    }
}

fn rebuild(c: &isize) -> Vec<Vec<isize>> {
    vec![vec![c + 1]]
}

impl ScWorld<isize> for isize {
    fn is_dangerous(&self, h: &History<isize>) -> bool {
        h.length() > 3
    }

    fn is_foldable_to(&self, c1: &isize, c2: &isize) -> bool {
        c1 == c2
    }

    fn develop(&self, c: &isize) -> Vec<Vec<isize>> {
        [drive(c), rebuild(c)].concat()
    }
}
