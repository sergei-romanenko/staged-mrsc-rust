// Miscellaneous

use itertools::Itertools;
use iter_comprehensions::{vec as vec_map};

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

