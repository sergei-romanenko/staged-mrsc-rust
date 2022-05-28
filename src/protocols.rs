use crate::counters::*;

use crate::{nwc, counter_system, mk_r_params};
use std::fmt::Debug;

counter_system! {
    Name Synapse;
    Params(i, d, v);
    Start(ω, 0, 0);
    Unsafe((d >= 1 && v >= 1) || (d >= 2));
    Rules{
        i >= 1 => i + d - 1, 0, v + 1;
        v >= 1 => i + d + v - 1, 1, 0;
        i >= 1 => i + d + v - 1, 1, 0;
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::big_step_sc::*;
    use crate::graph::*;
    use crate::statistics::*;

    fn run_min_sc<CW: CountersWorld + Debug>(cw: CW, m: isize, d: usize) {
        let name = format!("{:?}", cw);
        print!("\n{} ", name);
        let s = CountersScWorld::new(cw, m, d);
        let l = lazy_mrsc(&s, CW::start());
        let sl = cl_empty_and_bad(CW::is_unsafe, &l);

        let (len_usl, size_usl) = size_unroll(&sl);
        println!("({}, {})", len_usl, size_usl);

        let ml = cl_min_size(&sl);
        let gs = unroll(&ml);
        if gs.len() == 0 {
            println!(": No solution")
        } else {
            let mg = gs[0].clone();
            println!("{}", graph_pretty_printer(&*mg));
        }
    }

    #[test]
    fn run_protocols() {
        run_min_sc(Synapse, 3, 10);
        // run_min_sc(MSI, 3, 10)
        // run_min_sc(MOSI, 3, 10)
        // run_min_sc(ReaderWriter, 3, 5)
        // run_min_sc(MESI, 3, 10)
        // run_min_sc(MOESI, 3, 5)
        // run_min_sc(Illinois, 3, 5)
        // run_min_sc(Berkley, 3, 5)
        // run_min_sc(Firefly, 3, 5)
        // run_min_sc(DataRace, 3, 10)
        // Slow!
        // run_min_sc(Futurebus, 3, 5)
        // run_min_sc(Xerox, 3, 5)
    }
}
