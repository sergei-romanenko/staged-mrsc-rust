use crate::counters::*;

use crate::counter_system;
use std::fmt::Debug;

counter_system! {
    Synapse(i, d, v);
    Start(ω, 0, 0);
    Unsafe((d >= 1 && v >= 1) || (d >= 2));
    Rules {
        i >= 1 => i + d - 1, 0, v + 1;
        v >= 1 => i + d + v - 1, 1, 0;
        i >= 1 => i + d + v - 1, 1, 0;
    }
}

counter_system! {
    MSI(i, m, s);
    Start(ω, 0, 0);
    Unsafe(m >= 1 && s >= 1 || m >= 2);
    Rules {
        i >= 1 => i + m + s - 1, 1, 0;
        s >= 1 => i + m + s - 1, 1, 0;
        i >= 1 => i - 1, 0, m + s + 1;
    }
}

counter_system! {
    MOSI(i, o, s, m);
    Start(ω, 0, 0, 0);
    Unsafe(o >= 2 || m >= 2 || (s >= 1 && m >= 1));
    Rules {
        i >= 1 => i - 1, m + o, s + 1, 0;
        o >= 1 => i + o + s + m - 1, 0, 0, 1;
        // wI
        i >= 1 => i + o + s + m - 1, 0, 0, 1;
        // wS
        s >= 1 => i + o + s + m - 1, 0, 0, 1;
        // se
        s >= 1 => i + 1, o, s - 1, m;
        // wbm
        m >= 1 => i + 1, o, s, m - 1;
        // wbo
        o >= 1 => i + 1, o - 1, s, m;
    }
}

counter_system! {
    ReaderWriter(x2, x3, x4, x5, x6, x7);
    Start(1, 0, 0, ω, 0, 0);
    Unsafe(x3 >= 1 && x4 >= 1);
    Rules {
        // r1
        x2 >= 1 && x4 == 0 && x7 >= 1 =>
            x2 - 1, x3 + 1, 0, x5, x6, x7;
        // r2
        x2 >= 1 && x6 >= 1 =>
            x2, x3, x4 + 1, x5, x6 - 1, x7;
        // r3
        x3 >= 1 =>
            x2 + 1, x3 - 1, x4, x5 + 1, x6, x7;
        // r4
        x4 >= 1 =>
            x2, x3, x4 - 1, x5 + 1, x6, x7;
        // r5
        x5 >= 1 =>
            x2, x3, x4, x5 - 1, x6 + 1, x7;
        // r6
        x5 >= 1 =>
            x2, x3, x4, x5 - 1, x6, x7 + 1;
    }
}

counter_system! {
    MESI(i, e, s, m);
    Start(ω, 0, 0, 0);
    Unsafe(m >= 2 || (s >= 1 && m >= 1));
    Rules {
        i >= 1 => i - 1, 0, s + e + m + 1, 0;
        e >= 1 => i, e - 1, s, m + 1;
        s >= 1 => i + e + s + m - 1, 1, 0, 0;
        i >= 1 => i + e + s + m - 1, 1, 0, 0;
    }
}

counter_system! {
    MOESI(i, m, s, e, o);
    Start(ω, 0, 0, 0, 0);
    Unsafe(m >= 1 && (e + s + o) >= 1 || m >= 2 || e >= 2);
    Rules {
        // rm
        i >= 1 => i - 1, 0, s + e + 1, 0, o + m;
        // wh2
        e >= 1 => i, m + 1, s, e - 1, o;
        // wh3
        s + o >= 1 => i + m + s + e + o - 1, 0, 0, 1, 0;
        // wm
        i >= 1 => i + m + s + e + o - 1, 0, 0, 1, 0;
    }
}

counter_system! {
    Illinois(i, e, d, s);
    Start(ω, 0, 0, 0);
    Unsafe(d >= 1 && s >= 1 || d >= 2);
    Rules {
        // r2
        i >= 1 && e == 0 && d == 0 && s == 0 =>
            i - 1, 1, 0, 0;
        // r3
        i >= 1 && d >= 1 =>
            i - 1, e, d - 1, s + 2;
        // r4
        i >= 1 && s + e >= 1 =>
            i - 1, 0, d, s + e + 1;
        // r6
        e >= 1 =>
            i, e - 1, d + 1, s;
        // r7
        s >= 1 =>
            i + s - 1, e, d + 1, 0;
        // r8
        i >= 1 =>
            i + e + d + s - 1, 0, 1, 0;
        // r9
        d >= 1 =>
            i + 1, e, d - 1, s;
        // r10
        s >= 1 =>
            i + 1, e, d, s - 1;
        // r11
        e >= 1 =>
            i + 1, e - 1, d, s;
    }
}

counter_system! {
    Berkley(i, n, u, e);
    Start(ω, 0, 0, 0);
    Unsafe(e >= 1 && u + n >= 1 || e >= 2);
    Rules {
        // rm
        i >= 1 => i - 1, n + e, u + 1, 0;
        // wm
        i >= 1 => i + n + u + e - 1, 0, 0, 1;
        // wh1
        n + u >= 1 => i + n + u - 1, 0, 0, e + 1;
    }
}

counter_system! {
    Firefly(i, e, s, d);
    Start(ω, 0, 0, 0);
    Unsafe(d >= 1 && s + e >= 1 || e >= 2 || d >= 2);
    Rules {
        // rm1
        i >= 1 && d == 0 && s == 0 && e == 0 =>
            i - 1, 1, 0, 0;
        // rm2
        i >= 1 && d >= 1 =>
            i - 1, e, s + 2, d - 1;
        // rm3
        i >= 1 && s + e >= 1 =>
            i - 1, 0, s + e + 1, d;
        // wh2
        e >= 1 =>
            i, e - 1, s, d + 1;
        // wh3
        s == 1 =>
            i, e + 1, 0, d;
        // wm
        i >= 1 =>
            i + e + d + s - 1, 0, 0, 1;
    }
}

counter_system! {
    DataRace(out, cs, scs);
    Start(ω, 0, 0);
    Unsafe(cs >= 1 && scs >= 1);
    Rules {
        // 1
        out >= 1 && cs == 0 && scs == 0 =>
            out - 1, 1, 0;
        // 2
        out >= 1 && cs == 0 =>
            out - 1, 0, scs + 1;
        // 3
        cs >= 1 =>
            out + 1, cs - 1, scs;
        // 4
        scs >= 1 =>
            out + 1, cs, scs - 1;
    }
}

counter_system! {
    Futurebus(i, s_u, e_u, e_m, p_r, p_w, p_emr, p_emw, p_su);
    Start(ω, 0, 0, 0, 0, 0, 0, 0, 0);
    Unsafe(
        (s_u >= 1 && e_u + e_m >= 1) ||
        (e_u + e_m >= 2) ||
        (p_r >= 1 && p_w >= 1) ||
        (p_w >= 2));
    Rules {
        // r2
        i >= 1 && p_w == 0 =>
            i - 1, 0, 0, 0, p_r + 1, p_w, p_emr + e_m, p_emw, p_su + s_u + e_u;
        // r3
        p_emr >= 1 =>
            i, s_u + p_r + 1, e_u, e_m, 0, p_w, p_emr - 1, p_emw, p_su;
        // r4
        p_su >= 1 =>
            i, s_u + p_r + p_su, e_u, e_m, 0, p_w, p_emr, p_emw, 0;
        // r5
        p_r >= 2 && p_su == 0 && p_emr == 0 =>
            i, s_u + p_r, e_u, e_m, 0, p_w, 0, p_emw, 0;
        // r6
        p_r == 1 && p_su == 0 && p_emr == 0 =>
            i, s_u, e_u + 1, e_m, 0, p_w, 0, p_emw, 0;
        // wm1
        i >= 1 && p_w == 0 =>
            i + e_u + s_u + p_su + p_r + p_emr - 1, 0, 0, 0, 0, 1, 0, p_emw + e_m, 0;
        // wm2
        p_emw >= 1 =>
            i + 1, s_u, e_u, e_m + p_w, p_r, 0, p_emr, p_emw - 1, p_su;
        // wm3
        p_emw == 0 =>
            i, s_u, e_u, e_m + p_w, p_r, 0, p_emr, 0, p_su;
        // wh2
        e_u >= 1 =>
            i, s_u, e_u - 1, e_m + 1, p_r, p_w, p_emr, p_emw, p_su;
        // wh2
        s_u >= 1 =>
            i + s_u - 1, 0, e_u, e_m + 1, p_r, p_w, p_emr, p_emw, p_su;
    }
}

counter_system! {
    Xerox(i, sc, sd, d, e);
    Start(ω, 0, 0, 0, 0);
    Unsafe(d >= 1 && (e + sc + sd) >= 1 ||
           e >= 1 && (sc + sd) >= 1 ||
           d >= 2 ||
           e >= 2);

    Rules {
        // (1) rm1
        i >= 1 && d == 0 && sc == 0 && sd == 0 && e == 0 =>
            i - 1, 0, 0, 0, 1;
        // (2) rm2
        i >= 1 && d + sc + e + sd >= 1 =>
            i - 1, sc + e + 1, sd + d, 0, 0;
        // (3) wm1
        i >= 1 && d == 0 && sc == 0 && sd == 0 && e == 0 =>
            i - 1, 0, 0, 1, 0;
        // (4) wm2
        i >= 1 && d + sc + e + sd >= 1 =>
            i - 1, sc + e + 1 + (sd + d), sd, 0, 0;
        // (5) wh1
        d >= 1 =>
            i + 1, sc, sd, d - 1, e;
        // (6) wh2
        sc >= 1 =>
            i + 1, sc - 1, sd, d, e;
        // (7) wh3
        sd >= 1 =>
            i + 1, sc, sd - 1, d, e;
        // (8) wh4
        e >= 1 =>
            i + 1, sc, sd, d, e - 1;
    }
}

// -----

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
        run_min_sc(MSI, 3, 10);
        run_min_sc(MOSI, 3, 10);
        run_min_sc(ReaderWriter, 3, 5);
        run_min_sc(MESI, 3, 10);
        run_min_sc(MOESI, 3, 5);
        run_min_sc(Illinois, 3, 5);
        run_min_sc(Berkley, 3, 5);
        run_min_sc(Firefly, 3, 5);
        run_min_sc(DataRace, 3, 10);
        // Slow!
        // run_min_sc(Futurebus, 3, 5);
        run_min_sc(Xerox, 3, 5);
    }
}
