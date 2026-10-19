// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Executable checks for forward comparisons returning Bool4.

use semi_persistent_abstract_domains::bool4::Bool4;
use semi_persistent_abstract_domains::domains::d8::{
    ExecAnum, ExecTnum, ExecUnum, Interval, ReducedProduct,
};

fn interval(lo: u8, hi: u8) -> ReducedProduct {
    ReducedProduct {
        tnum: ExecTnum::top(),
        anum: ExecAnum::top(),
        interval: Interval { lo, hi },
        unum: ExecUnum::top(),
    }
}

fn with_tnum(tnum: ExecTnum) -> ReducedProduct {
    ReducedProduct {
        tnum,
        anum: ExecAnum::top(),
        interval: Interval { lo: 0, hi: 15 },
        unum: ExecUnum::top(),
    }
}

fn four_bit_tnums() -> Vec<ExecTnum> {
    let mut result = Vec::with_capacity(81);
    for mut code in 0u8..81 {
        let mut val = 0u8;
        let mut mask = 0u8;
        for bit in 0..4 {
            match code % 3 {
                0 => {}
                1 => val |= 1 << bit,
                2 => mask |= 1 << bit,
                _ => unreachable!(),
            }
            code /= 3;
        }
        result.push(ExecTnum { val, mask });
    }
    result
}

fn tnum_contains(tnum: ExecTnum, value: u8) -> bool {
    value & !tnum.mask == tnum.val
}

/// The abstraction of the concrete comparison results seen: hit[0] for false, hit[1] for true.
fn alpha(hit: [bool; 2]) -> Bool4 {
    match hit {
        [false, false] => Bool4::Bottom,
        [true, false] => Bool4::False,
        [false, true] => Bool4::True,
        [true, true] => Bool4::Top,
    }
}

fn assert_refines(narrower: Bool4, wider: Bool4) {
    for value in [false, true] {
        assert!(!narrower.contains(value) || wider.contains(value));
    }
}

#[test]
fn equality_and_inequality_use_singletons_and_disjointness() {
    let five = ReducedProduct::constant(5);
    let six = ReducedProduct::constant(6);
    let overlap = interval(4, 6);

    assert_eq!(five.eq(&five), Bool4::True);
    assert_eq!(five.ne(&five), Bool4::False);
    assert_eq!(five.eq(&six), Bool4::False);
    assert_eq!(five.ne(&six), Bool4::True);
    assert_eq!(five.eq(&overlap), Bool4::Top);
    assert_eq!(five.ne(&overlap), Bool4::Top);
}

#[test]
fn equality_detects_conflicting_known_tnum_bits() {
    let even = ReducedProduct {
        tnum: ExecTnum { val: 0, mask: 0xfe },
        anum: ExecAnum::top(),
        interval: Interval::top(),
        unum: ExecUnum::top(),
    };
    let odd = ReducedProduct {
        tnum: ExecTnum { val: 1, mask: 0xfe },
        anum: ExecAnum::top(),
        interval: Interval::top(),
        unum: ExecUnum::top(),
    };

    assert_eq!(even.eq(&odd), Bool4::False);
    assert_eq!(even.ne(&odd), Bool4::True);
}

#[test]
fn unsigned_less_than_uses_interval_endpoints() {
    assert_eq!(interval(0, 5).ult(&interval(6, 10)), Bool4::True);
    assert_eq!(interval(6, 10).ult(&interval(0, 5)), Bool4::False);
    assert_eq!(interval(0, 10).ult(&interval(5, 15)), Bool4::Top);
    assert_eq!(interval(0, 0).ult(&interval(1, u8::MAX)), Bool4::True);
    assert_eq!(
        interval(u8::MAX, u8::MAX).ult(&interval(0, u8::MAX)),
        Bool4::False
    );
}

#[test]
fn four_bit_interval_results_are_the_exact_comparisons() {
    for xlo in 0u8..=15 {
        for xhi in xlo..=15 {
            let x = interval(xlo, xhi);
            for ylo in 0u8..=15 {
                for yhi in ylo..=15 {
                    let y = interval(ylo, yhi);
                    let mut eq = [false; 2];
                    let mut ne = [false; 2];
                    let mut ult = [false; 2];
                    for xv in xlo..=xhi {
                        for yv in ylo..=yhi {
                            eq[(xv == yv) as usize] = true;
                            ne[(xv != yv) as usize] = true;
                            ult[(xv < yv) as usize] = true;
                        }
                    }
                    let case = format!("[{xlo}, {xhi}] vs [{ylo}, {yhi}]");
                    assert_eq!(x.eq(&y), alpha(eq), "eq {case}");
                    assert_eq!(x.ne(&y), alpha(ne), "ne {case}");
                    assert_eq!(x.ult(&y), alpha(ult), "ult {case}");
                }
            }
        }
    }
}

/// Unreduced inputs only need sound results: equal constant Tnums still carry
/// the interval [0, 15], so `eq` cannot see the singleton and returns `Top`.
/// After `reduce`, the interval is tightened and the results are exact.
#[test]
fn four_bit_tnum_results_match_the_concrete_oracle() {
    let tnums = four_bit_tnums();
    for left_tnum in &tnums {
        let left = with_tnum(*left_tnum);
        for right_tnum in &tnums {
            let right = with_tnum(*right_tnum);
            let mut eq = [false; 2];
            let mut ne = [false; 2];
            for left_value in 0u8..=15 {
                if !tnum_contains(*left_tnum, left_value) {
                    continue;
                }
                for right_value in 0u8..=15 {
                    if !tnum_contains(*right_tnum, right_value) {
                        continue;
                    }
                    eq[(left_value == right_value) as usize] = true;
                    ne[(left_value != right_value) as usize] = true;
                }
            }
            let case = format!(
                "tnum(val={:#06b}, mask={:#06b}) vs tnum(val={:#06b}, mask={:#06b})",
                left_tnum.val, left_tnum.mask, right_tnum.val, right_tnum.mask
            );
            assert_refines(alpha(eq), left.eq(&right));
            assert_refines(alpha(ne), left.ne(&right));
            let (left, right) = (left.reduce(), right.reduce());
            assert_eq!(left.eq(&right), alpha(eq), "reduced eq {case}");
            assert_eq!(left.ne(&right), alpha(ne), "reduced ne {case}");
        }
    }
}

#[test]
fn interval_comparisons_are_monotone_under_widening() {
    for left_lo in 0u8..=7 {
        for left_hi in left_lo..=7 {
            let left = interval(left_lo, left_hi);
            for wider_left_lo in 0u8..=left_lo {
                for wider_left_hi in left_hi..=7 {
                    let wider_left = interval(wider_left_lo, wider_left_hi);
                    for right_lo in 0u8..=7 {
                        for right_hi in right_lo..=7 {
                            let right = interval(right_lo, right_hi);
                            for wider_right_lo in 0u8..=right_lo {
                                for wider_right_hi in right_hi..=7 {
                                    let wider_right = interval(wider_right_lo, wider_right_hi);
                                    assert_refines(left.eq(&right), wider_left.eq(&wider_right));
                                    assert_refines(left.ne(&right), wider_left.ne(&wider_right));
                                    assert_refines(left.ult(&right), wider_left.ult(&wider_right));
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
