// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Four-point boolean domain for Task 1.
//!
//! ```text
//! Bool4  = Bottom | False | True | Top
//! values = Bottom {}, False {false}, True {true}, Top {false, true}
//! ```
//!
//! `Top` is the running example's unknown. `Bottom` is impossible: it contains
//! no boolean, so a later guard must not treat it as a license. Comparison
//! transfers and backward narrowing are a separate piece of work; this module
//! is only the lattice and the boolean operations.

use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Bool4 {
    Bottom,
    False,
    True,
    Top,
}

impl Bool4 {
    #[inline]
    pub fn bottom() -> (r: Bool4)
        ensures
            r == Bool4::Bottom,
            forall|b: bool| #![auto] !r.has(b),
    {
        Bool4::Bottom
    }

    #[inline]
    pub fn top() -> (r: Bool4)
        ensures
            r == Bool4::Top,
            forall|b: bool| #![auto] r.has(b),
    {
        Bool4::Top
    }

    #[inline]
    pub fn constant(value: bool) -> (r: Bool4)
        ensures
            r == if value { Bool4::True } else { Bool4::False },
            forall|b: bool| #![auto] r.has(b) <==> b == value,
    {
        if value { Bool4::True } else { Bool4::False }
    }

    pub open spec fn has(self, b: bool) -> bool {
        match self {
            Bool4::Bottom => false,
            Bool4::False => b == false,
            Bool4::True => b == true,
            Bool4::Top => true,
        }
    }

    pub open spec fn refines(self, other: Bool4) -> bool {
        forall|b: bool| self.has(b) ==> other.has(b)
    }

    pub fn contains(self, b: bool) -> (r: bool)
        ensures
            r == self.has(b),
    {
        match self {
            Bool4::Bottom => false,
            Bool4::False => b == false,
            Bool4::True => b == true,
            Bool4::Top => true,
        }
    }

    pub open spec fn join_spec(self, other: Bool4) -> Bool4 {
        match (self, other) {
            (Bool4::Top, _) | (_, Bool4::Top) => Bool4::Top,
            (Bool4::Bottom, x) => x,
            (x, Bool4::Bottom) => x,
            (Bool4::False, Bool4::False) => Bool4::False,
            (Bool4::True, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::True) | (Bool4::True, Bool4::False) => Bool4::Top,
        }
    }

    pub open spec fn meet_spec(self, other: Bool4) -> Bool4 {
        match (self, other) {
            (Bool4::Bottom, _) | (_, Bool4::Bottom) => Bool4::Bottom,
            (Bool4::Top, x) => x,
            (x, Bool4::Top) => x,
            (Bool4::False, Bool4::False) => Bool4::False,
            (Bool4::True, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::True) | (Bool4::True, Bool4::False) => Bool4::Bottom,
        }
    }

    pub open spec fn not_spec(self) -> Bool4 {
        match self {
            Bool4::Bottom => Bool4::Bottom,
            Bool4::False => Bool4::True,
            Bool4::True => Bool4::False,
            Bool4::Top => Bool4::Top,
        }
    }

    pub open spec fn and_spec(self, other: Bool4) -> Bool4 {
        match (self, other) {
            (Bool4::Bottom, _) | (_, Bool4::Bottom) => Bool4::Bottom,
            (Bool4::False, _) | (_, Bool4::False) => Bool4::False,
            (Bool4::True, Bool4::True) => Bool4::True,
            (Bool4::True, Bool4::Top) | (Bool4::Top, Bool4::True) | (Bool4::Top, Bool4::Top) => Bool4::Top,
        }
    }

    pub open spec fn or_spec(self, other: Bool4) -> Bool4 {
        match (self, other) {
            (Bool4::Bottom, _) | (_, Bool4::Bottom) => Bool4::Bottom,
            (Bool4::True, _) | (_, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::False) => Bool4::False,
            (Bool4::False, Bool4::Top) | (Bool4::Top, Bool4::False) | (Bool4::Top, Bool4::Top) => Bool4::Top,
        }
    }

    pub fn join(self, other: Bool4) -> (r: Bool4)
        ensures
            r == self.join_spec(other),
            forall|b: bool| self.has(b) ==> r.has(b),
            forall|b: bool| other.has(b) ==> r.has(b),
    {
        let r = match (self, other) {
            (Bool4::Top, _) | (_, Bool4::Top) => Bool4::Top,
            (Bool4::Bottom, x) => x,
            (x, Bool4::Bottom) => x,
            (Bool4::False, Bool4::False) => Bool4::False,
            (Bool4::True, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::True) | (Bool4::True, Bool4::False) => Bool4::Top,
        };
        r
    }

    pub fn meet(self, other: Bool4) -> (r: Bool4)
        ensures
            r == self.meet_spec(other),
            forall|b: bool| r.has(b) ==> self.has(b) && other.has(b),
            forall|b: bool| self.has(b) && other.has(b) ==> r.has(b),
    {
        match (self, other) {
            (Bool4::Bottom, _) | (_, Bool4::Bottom) => Bool4::Bottom,
            (Bool4::Top, x) => x,
            (x, Bool4::Top) => x,
            (Bool4::False, Bool4::False) => Bool4::False,
            (Bool4::True, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::True) | (Bool4::True, Bool4::False) => Bool4::Bottom,
        }
    }

    pub fn not(self) -> (r: Bool4)
        ensures
            r == self.not_spec(),
            forall|b: bool| self.has(b) ==> r.has(!b),
    {
        match self {
            Bool4::Bottom => Bool4::Bottom,
            Bool4::False => Bool4::True,
            Bool4::True => Bool4::False,
            Bool4::Top => Bool4::Top,
        }
    }

    pub fn and(self, other: Bool4) -> (r: Bool4)
        ensures
            r == self.and_spec(other),
            forall|x: bool, y: bool| self.has(x) && other.has(y) ==> r.has(x && y),
    {
        match (self, other) {
            (Bool4::Bottom, _) | (_, Bool4::Bottom) => Bool4::Bottom,
            (Bool4::False, _) | (_, Bool4::False) => Bool4::False,
            (Bool4::True, Bool4::True) => Bool4::True,
            (Bool4::True, Bool4::Top) | (Bool4::Top, Bool4::True) | (Bool4::Top, Bool4::Top) => Bool4::Top,
        }
    }

    pub fn or(self, other: Bool4) -> (r: Bool4)
        ensures
            r == self.or_spec(other),
            forall|x: bool, y: bool| self.has(x) && other.has(y) ==> r.has(x || y),
    {
        match (self, other) {
            (Bool4::Bottom, _) | (_, Bool4::Bottom) => Bool4::Bottom,
            (Bool4::True, _) | (_, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::False) => Bool4::False,
            (Bool4::False, Bool4::Top) | (Bool4::Top, Bool4::False) | (Bool4::Top, Bool4::Top) => Bool4::Top,
        }
    }
}

pub proof fn join_idempotent(a: Bool4)
    ensures
        a.join_spec(a) == a,
{
}

pub proof fn join_comm(a: Bool4, b: Bool4)
    ensures
        a.join_spec(b) == b.join_spec(a),
{
}

pub proof fn join_assoc(a: Bool4, b: Bool4, c: Bool4)
    ensures
        a.join_spec(b).join_spec(c) == a.join_spec(b.join_spec(c)),
{
}

pub proof fn join_bottom(a: Bool4)
    ensures
        a.join_spec(Bool4::Bottom) == a,
{
}

pub proof fn join_top(a: Bool4)
    ensures
        a.join_spec(Bool4::Top) == Bool4::Top,
{
}

pub proof fn meet_idempotent(a: Bool4)
    ensures
        a.meet_spec(a) == a,
{
}

pub proof fn meet_comm(a: Bool4, b: Bool4)
    ensures
        a.meet_spec(b) == b.meet_spec(a),
{
}

pub proof fn meet_assoc(a: Bool4, b: Bool4, c: Bool4)
    ensures
        a.meet_spec(b).meet_spec(c) == a.meet_spec(b.meet_spec(c)),
{
}

pub proof fn meet_top(a: Bool4)
    ensures
        a.meet_spec(Bool4::Top) == a,
{
}

pub proof fn meet_bottom(a: Bool4)
    ensures
        a.meet_spec(Bool4::Bottom) == Bool4::Bottom,
{
}

proof fn lemma_refines_cases(a: Bool4, b: Bool4)
    requires
        a.refines(b),
    ensures
        a == Bool4::Bottom || (a == Bool4::False && (b == Bool4::False || b == Bool4::Top)) || (a
            == Bool4::True && (b == Bool4::True || b == Bool4::Top)) || (a == Bool4::Top && b
            == Bool4::Top),
{
    match (a, b) {
        (Bool4::Bottom, _) => {},
        (Bool4::False, Bool4::False) | (Bool4::False, Bool4::Top) => {},
        (Bool4::True, Bool4::True) | (Bool4::True, Bool4::Top) => {},
        (Bool4::Top, Bool4::Top) => {},
        (Bool4::False, Bool4::Bottom) | (Bool4::False, Bool4::True) => {
            assert(a.has(false) && !b.has(false));
        },
        (Bool4::True, Bool4::Bottom) | (Bool4::True, Bool4::False) => {
            assert(a.has(true) && !b.has(true));
        },
        (Bool4::Top, Bool4::Bottom) | (Bool4::Top, Bool4::False) => {
            assert(a.has(true) && !b.has(true));
        },
        (Bool4::Top, Bool4::True) => {
            assert(a.has(false) && !b.has(false));
        },
    }
}

pub proof fn not_monotone(a: Bool4, b: Bool4)
    requires
        a.refines(b),
    ensures
        a.not_spec().refines(b.not_spec()),
{
    lemma_refines_cases(a, b);
}

pub proof fn and_monotone(a: Bool4, b: Bool4, c: Bool4)
    requires
        a.refines(b),
    ensures
        a.and_spec(c).refines(b.and_spec(c)),
{
    lemma_refines_cases(a, b);
}

pub proof fn or_monotone(a: Bool4, b: Bool4, c: Bool4)
    requires
        a.refines(b),
    ensures
        a.or_spec(c).refines(b.or_spec(c)),
{
    lemma_refines_cases(a, b);
}

} // verus!
