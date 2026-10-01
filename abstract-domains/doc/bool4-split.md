# Four-point boolean: split

Task 1's four-point boolean, from `interval-extensions.md` §2. Two people, two pieces. Piece A does not depend on intervals. Piece B uses the type from piece A and does not change its lattice.

## Piece A — the domain

Owner: implementation owner. Files: `src/bool4.rs`, `tests/bool4.rs`.

`Bool4 = Bottom | False | True | Top`.

| Value | Concrete booleans | Running example |
| --- | --- | --- |
| `Bottom` | none | impossible |
| `False` | `{false}` | false |
| `True` | `{true}` | true |
| `Top` | `{false, true}` | unknown |

Implement and prove:

- canonical `bottom`, `top`, and concrete-boolean `constant` constructors
- `has`, and `refines` as subset of `has`
- `join`, `meet`, `not`, `and`, `or`, each with containment: every concrete input's concrete result is in the abstract result
- §3.5 for `meet` and `join`: idempotent, commutative, associative, units, zeros
- monotonicity of `not`, `and`, and `or` in the refined argument

`meet(Top, True) = True` is the running example's `(union c (True))`. `meet(True, False) = Bottom`. Bottom contains neither boolean.

## Piece B — comparisons and backward narrowing

Owner: proof/test owner. Build on the Piece A API; do not start by editing `bool4.rs`.

Forward comparisons, result type `Bool4`:

- `eq` / `ne` from interval disjointness and singleton equality, plus conflicting known Tnum bits as a proof of inequality
- unsigned `<`, `<=`, `>`, `>=` from interval endpoints

Implemented in the multi-width `ReducedProduct`: `eq`, `ne`, and unsigned
`ult` (`<`). Their contracts contain every concrete comparison result for
represented inputs, and their comparison-specific refinement lemmas prove
monotonicity for nonempty `eq`/`ne` inputs and for all well-formed `ult`
inputs. The `d8` executable tests exhaust all interval pairs and all 81 Tnum
states over the embedded four-bit range, and cover zero and the machine
maximum.

Backward narrowing for a taken branch. For a true unsigned `x < y`, narrow with checked forms of `x.hi <= y.hi - 1` and `y.lo >= x.lo + 1`. An infeasible branch is `Bottom` or `None`, not an ordinary well-formed interval. Run the reduced-product reduction after the narrow.

Prove the acceptance criteria in §2: every concrete comparison of represented inputs is in the `Bool4` result; a backward step keeps every concrete pair that satisfies the branch and drops only pairs that violate it; zero and the machine maximum do not underflow or overflow; small-width tests enumerate forward and backward results against concrete values.
