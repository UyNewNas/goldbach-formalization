# P2.6: exact Cell05 prefix first moments and quantitative ranges

Base: `9f937603bac4ac23c93511971732610e20cc7595` on the existing P2.6
continuation branch. `P2_6_complete` remains false.

## Closed results

The new finite weighted-mean theorem preserves the original nine-vertex
normalization, including both the unweighted sum and gap-weighted sum, and
the division by ten. Applied to every Cell05 row and factor, it proves
`53/13824 ≤ mean ≤ top`. Thus every vertex deviation and the mean deviation
lies between zero and `1 - (53/13824)/top`, and that upper endpoint is
strictly less than one.

The existing `P2Winner9HomogeneousRecurrence` and Saving19 prefix interface
and evaluator are reused unchanged. Their degree-zero and degree-one
coefficients are proved equal to one and the sum of nodes. Consequently
the original `normalizedMoment` evaluator has exact closed formulas in
degrees zero and one.

A generic explicit encoding takes a common denominator equal to the product
of the rational entries' own denominators and proves the natural numerators
encode the actual nonnegative rationals exactly. This also proves the sum
of encoded gap weights is positive. No host-generated literals, stored
moment values, hash equality, or final floor premises are used.

For all 56 Cell05 rows and all ten factors, the existing prefix algorithm
on these exact encodings now has zeroth value one and first value
`1 - mean/top`. The latter value lies in the certified deviation interval.
These are closed statements about the original parser-bound coordinates.

## Verification

The seven targets passed seven fresh normal compilations (`--trust=0`,
warnings as errors), seven independent stock-kernel replays, and a complete
serialized-module/declaring-module inventory, full-type and transitive-axiom
audit. All 81 owned declarations passed: 22 + 3 + 3 + 3 + 6 + 29 + 15.
Only `propext`, `Classical.choice`, and `Quot.sound` occur.

`RUN.json` pins the 139-module project source/object closure and toolchain,
as well as the audit and reusable verifier source. The full raw audit and
declaration records are retained. `project-objects.tar.xz` contains exactly
those 139 project objects, checked member-by-member against `RUN.json`.
Lean is 4.33.0-rc1 and Mathlib is
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; dependencies were not updated.

```sh
python3 -B tools/p26/first-moment/verify.py
```

The reusable verifier now accepts a scope and audit path; its prior default
eight-target geometry-join workflow is preserved. Existing successful
receipts have not been overwritten or relabeled.

## Remaining boundary

This closes finite algorithmic normalization and first-value checks, not
an equality to real Lebesgue higher moments. The existing
`HigherMomentsPrefix` semantic connection still needs a matching accepted
analytic dependency closure in this environment. Original Cell05 stored
Q80 and new Q96 floor checks still require the exact missing original
moment-refinement bytes recorded in the preceding report. The full
13-cell/28,918-row certificate, ownership/coverage and integral endpoint
are not certified by this work. The MCP availability guardian remained
healthy during compilation and verification.
