# Strict 06: balanced symmetric mass and guard normalization

## Actual failure

The original P2 strict-symbolic-06 checker compiled proof source `a2dcc3fe`.
Its complete log, `p2-strict-symbolic-06.log`, is 13,454 bytes with SHA-256
`501f0a48515e5cae43d70408517a6d46cabc6c5c419b85d3cbe736e40cfc12f7`.
The batch completed in 147.225 seconds with 286 of 321 symbolic modules
successful: 283 reused records and 3 fresh passes. The closure remains open.

`ActualThirdOriginalP4ABalancedSymmetricLeaf.lean` failed at two sites:

- At old line 303, `divNat_sound` left the natural-number cast of 2 in the
  real denominator of `hraw`. The existing mass identity `heq` used the real
  literal 2, so `rw [heq]` did not match.
- At old line 344, the caller's branch hypothesis matched on `k`, while
  the supplier's elaborated hypothesis matched on `k` and its denominator
  binding proof. Simplifying the visible branch formula did not reconcile
  those dependent match expressions.

These are expression-normalization failures, not a missing integral bound
or a mathematical gap.

## Frozen manuscript and preserved mathematical scope

The frozen 1106 producer `certify_extended_prefix.py` has SHA-256
`1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`.
Its `density_mass` encloses the integral of `4/(x*y*z^2)` over the full
rectangle using two logarithmic widths and the exact rational z factor.
For an identical-interval symmetric square, `enclosure` restricts to the
ordered half and divides the lower mass endpoint downward and the upper
endpoint upward by 2. The frozen numerical appendix specifies the directed
arithmetic convention; its SHA-256 is
`bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`.

The Lean candidate keeps this half-mass operation tree, the original
256-term unit-log branch, all integer data and denominators, and the
balanced `xy`/`xyz` restriction. It adds no symmetry assumption or target
integral bound. Existing `symmetric_mass_formula` and the literal guard
bridge remain the mathematical suppliers.

## Minimal proof changes

Before the existing `rw [heq] at hraw`, one `simp only [Nat.cast_ofNat] at
hraw` normalizes the cast of 2. The mass identity itself is unchanged.

Each of the three branch/root/residual arguments now uses `cases k` and
then the original hypothesis by `exact`. The complete guard-supplier call
is byte-identical to the corresponding call in
`ActualThirdOriginalP4ASymmetricTentPrerequisites.lean` at `a2dcc3fe`, which
this same strict batch passed in 5.111 seconds. No premise is added.

The original log supplied a source-bound `unnecessarySeqFocus=false`
baseline exception. The candidate does not inherit that exception. The
two single-goal `field_simp ... <;> ring` sequences are written as successive
`field_simp` and `ring` tactics; the polynomial arguments are unchanged.
The remaining `<;>` sites split `Fin 2` or `TentSide` into two actual cases.
No linter setting or checker gate is modified.

## Static checks and verification boundary

Comparison against `a2dcc3fe` confirms that the entire diff consists only
of the specified proof replacements. All eight public theorem headers,
five private theorem headers, the complete `balancedSymmetricCost`
definition, and the one import remain byte-identical. `git diff --check`
passes. The unchanged public hypotheses preserve the original mathematical
boundary; no axiom, admitted proof, or alternative evaluation is introduced.

Original source SHA-256:
`0bc272d549f1048d2c7d90f03e2fc7bd18eebc0acb7a6992c80b714c45a85eb6`.

Frozen candidate SHA-256:
`826fefa3ab664173f091ddb7656ea85115840014166cff70fcca7e81a736d7b4`.

This candidate has not been compiled. Strict elaboration and lint remain
for root's next original-checker run; no compilation, kernel, finite-check,
or endpoint credit is claimed. No index, remote task, or running P2 input
was changed by this repair.
