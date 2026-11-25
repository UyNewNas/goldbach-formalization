# Strict 03: ordinary six-tent mass and query normalization

## Actual failure and scope

P2 task `c2edcc3a270e4e2aabb7155f3b8bc0e0` compiled source `fcd0acba`
with the original strict checker. Its complete log is
`p2-strict-symbolic-03.log` (19,151 bytes; SHA-256
`3553e024808d4e959ba69b79575bc26a170604a7035e49a9e076d51b7d4f8205`).
The batch ended with 267 of 319 modules successful, including 264 reused
records; it did not complete the symbolic closure.

This repair changes only two proof sites in
`ImbalancedChen/ActualThirdOriginalSixTentOrdinaryMassCeil.lean`:

- At old line 96, `rw [heq] at hraw` could not match the two logarithms:
  `hraw` used `Fin.castSucc 0` and `Fin.castSucc 1`, whereas `heq` used
  the corresponding numeric indices in `Fin 3`.
- At old line 171, the final `simpa` left the rational-to-real cast of the
  denominator power in the NEW query, while the reader enclosure used the
  real power directly.

Both are expression-normalization failures. Neither exposes a missing mass
estimate, a new query-domain condition, or a changed strict/weak boundary.

## Original mathematical and reader semantics

The already frozen 1106 producer `certify_extended_prefix.py` was checked at
`density_mass`, `SieveTable.point`, and the relevant `mean_upper` branch.
Its SHA-256 is
`1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`;
the accompanying `numerical-appendix.tex` has SHA-256
`bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`.
Both come from frozen manuscript source
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`.

The ordinary mass still multiplies the two separate logarithmic widths and
the full rectangular z mass. The factor 4 is supplied once by `literalMassZ`;
the two logarithms retain the original 256-term, no-range-reduction branch.
The OLD endpoints still use their exact rational queries, and the NEW upper
query still uses the same reader at the unreduced pair
`((ordinaryNew a b).hi, P160)`. The zero clamp, its equality boundary, and the
terminal branch remain those proved by `query_encloses_all`.

The frozen 1106 producer supplies this semantic correspondence; it is not
claimed to be the separate P160 producer SHA cited in the module's historical
header. No historical producer or numerical data was reconstructed here.

## Minimal proof edits

The mass proof now rewrites the two concrete finite indices using their
explicit `rfl` equalities before applying the existing `heq`. This keeps both
coordinates in their original order and leaves all interval operations intact.

The query proof adds `Rat.cast_pow` and `Rat.cast_ofNat` to its existing
`simpa only` list. Unfolding `P160` and simplifying its integer cast can expose
`(2 : ℚ)^160` under the outer real cast; these rules normalize that remaining
cast to `(2 : ℝ)^160`. No query value, denominator, or enclosure inequality
changes.

## Checks and verification boundary

Static comparison against `fcd0acba` confirms byte-identical imports, all
seven public theorem headers, the one private theorem header, and both
complete computational definitions. `git diff --check` passes. No assumptions,
axioms, admitted proofs, native evaluation, or linter settings were added.
The original absence of a final newline is preserved.

Source SHA-256 before this repair:
`0aefb001448b56e64e227e71dfb71a84167b45ea309007d054102fe455b79eb5`.
Candidate SHA-256:
`6496f104ab08e8c3d177966f91f6d64c3850dff2c06de2b0fa31c851052b120d`.

This candidate has not been compiled. It carries no new compilation, kernel,
finite-check, or endpoint-completion credit. The existing strict batch was
allowed to finish its postcheck; no remote task or running P2 input was changed.
