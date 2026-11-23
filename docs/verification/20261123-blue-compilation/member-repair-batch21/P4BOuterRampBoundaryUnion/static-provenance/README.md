# BoundaryUnion: existing proof-body extraction

Status: **UNCOMPILED static source candidate**. No live source, pin, data,
build output, old inventory or manifest changed. No Lean/Lake/compiler/kernel/
type/axiom probe ran. The sole source owner must adopt and validate it.

Module: `ImbalancedChen.P4BOuterRampBoundaryUnion`.
Actual registered preimage SHA256:
`9567519840622b69609ba6a042f9e1e40b666fcdbc05e6e87e91ba7c7d0d5f1c`.
Candidate SHA256:
`c0d48d9ec2b1b77bf66a597a54a8950e9566c7ad17858bd1b43315d12466f03a`.

The extraction uses the already-existing inventory and patch:

* `/workspace/blue-member-four-commit-reuse-inventory-20261123.json`
* `48db3d60-P4BOuterRampBoundaryUnion.patch`, SHA256
  `f182d5944249f5251c9b5a862d7ef99ec0a76e0affcc84133da5b24114336890`.

The actual baseline exactly matches that patch's registered preimage. Its
published source authority is commit
`48db3d603d632bc60037e149a55717832e4c04be`, path
`ImbalancedChen/P4BOuterRampBoundaryUnion.lean`, blob
`430e605a85c22f0eea65a59c5c8728d6592c4089`, whole-file SHA256
`aed450cac730845f55f48042265b8bb7e95e82332f69940a71313d39bc251fe4`.

The whole published file changes imports and is not installed. This candidate
retains current `ActualUpperCountingInputs` and `P4BLogGateOuterRamp` imports
byte-for-byte. It copies only these four previously published proof bodies:

1. `exists_gate_strip_of_product_pos`: explicit original root `not_imp`
   and `exists_prop` simplifications.
2. `ramp_product_sub_strict_indicator_le_strip_union`: explicit original
   arithmetic-indicator summand in `Finset.single_le_sum`.
3. `finiteSourceMass_ramp_product_le_strict_card_add_strip_cards`: existing
   addition monotonicity applied to the correct side.
4. `finiteSourceMass_ramp_product_surplus_paid`: the same addition-side API
   normalization for the original paid strip bound.

Every copied body is byte-identical to its contiguous published source block.
`PROVENANCE.json` binds the complete headers, separate published/candidate body
hashes, source line and byte ranges, original inventory row, and original patch.
`published-reference/` contains the whole original published source for review;
`candidate/` retains the original current import family. No published theorem
proof was recreated or adapted. The other two source-owner reuse modules are
outside this candidate package and were not edited.

All ten public theorem headers, hypotheses, constants, quantifiers and every
byte outside the four proof implementations remain unchanged. The module has
no local definitions; imported definitions remain governed by the unchanged
current imports. No header exception or mathematical gap was identified.

The strict gate and literal arithmetic strip `-width < G_i ≤ 0` retain both
their boundary conventions, including the zero wall. Empty gate families are
still covered. The same natural carrier, cutoffs and finite ramp product are
used. The `hpaid` arithmetic strip-cardinality estimate remains an explicit
premise; no null-wall, volume, continuity or asymptotic estimate replaces it.
The eventual real-source adapter retains the original order of delta, target,
and evenness quantifiers. This is the same finite geometric-to-arithmetic
payment used with the smooth approximations and boundary payment in Nov6
`argument.tex:601–621`, with no additional analytic licence.

The next step belongs to the sole owner: recheck the current preimage and
perform the standard guarded normal/kernel/all-public validation. The existing
inventory itself claims no compiled-object or current-runtime qualification,
and neither does this extraction.
