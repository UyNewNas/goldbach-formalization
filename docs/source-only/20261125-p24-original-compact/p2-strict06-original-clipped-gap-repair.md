# Strict 06: original clipped-gap proof repair

Status: **SOURCE_REPAIR_PREPARED / FRESH_LEAN_CHECK_PENDING**.

The complete strict06 log for source `a2dcc3fe` is
`p2-strict-symbolic-06.log`, 13,454 bytes, SHA-256
`501f0a48515e5cae43d70408517a6d46cabc6c5c419b85d3cbe736e40cfc12f7`.
It reports 286/321 successful modules (283 reused, three fresh), no pending
modules and five direct failures. Only
`ActualThirdOriginalP4AOriginalClippedGapLeaf.lean` is repaired here.

## Original construction retained

The frozen 1106 `certify_extended_prefix.py` was checked at `enclosure`:
the outside-cell return, positive `cap_lo-x1-y1` assertion, signed `olo`,
`sa=max(2*z1,olo)`, nonnegative `delta=NT-cap_lo`, paired queries and final
nonnegative clipping. Its SHA-256 is
`1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`,
from manuscript source `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`.
The accompanying appendix retains the lower factor's zero extension at
arguments at most 2. This check is semantic correspondence, not a new
authentication of a separate historical P160 producer.

The Lean construction still allows signed `ao < 0`, uses
`start=max(2*z1,ao)`, and assumes only the original positive residual and
cap-floor conditions. Concavity is used on `[2,infinity)`; the OLD-at-most-2
branch uses the actual zero clamp. Integration remains on the full compact
intersection, including an empty intersection, with no nonempty premise.

## Actual errors

- **Input line 77:** the selected `add_le_add_right` produced the opposite
  summand order for the transitivity step. Use the explicit two-inequality
  `_root_.add_le_add` instead. The existing `hd` establishes
  `max 2 t <= 2+d`; monotonicity through this clamped argument completes the
  same bound. This also gives `hd` an explicit role without changing its
  public declaration or adding a hypothesis.
- **Input line 298:** the expected function type made the intersection
  request `Inter (Point -> Prop)`. Express the same a.e. inclusion as a
  membership implication under `volume : Measure BoxPoint`. Its proof is
  still the second component of membership in the intersection.

## Separate consequences of losing baseline style exceptions

The old source had baseline-only exceptions for unnecessary sequencing,
unused tactics/variables and unreachable tactics. No exception is carried
to the candidate. Three polynomial `field_simp`/`ring` proofs now run
sequentially. The paired-query fraction is split by `add_div` and its two
terms cancelled separately. Two scale-cancellation steps reuse the already
proved `producer_log_ratio`, removing trailing tactic risk. The lower raw
coordinate binding is used explicitly in the positivity transport; the
unused ambient `hi` parameter of the delta lemma is explicitly cleared in
the proof while preserving its public header. These are local static
repairs, not a claim that the candidate's strict lint has passed.

## Preservation and verification boundary

Comparison against `a2dcc3fe` confirms unchanged 12 public theorem headers,
three private headers, six complete computational definitions, imports and
options. `git diff --check` passes. No new hypothesis, admitted proof, axiom,
unsafe declaration, native evaluation or linter setting was added.

- Before SHA-256: `e3015da8ecd681698aafe946af1243d7d46f190624f0b6a16c4dd51e23d09aa4`.
- Candidate SHA-256: `9fa3ea4095fcebda6c803047b279cdafe6fb3e27e7e23385adcb862398135b03`.

No Lean compilation, remote task, index operation or commit was performed.
The candidate grants no new compilation, kernel, finite-check or endpoint
completion credit.
