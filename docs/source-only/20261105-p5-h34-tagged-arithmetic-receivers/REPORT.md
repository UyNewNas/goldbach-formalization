# P5.6 → h34 — tagged original arithmetic receiver inclusion

Date: 2026-11-05. Parent: `2f6299fea73f72455b4270a1641f53dda6df0a94`.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
State: **PARTIAL_SOURCE_INCREMENT; SOURCE_ONLY; UNCOMPILED; ZERO FORMAL CREDIT**.
Complete h34 manuscript-internal proof: **OPEN**.

## New manuscript-local source

`Part5OriginalH430TaggedArithmeticReceivers.lean`: 216 lines, 10 theorem declarations, 8 definitions (plus type abbreviations).

The previous source packet compared original U3/U4 counts with frozen
root counts. This packet exposes the *actual arithmetic occurrences*:
one tagged (U3 or U4, selected prime p, quotient-receiver prime q) per
original strict receiver. It does not interpret a root feedback mark
as that arithmetic multiplicity.

1. `originalBand` exactly reuses the two strict `chenSinglePrimeSelector`
   sets. `original_band_prime` and `original_band_geometry` discharge
   prime/coprime and frozen root-band conditions from the selectors
   themselves, with no new assumption.
2. `original_receiver_subset_frozen` proves pointwise containment of
   the SAME actual q, by the actual smaller frozen same-Q cutoff.
   `original_receiver_root_witness` simultaneously attaches the
   corresponding generated root's geometrical Coherent certificate and
   its one literal history origin; it does NOT claim a bijection from
   q to that origin.
3. `TaggedPair` stores both p and q. `TaggedReceiver` adds an
   explicit U3/U4 sum tag. `original_tagged_card` and
   `original_U34_eq_tagged_card` intend to identify cardinality with
   the two original Upsilon counts, retaining overlap multiplicity.
4. `original_tagged_subset_frozen` lifts the pointwise same-p,same-q
   inclusion to the full literal tagged arithmetic source.
   `original_U34_le_frozen_tagged` then obtains the upper-cost bound
   from finite-cardinality monotonicity, not an invented count licence.
5. `frozenOnly` explicitly names the extra frozen-only receiver lane
   (frozen tagged source minus original tagged source). Its contribution
   is NOT assumed to vanish or to have been paid.

## Critical unfinished boundary

The *tagged arithmetic* receiver is not the generated feedback
`Occurrence` or `requestValue`. There are generally many q for the
one tagged root p, while its feedback root has mark 1. One must prove
actual selected-count ownership, full/selected/inherited filters,
rejection-lane payment, and a genuine arithmetic count induction
before making that identification.

Other internal tasks still open: base/fixed/switched/seed/floor,
PP/same-rho source instantiation, native-history weight and outer
Theta normalization, and one common causal 430+11 refinement.

No P1.4/P3.6, production files, pinned dependencies or CI were changed.
Genuinely external inputs are recorded separately, not implemented.

## Validation

Only textual delimiter, placeholder and Git-object checks were used.
No Lean parser/elaborator, kernel replay, transitive axiom audit,
numerical430 replay or independent review was run. Prior proofs
including this new finite set interpretation are UNEVALUATED.
This is not evidence that a Lean theorem compiled.

Next: identify actual tagged root (p,q) source occurrences with the
original selected/full/inherited owner+filter channels and the correct
receiver-to-feedback count recurrence, including the frozenOnly lane.
Do not map all q to one feedback origin injectively or use a new
target-equivalent counting assumption.
