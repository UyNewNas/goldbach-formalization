# h34 external-input boundary

Scope: manuscript-internal proof generation only. External analytic results
are recorded/reused, not implemented. This packet introduces no axioms.

## Reused library and manuscript-local inputs

- Existing integer-division-to-real comparison:
  `Certificates.P2HistoricLogPointInterpreter.ediv_le_real`.
  It is invoked only for the candidate's outer quotient; this packet does not
  implement the logarithm backend imported through that existing module.
- Existing finite sums, real order/casts, nonnegative-integral facts, and
  elementary rational arithmetic from the pinned Mathlib closure.
- Existing local production W1/W2 suppliers and their transitive prime-profile,
  PNT/Mertens or distribution dependencies. Only their stated source interfaces
  are reused; their external analytic proofs are not expanded or newly audited.

## Not externalized

The complete original count-history construction, old-generation closed-cell
count invariant, numerical feedback quadrature/base comparisons, analytic seed
APPLICATION, manuscript PP/same-rho instances, and common430+11 refinement are
still manuscript-local obligations. The parameter `hcells` in the fixed-channel
induction lemma is not a supplied count licence and is not declared proved.

## Pinned source evidence

Base revision: def3f8c2a8418844e3ea230c2c7876e9917cc143.
`P2HistoricLogPointInterpreter.lean` blob483caca686cc7860bbd3d1e6e01523e725253c7a;
`Part5OriginalH430ImmutableBankProfiles.lean` blob05cc046cd35c74cc8a3e7da6e5df2e22d6ca814b;
literal point records blob6f0aeb88b8427c37144772fa5adca3a3d7aaf0c4.
The existing Lean/Mathlib/native-package pins are unchanged. Their complete
transitive axiom closure and availability were not independently checked by
compilation in this session. No additional external theorem is claimed verified.
