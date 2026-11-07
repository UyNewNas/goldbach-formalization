# P5.6/h34 — external inputs recorded only (fixed-Q slot injection)

Prior head: 588122f6848b049fc1a610db6fd7d1a2f27c7473.
Mathematical source commit: fd45bcf10bda501e0564144495bced3765c7ebcc.
Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766,
paper/source/manuscript-body.tex, blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79.
Lean: v4.33.0-rc1. Mathlib: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

## Newly required genuinely external analytic inputs: NONE

No PNT, Mertens, BV, Rosser, Buchstab or other external theorem was
proved, reformulated, assumed, or instantiated in a stronger form.

## Precisely reused existing interfaces

- Previous source-only manuscript-local
  observed_slot_has_actual_rank_two_position from
  Part5OriginalH430PhysicalSlotListPositions: from membership in
  observedPhysicalSlots gives a Fin-bounded index in the actual
  firstExitDepthFrontier 2 LIST with the [ell,p] prefix, at the slot's
  original physical Q. Here an actual filter proves slot.1 = fixed Q.
  This earlier theorem is NOT compiled or independently verified.
- Finset.mem_filter from pinned Mathlib obtains both original source
  membership and fixed-Q equality. Used in
  observed_fixed_q_slot_has_position and the injectivity proof.
- Classical.choose / Classical.choose_spec and List.cons.inj from pinned
  Lean/Mathlib choose a genuine Fin index and recover both prime
  coordinates from equal prefixes. These are FINITE logical operations,
  not proof-escape axioms or an analytic number theory assumption.
- Fintype.card_le_of_injective and the finite-type cardinality simp
  in pinned Mathlib yield the per-Q count bound in
  observed_fixed_q_slots_card_le_frontier_length.

## Still manuscript-internal, NOT outsourced

Post full/selected/inherited position survival; original U3/U4 root
weights and q/tag owner multiplicities; cutoff/retention/no-factor
rejection; signed Euler payments; request-level all-action CLOSED-CELL,
base/seed/floor and feedback-integral/Theta/count; manuscript PP/same-rho;
native-history mass; and the genuine common nested causal 430+11
refinement remain OPEN. One finite slot per observed prefix is not
one paid receipt. Numerical certificates remain UNEVALUATED.
