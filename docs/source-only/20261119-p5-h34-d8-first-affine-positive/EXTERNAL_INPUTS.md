# P5.6 h34 external-input boundary — D8 first-affine packet

Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d.
Baseline GitHub head: ba479ca0075afd6900f09c7e8efc49dce95def9c.
No new external analytic input, axiom, or replacement interface is added.

Existing Mathlib real arithmetic, interval integrability, interval
monotonicity and logarithm inequalities are reused through the fixed
source import chain. Existing RationalLogCertificate.check_sound, original
P2EnhancedSeedPairD8Geometry.literal_geometry, original moving
supportLine, first_affine_piece, continuousOn_outerSlice and original
P2EnhancedSeedPairD8PieceSum are reused unchanged.

This packet implements only the manuscript-local D8 FIRST integral
comparison. The original second-affine 103/1000 bound cannot be added
to the new first-affine 1/200 bound because the former's public theorem
already denotes the complete D8 integral. A separately proven second-only
certificate and its exact gluing are required to improve D8 globally.

The incomplete original 430+11 all-action induction, U3/U4 counts,
root and owner weights, PP/same-rho, seed, intercept and native-history
connections remain INTERNAL. No external proof was attempted.
