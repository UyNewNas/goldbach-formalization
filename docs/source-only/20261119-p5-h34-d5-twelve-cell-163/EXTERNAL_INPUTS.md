# P5.6 / h34 external input boundary

No new external theorem, axiom or PNT/Mertens/BV implementation was introduced.

Reused: fixed-version mathlib interval integral additivity and monotonicity; existing `RationalLogCertificate.check_sound`; fixed manuscript-local D5 geometry `P2EnhancedSeedD5PlusGeometry`, log-Fubini `P2EnhancedSeedD5PlusLogFubini`, and prior `Part5OriginalH430FourCellD5Darboux.first_cell/second_cell` with only the private visibility modifier removed. The exactly stated existing consumers are unchanged and their proofs are not independently replayed here. Toolchain remains `leanprover/lean4:v4.33.0-rc1`.

Still manuscript-INTERNAL: frozen analytic intercept application, original PP/same-rho objects, full selected-count mapping, root/owner weights, double-table seed, all-action closed-cell induction, native-history, integral–Theta–count and common 430+11 nested refinement. Those remain open and are not relabelled external inputs. All source-only proof dependencies and finite guards remain UNCOMPILED/UNEVALUATED.
