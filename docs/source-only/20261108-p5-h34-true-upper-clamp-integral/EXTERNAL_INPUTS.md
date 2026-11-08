# P5.6 → h34 — external input register: true U3/U4 upper H430 clamp integral

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766` / `paper/source/manuscript-body.tex` (blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).
Source commit: `51a1e0f9b325e85cb14b3291286514e6af679f8f`.

**New external number-theory inputs: NONE.** This packet introduces no new PNT, Mertens, BV, PP/same-rho or Buchstab classical theorem. No external theorem is reconstructed.

Existing dependencies used at this exact call site: `ImbalancedChen.Part5OriginalH430TrueUpperU34Phase` (source-only packet from `ee2072a`), its `u3_first_phase_true_H430`, `u3_middle_phase_true_H430`, `u3_clamped_phase_true_H430`, `u4_entire_phase_true_H430`, and the original `Part5OriginalU34H430Integrable.U3_eq_main_on_U4`. Mathematical support is the current pinned Mathlib real/rational arithmetic (`norm_num`, `linarith`, `nlinarith`), `setIntegral_congr_fun`, and `integral_const_mul`. Inherited source elaboration is not verified.

The actual original tagged U3/U4 selected-count, historical owner, z0, root weight and full/selected/inherited correspondence; original PP/same-rho compatibility; and the 430+11 common refinement remain manuscript-INTERNAL obligations, not external assumptions. Source only, no Lean compilation, kernel replay, transitive axiom audit or finite numerical430 replay. Numerical430: **UNEVALUATED**.
