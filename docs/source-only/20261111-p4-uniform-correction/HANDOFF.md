# P4 uniform same-rho correction, 2026-11-11 08:40 round

SOURCE ONLY / UNCOMPILED / NOT KERNEL ACCEPTED / NO STATUS PROMOTION.

## Exact source and reuse
Base: 3a46b3f0a4ee8ee7e628c9234717fae03064a52b.
Lean change commit: 146d512e549679a5b00e076176ac83da345a3436.
Branch: chatgpt/p4-uniform-correction-20261111.
Modified: ImbalancedChen/P4BRangeFreeActualCorrection.lean only; no workflow change.
Pinned toolchain leanprover/lean4:v4.33.0-rc1, mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, goldbach 09b97db5764ade1246bfb77206baa1b124760958; manifest unchanged.

Read existing All22 structural report, T09 yellow-scope verdict, and paused-round checkpoint. Original raw All22 already telescopes the actual final dispatcher; lowerEarlyDefect for slots 0/1/2 remains unsigned. Repeating that algebra would not pay it. Existing P4B actual hyperbola, active-range and range-free suppliers were inspected; no new prime bound, reciprocal tail or correction estimate was implemented. Old p4-upper branch is an October 13 checkpoint, not the current baseline. Existing P2 candidate 34aa0f58 and full87 work are not duplicated or modified.

The root CURRENT_MANUSCRIPT_MAP still describes October 10: this is not silently treated as the current whole-manuscript mapping. The frozen November 6 argument.tex was read directly (blob 90234d94460f1d7d59982635d7bf54c9b19250da). Its prop:current-positive-product and eq:current-coprime-correction require the same coefficient and negligible coprime-mean correction. This change is only the quantifier refinement needed when a common policy is chosen later; it does not claim the whole proposition.
Existing EXTERNAL_REUSE audit and fixed dependencies were read. The applicable result is already in this repository; its finite envelope constant is independent of the attachment precision, policy and cap. Thus the smallest adaptation is to lift those quantifiers through the existing proof, not to formalize external analytic results. External sources not directly accessed in this round remain unverified, not nonexistent.

## New export and mathematical derivation
P4BRangeFreeActualCorrection.eventually_actual_compact_smooth_correction_le_uniform_policy:
for a fixed ActualCompactSmoothFamily F, theta>0, nu>0, r>0 and tolerance>0,
eventually in N, for every even N, every epsilon with epsilon^2 <= r, every retain and cap, and every b in [b0,b1], the absolute actualSmoothOuterCorrection is at most tolerance * singularNormalization N.

The supplier C and scalar c=8*C*(nu*r+1)*(exp(F.width)+1), the power-growth threshold and power-log payment are all independent of epsilon, retain and cap. The introduction of these objects is moved after N and its eventual bounds. The finite supplier already permits precisely these choices. Its full-product support and floor/ceiling payment are reused verbatim.
The old eventually_actual_compact_smooth_correction_le keeps its exact name, parameter order and conclusion as a specialization wrapper. This preserves downstream callers.

## Eliminated / remaining
Eliminated at candidate-source level: dependence of the error threshold on a separately fixed retention policy, enumeration cap and legal attachment precision. A later common choice can consume one threshold without swapping rho.
Not eliminated: early slots 0/1/2 payment, same-policy All22 gain attachment, remaining density reserve, full hUpper, signed PP, or complete noncompact-family tail/integrability. F, theta, nu and r remain fixed before the threshold. No arbitrary noncompact family uniformity is asserted.
No unpaid mathematical claim was inserted as an assumption, and no sorry/admit/axiom/unsafe/native_decide was added.

## Validation and next entry
Static forbidden-token scan passed. A script verified that the reused theorem proof body is byte-for-byte the original apart from moving epsilon/hepsilon/retain/cap introductions. Quantifier-order check passed. Independent read-only reviewer found the strengthening mathematically sound and no obvious new Lean issues; this is not elaboration evidence.
No Lean build, kernel replay, axiom audit, CI trigger or user-machine access occurred. Full dependency validation remains with the existing compilation-repair workflow, using this exact branch head. Its next entry is this module plus downstream callers of the compatibility theorem. New export must be checked for complete type and transitive axioms before any green status.
