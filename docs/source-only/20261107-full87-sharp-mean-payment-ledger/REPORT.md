# P1.4 — same-rho exact singleton smooth mean to sharp π density

Base: `5fe69c35fbfce5dff40437f683fb8f177315dec4`; new SOURCE_ONLY Lean candidate: `2be95b1f4e7dd07d0306b56e807ada635f10292a`. Branch `chatgpt/p1-full87-sharp-mean-payment-ledger-20261107`. Source `P4AOriginalFull87SharpMeanPaymentLedger.lean` (271 lines; Git blob `8fe9f4695cbbab3b27f191ea4fef29efba22e927`).

## Genuine new internal calculation

The previous corrected `actualSharpCarrierLiteral` already deleted every p|N, including p=2 for even N; `actual_carrier_singleton_PP_invoice` retained signed PP, two sharp/smooth endpoints and ONE centre invoice. But its mean was the modulus-dependent `finiteCoprimeMass` of the smooth enlarged prime prefix; the manuscript's target is sharp `π(N)/φ(q)`, not that mean.

New proof bodies, for each original frozen policy P and exactly `actualSmallRoughModuli (P false)` and its sign-attached `actualSmallRoughRho`:

* `weighted_prime_mass_sharp_split`: weighted total mass = π(N) − lowerWeightDefect + upperWeightTail. No positivity assumption or inaccurate deletion at p=N.
* `physical_full_q_valid`: directly specializes existing physical support proofs to q>0, Squarefree q and coprime(q,N). This is a proof-use bridge, not a q-level bound.
* `actual_smooth_mean_to_sharp_density_exact`: defines Q, ρ, V=Σ_Q ρ(q)/φ(q), C=Σ_Q ρ(q)*weightedModulusPrimeMass(q)/φ(q), lower defect B and upper tail U and proves the exact identity

      Σ_Q ρ(q) X_W^(q)/φ(q) − π(N)V = (U−B)V − C.

  This uses the earlier proved finite coprime split and has no spurious extra centre invoice.
* `actual_smooth_mean_to_sharp_density_invoice`: bounds the absolute difference by |U−B| Σ_Q |ρ(q)/φ(q)| plus Σ_Q |ρ(q)*weightedModulusPrimeMass(q)/φ(q)|, retaining signed coefficients and exact denominators.
* `actual_carrier_sharp_density_invoice`: joins the previous actual-carrier PP/endpoint/centre invoice with this NEW sharp-density invoice, all using the same ρ and one centre deletion. It does not substitute unrelated sieve bounds or claim asymptotic smallness.

This removes the former unspecified finite algebraic gap between the true smooth-coprime singleton comparison and sharp prime density. It does NOT pay any reserve or prove that these absolute budgets are o(H_N).

## Evidence / checks

GitHub source commit and blob independently reread; 271 lines. Scanner found no forbidden proof escapes, and balanced delimiter check passed (static checks only). Ran 1,820 independent deterministic Python Fraction examples, with signed ρ, nonunit/negative W, varied N, D, q including 0 and totalized φ(0); all exact finite equalities and invoices matched. These tests are synthetic and do not test the saved87 records or the Lean elaborator.

SOURCE_ONLY / UNEVALUATED / UNCOMPILED. No Lean/Lake installation, compilation or kernel replay, no transitive axiom audit, independent proof review, certificate replay, CI dispatch, Codex, external foundations or toolchain upgrade. Formal verification contribution remains zero.

## Unpaid internal and registered external obligations

Actual manuscript Gevrey profile W: exact finite prime universe, 0≤W≤1, interior-one support and prescribed polylog Euler derivative bounds. Physical signed PP permission: q bound <= N^(7/32) (or precisely licensed cutoff), active-versus-display support, actual causal policy, squarefree/coprime, fixed parameters before N, original mixed derivative assumptions. A permitted analytic signed primitive PP is REGISTER_ONLY and not invoked. Quantify new |U−B| density-mass factor, weighted modulus-prime invoice, original endpoints, original centre invoice, primitive discrepancy against H_N without duplicate payment. Rank9 history/cubic expense, ordinary residual, sixth raw/finite/filtered loss, saved87 full geometry/certification, changed/tagged, two separate compiler/density reserve and same-rho final assembly remain yellow.

Next: specialize the fixed manuscript Gevrey W to the original exact prime prefix with permitted derivative bounds, and establish physical q cutoff on ACTIVE rho (not merely the larger displayed support), then pay the above two new invoices quantitatively.
