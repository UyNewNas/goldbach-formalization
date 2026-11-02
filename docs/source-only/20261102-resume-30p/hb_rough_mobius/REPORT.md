# P / hb_rough_mobius: actual unrough Möbius supplier

Status: **SOURCE CANDIDATE; UNCOMPILED; ZERO FORMAL CREDIT.** The broad node `P3.6.same_rho_PP` remains **OPEN**. This task supplies a genuinely missing zero-cutoff adapter to O's exact `ClassicalUnroughMobiusSW` interface. It does not re-prove O's Rankin tail, convolution, small-w reduction, or literal rough-Möbius prefix, and does not take their desired estimate as a premise.

## What was missing and what was found

O already reaches `eventually_roughMobius_prefix_log_saving` and the literal HB role prefix, conditional on `ClassicalUnroughMobiusSW`. That proposition is defined in `O/hb_rough_mobius/P5ActualRoughMobiusSmallSW.lean:22`; it had no supplier in that branch. The current repository's prime and von Mangoldt SW theorems cannot be used as Möbius estimates just because their names contain SW.

A deeper source search found an actual suitable analytic input in the local archive: `20261027-RoughSW-PerronContour/Part3ActualRoughSmoothedContourBudget.lean:21`, `exists_actual_rough_smoothed_contour_budget`. Its statement allows **any real cutoff z ≥ 0**, has the actual signed Perron sum on the left, and supplies explicit left-edge, horizontal-edge, and truncation terms. It has no character-cancellation or SW premise. Its archived specialization `Part3ActualSmoothedRoughCharacterSW.lean` fixes `z = roughZ x`; importing that conclusion cannot give unrestricted μ. The archived GlobalClosure sharp/interval draft also fixes that cutoff and was explicitly unfinished/unreviewed in its STOP10 checkpoint. Neither old final theorem is imported as the supplier.

The generic budget's source chain consumes the pinned goldbach declaration `AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4.exists_uniform_quadratic_LFunction_one_lower_bound` in `MathlibNt/AnalyticNumberTheory/Siegel/Bombieri1965Theorem4SiegelLowerBound.lean:22`. Its initial input is only `η > 0`; its conclusion supplies a positive uniform constant for actual primitive nonprincipal quadratic Dirichlet characters. Actual primitive induction, finite Euler correction, zero-free rectangles, original-level reciprocal bounds, and Perron then supply the full original-modulus nonprincipal character estimates. This is a substantive implemented source chain, though the local archived adapters are still held and uncompiled.

## New declarations and exact adaptation

`P5UnroughMobiusSmoothed.lean` exposes `exists_actual_smoothed_unrough_character_SW`. It reuses the generic physical contour budget at `z = 0`. The actual extra work is the monotone amplitude comparison

`log(max 2 0) ≤ log(max 2 (roughZ x))`

and the corresponding Euler-width gate `roughDelta 1 x * log(max 2 0) ≤ 1`. Existing conductor widths, amplitude thresholds, and asymmetric scale estimates are used with the original character and original q. The old private scalar horizontal/tail payment proofs are retained in the new namespace; they are adapted support code, not claimed as new analytic results. All constants precede x, q, χ, τ, U, and the endpoint X. The generic Bool interface is retained solely to consume the existing physical coefficients; this task does not redo the rough-one project.

`P5UnroughMobiusSharp.lean` obtains the actual smoothing kernel from primary `SmoothExistence`, applies the existing signed unsmoothing inequality with ε = log(x)^(-(A+1)), absorbs the bounded endpoint error using X ≥ x^θ, and subtracts two literal sharp prefixes. It exposes `exists_unrough_sharp_character_SW` and `exists_unrough_interval_character_SW`. The interval is exactly `Finset.Ioc (Nat.floor X) (Nat.floor Y)`; neither endpoints nor modulus are silently changed.

`P5UnroughMobiusSWSupplier.lean` proves `roughOneSlot_zero`, the literal coefficient identity `zero_cutoff_base_eq_mu` including n = 0, and `modulus_log_transport`. Its final declaration is

`ImbalancedChen.P5Z.UnroughMobiusSWSupplier.classicalUnroughMobiusSW : ClassicalUnroughMobiusSW`.

It has **no SW hypothesis**. The precise interface transport is:

| O requirement | Supplied argument |
| --- | --- |
| For all fixed A ≥ 0, B ≥ 0, K ≥ 1 | Request the character theorem with A, B+1, L=0, θ=1/2 |
| Constants before W,a,b,q,r | Choose C'=4C and X'=max 2 (max x0 (exp K)) first |
| q ≤ K log(W)^B | W ≥ exp K gives K ≤ log W; hence q ≤ log(2W)^(B+1) |
| W ≤ a ≤ b ≤ 2W | Set ambient x=2W; W≥2 gives x^(1/2)≤W≤a≤b≤x |
| Literal μ and k=1 | Set useMu=true, z=0, τ=0, U=1; prove coefficient equality |
| Primitive residue r, original modulus q | Exact finite character orthogonality at q; no conductor reduction of the AP or φ(q) |
| Actual coprime mean | Principal contribution cancels exactly; averaging nonprincipal twists costs at most 1 |
| C' W/log(W)^A | C(a+b)/log(2W)^A ≤ 4C W/log(W)^A |

In particular q=1 is included through the exact principal cancellation. No principal Möbius asymptotic is assumed. There is no absolute upper bound on q or W. No loss of the original interval or hidden dependence of C on its endpoints occurs.

For the already implemented O small-w use, ℓ≤U^(1/4), V=U/ℓ≥U^(3/4), w≤V^(1/4) yield W=V/w≥U^(9/16). O correctly requests K=(16/9)^B and transports the threshold and logarithmic constant. The new theorem supplies precisely that quantified input. No second prefix wrapper is added: the existing O theorem can consume `classicalUnroughMobiusSW` directly after import installation and verification.

## Reuse, provenance, and installation boundary

`REGISTRY.json` records exact raw SHA256 hashes, direct imports, declaration locations, and intended install modules for the three new files and all reused dependencies. Existing public O/M/J sources are referenced at their existing paths, never copied. The O hashes remain the frozen ones, including prefix `0c871e9f248e5679cf30509fc32c6f5bdeec7cbef49b491c2c27266af62b31f0` and small-w `2f13559f0cb248912e2acb3de46bd0d273e8ddd0ba916b6c062881ee29e0cd1c`.

Sixteen necessary archived dependency files had no pre-existing public docs counterpart found by module/file search. They were mechanically copied **byte for byte** into `dependencies/`, with original archive path, original/copy hashes, byte equality, and intended `ImbalancedChen.*` module recorded. These are `reuse_only`, with no new proof credit. Their original locations were local `.lake/proof-continuation/source-reviews/drafts/...`; the copies make this delivery reviewable but do not install or validate them.

The registered graph follows every import through the new and archived files and stops explicitly at production, existing public source, or pinned native-package boundaries. It is not a claim that the entire recursive project import/kernel closure has been checked. All source-only module targets remain uninstalled. O's downstream public/archived Brun and prefix dependencies are governed by O's registry and the separate t16 review, rather than recopied here. P's supplier only imports O's SmallSW interface and its inherited chain; it does not import the O final prefix or Brun consumer.

Native sources were inspected in the local WSL mirror at goldbach revision `09b97db5764ade1246bfb77206baa1b124760958` and mathlib revision `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, matching the manifest. Read-only file hashes and source inspection are not a new compilation or verification of those packages.

Rejected near suppliers are separately pinned in the registry: `NonprincipalPrimitivePsiSiegelWalfiszSource` and its Richert supplier use von Mangoldt coefficients; `primeSW_uniform_real` uses the prime indicator; nonquadratic pointwise SW controls `lambdaCharacterPrefix`; the Chen M2 source controls a finite Möbius Dirichlet-polynomial moment. None supplies O's literal unrough μ discrepancy directly.

## Manuscript and difficulty classification

The manuscript was checked at `manuscript-body.tex:138–175,323–355`, hash `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`, and the original completion note at lines 185–207, hash `a953b3233c1249b4791830da33b76a58b19ca110a5e1b5b6172b3248a00053e1`. The primitive residue, exact coprime mean, all prime-power supported w, and original logarithmic range agree with O. The missing supplier was a **class 2 fillable omitted deduction** from an existing generic actual analytic source, with **class 1 Lean/API and elaboration work still unverified**. This audit found no evidence of a class 3 substantive manuscript gap at this leaf. That is not a judgment on every other PP obligation.

## Static checks and remaining obligations

Checks performed: source reading; declaration/import inventory; native API signature inspection; raw SHA256 and copied-byte comparisons; exact old-source pin comparisons; static admission-token scan. No new `sorry`, `admit`, `axiom`, or runtime/finite proof guard evaluation was introduced. No Lean/lake/compiler, CI, Git operation, production edit, old-file edit, or installation was performed.

Independent t28 read all three new files plus exact orthogonality, signed unsmoothing, and the generic contour chain; its reported mathematical interface check found no coefficient substitution or parameter mismatch. Its source review and any final caveats are recorded separately by t28. This report does not convert that static review into elaboration evidence.

Remaining obligations are installation and elaboration of this complete new/archived import segment, checking all inherited production/native/public dependencies at the pinned environment, and the independent remaining PP branches. The proposition `ClassicalUnroughMobiusSW` is eliminated as an external premise **in this source candidate**. The whole project, O's prefix, and `P3.6.same_rho_PP` are not claimed kernel-complete. Every delivered Lean file has `compiled=false`, `kernel_verified=false`, `formal_credit=0`; existing guards remain `UNEVALUATED`.
