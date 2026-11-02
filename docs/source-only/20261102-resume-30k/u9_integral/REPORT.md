# K / u9_integral — actual U9 signed midpoint enclosure

Status: **source step written; original saved upper endpoint and full h9 OPEN; uncompiled; kernel_verified=false; formal_credit=0**.

The new analytic result derives a signed midpoint enclosure for the actual original U9 integral on every complete rational partition, including the original 1024 panels. It proves the actual first and second derivatives, continuity on the entire closed source interval, and a rational whole-cell enclosure of the actual second derivative. The shared signed midpoint theorem then supplies the original factor `width^3/24`; no curvature enclosure, integral error, numerical endpoint or h9 inequality is assumed by these analytic theorems.

A separate exact reduction removes the independent lower-integral port from the original fixed-density h9 consumer. It preserves the original stored Simpson slope and `U9Envelope`. The saved upper endpoint remains an explicit OPEN port in this adapter. The adapter is supplemental to the analytic work and is not counted as a proof of that endpoint.

Only `docs/source-only/20261102-resume-30k/u9_integral` was written. No compiler, Lean/lake/build, CI, finite mathematical execution, certificate replay, bulk literal generation, Git, quota call or subagent was used. A generic midpoint draft written before the root's shared-module coordination was removed from this directory; the delivered code imports the single shared module owned by K/u7_sharp.

## Exact original source and predecessor

Read the K README and u9_integral row, J/h9's two full source files, REGISTRY and REPORT, and the independent J `reviews/lower_errors.md` review. That review gives narrow SOURCE_REVIEW_PASS for J's actual repeated-coordinate signed PP payment; it explicitly leaves strict-source PP, both original integral endpoints, common density and h9 open. No inherited source review is represented as compilation credit.

The manuscript comparison uses `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex:562-630` and `691-996`. The literal Y9 pair bands are `h=19/125`, `d=59/250` and the quotient cutoff is `sqrt(N/(p1*p2))`. Lines 879-895 and the lower-completion module at 240-263 retain the original labelled multiplicities and root coefficient `-1/4`. The new real-integral theorem does not deduplicate prime products, change a branch label, or claim an unweighted prime law from the real squared-terminal-kernel dictionary.

The genuine integral remains `currentChenUpsilon9HarmonicIntegral`. The installed exact Fubini/log dictionary gives

    J = integral_[h,d] log((1-t-d)/d)/(t*(1-t)) dt.

The original ordered three-exponent real domain is also connected through the existing `P5U9RealDomain.squaredTerminalKernel_integral_eq_originalJ`. The terminal kernel is `1/(t*u*w^2)` on `w in [(1-t-u)/2,1-t-u)`; the unsquared kernel has a different integral and is not substituted.

Actual producer sources were found and read at `../goldbach-research/certify_sharp_switch_midpoint.py` and `sharp-switch-midpoint-proof.tex`. The former's `log_terms(t,9)` is

    l = log((1-t-d)/d), ld = -1/(1-t-d), ldd = -1/(1-t-d)^2;
    r = 1/t+1/(1-t), rd = -1/t^2+1/(1-t)^2,
    rdd = 2/t^3+2/(1-t)^3;
    main_second = ldd*r+2*ld*rd+l*rdd.

Its `midpoint` routine sums `(value(mid)+second(cell)*step^2/24)*step` and `run` uses `K0=67619/10000`, 1024 cells for the saved artifact. `../chen-imbalanced-semiprimes/verification/data/sharp-switch-midpoint-1024.json` supplies the original saved upper cost. The original independent lower slope is from `../goldbach-research/sharp-switch-simpson-independent.py/.json`: 64 panels, 112-bit Simpson, a separate fourth-derivative method. Both producer families were read without execution.

The true original constants remain `currentK=8452171/1250000`, `currentC=49044063/25000000`, and fixed density `currentK+1/100000000`. K0 is used only where the historical producer used K0.

## New source bodies

`P5OriginalU9MidpointCurvature.lean` proves the exact kind=9 derivative chain from the literal scalar density. Positivity of `t`, `1-t` and `1-t-d` follows from the original closed interval. In particular both logarithm derivative signs are negative. No sampled derivative or interpolated numerical curve appears.

For each rational `h<=l<=r<=d`, reciprocal boxes use the correct opposite endpoints. The logarithm box uses the existing proved lower Taylor value at r and upper value at l. Existing signed four-corner `Enclosure` multiplication propagates these bounds through exactly `ldd*r+2*ld*rd+l*rdd`. `curvatureBox_contains` proves containment for every real point of the closed cell, with no numerical guard as a hypothesis.

`P5OriginalU9MidpointIntegral.lean` imports the shared `ImbalancedChen.P5OriginalSignedMidpoint` from K/u7_sharp. Its `midpoint_bounds` theorem proves the signed Peano identity from FTC and the nonnegative two-half-cell kernel. The U9 module discharges all its derivative/continuity/curvature assumptions from the first file, and supplies the midpoint value through the existing directed log API. It then sums every adjacent cell and uses the exact original Fubini dictionary. The exports include the 1024-panel enclosure, K0-scaled cost enclosure, and three-exponent real-domain enclosure. No 1024-term sum is evaluated or expanded into new literal data.

These rational boxes form an exact **unrounded semantic model** of the producer's mathematical expression and partition. They do not assert equality with every historical Q80 intermediate of `certify_conservative_chen.I`, whose log routine uses bit reduction, 32 odd-power terms and rounding after individual operations. The direct log API here has a separately proved rational remainder. The analytic source and signed midpoint rule are the same; raw output authentication and exact endpoint comparison are still separate obligations. No alternative output is silently identified with the saved endpoint.

`P5OriginalU9UpperOnlyStrictSlot.lean` proves the stored rational comparison `lowerU9AtK0<=savedU9`. At the actual `0<=k<=K0`, a genuine upper bound `J<=savedU9/K0` gives

    k*J <= k*savedU9/K0
        <= savedU9-(K0-k)*lowerU9AtK0/K0 = U9Envelope(k).

The second step is a numerical slope comparison, not a lower bound for J. Thus no independent lower-integral certificate is needed by this consumer. The existing lower Simpson number remains the literal slope. The supplier uses J's `original_branch_PP_of_strict` at the same original fixed e/rho. It retains eventual licence, cap, active scope, actual common density and all three actual strict-source PP estimates.

## Eliminated and remaining obligations

Eliminated in the candidate proof bodies:

1. The actual closed-cell first/second derivative and continuity obligations for the kind=9 midpoint integrand.
2. An assumed enclosure of the actual second derivative over each complete original mesh cell; it is now derived from rational endpoints and the proved log bounds.
3. An assumed midpoint integration error or assumed coverage identity; the exact signed `width^3/24` rule is instantiated on the whole true integral and all adjacent cells are included.
4. The independent true lower-integral port for the fixed-density h9 adapter, by the valid upper-only reduction above.

Still OPEN:

1. The exact saved upper endpoint `J<=savedU9/K0`, with saved numerator `3937512077512215599969887` and denominator `1208925819614629174706176`. The new rational 1024 sum is not claimed to have passed this comparison. Either authenticate all relevant Q80 producer operations/output against the analytic semantics or prove an adequate exact rational comparison without numerical assumptions.
2. The separate true lower endpoint `lowerU9AtK0/K0<=J`, with numerator `16911485600294926597530591281091713` and denominator `5192296858534827628530496329220096`, remains unproved as an independent fact. It is no longer required by the new h9 adapter. No claim is made that the 1024 midpoint lower sum reaches the sharper independent Simpson lower endpoint.
3. Actual common-policy density and common e selection, original cap/licence/active scope, and all three strict-coordinate same-rho PP estimates. J's repeated-coordinate payment is reused, not enlarged into a proof of the full branch PP hypothesis.
4. Same-instance assembly with the other seven suppliers, independent source review, draft installation, elaboration and kernel verification.

No original endpoint, source family, K, c, envelope or root normalization was changed. No manuscript contradiction or absent mathematical source is alleged.

## Installation and verification scope

Install the two U9 analytic modules in displayed dependency order after the shared K/u7_sharp signed-midpoint module. The optional upper-only slot also needs the two J/h9 modules at their declared install targets. REGISTRY records every direct import's actual source path/hash, including uninstalled draft paths; these are not invented production aliases.

The shared signed-midpoint source remains pinned at its final notified hash `507dee4fe27c1fb4b6bdc4ba095a1fde3651a4ca215fa4381fbc4bafe89b0e69`. The three direct Mathlib derivative modules are absent at their manifest-resolved repository installation paths. They are now pinned to actual byte-exact upstream snapshots under this packet's `provenance/mathlib-e4c91783/Mathlib/Analysis/Calculus/Deriv/` directory. These are source-inspection snapshots, not an installed Mathlib tree or import-resolution claim.

The snapshots were fetched read-only from the exact manifest revision `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. `Mul.lean` (29294 bytes, SHA `9eaf8d222c347ea647939daa68fac11edeb7c2572719246ce03d43cb04c94b44`) and `Pow.lean` (5972 bytes, SHA `e800a35ad837f14ee41c68f967af9e27222efa06288c6a6c08efc1af50a550c5`) match K/u7_sharp's exact upstream references. `Inv.lean` is 9568 bytes, SHA `728a55b0c00e62076563a9018c801d6f61ff491ab040b923c7235879060f3477`. REGISTRY records each actual snapshot path, URL, hash, byte count and absent installation target separately. The derivative API declarations were inspected; no proof body changed.

This metadata refreeze addresses the root's deterministic intake finding about three unresolved package-source records. It supersedes registry hash `2f196dad1244c6e9b603e56ac91b6ea60955fa5a28a03b5d9a7a465e250e6962` and report hash `ee6bb5779f83e5033e747c9eb24f56921b21d5c5b7903778164eaaf031ff8c99`. All three delivered U9 proof modules and the shared midpoint dependency are unchanged.

Validation was limited to mathematical/source inspection, textual declaration/import/placeholder searches, JSON parsing and SHA-256 provenance inventory. No proof or endpoint test was executed. All sources remain static candidates with zero formal credit.
