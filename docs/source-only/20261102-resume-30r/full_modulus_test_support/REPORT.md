# R20 / D18 — full_modulus_test_support

**SOURCE SUPPLIER: the actual six-piece finite-c source is associated with genuine whole-positive-modulus smooth tests.** This removes the Q19/Q29 finite-c/test-support seam at source level. The source is uncompiled: `compiled=false`, `kernel_verified=false`, `formal_credit=0`, all inherited finite bodies `UNEVALUATED`. Actual normalized Kuznetsov, full spectral realization, ABL/continuous fibers, classical spectral estimates and the final 7/32 return remain OPEN in R21–R24. This report does not assign formal verification credit.

Only this assigned directory was written. No Lean/lake/compiler, CI, finite guard, numerical replay or Git operation was run; no production/old-batch/main.md file was changed and no child agent was spawned. After the app interruption, the current source files were checked and work resumed in this same directory.

## Exact manuscript and classification

Read R `BRIEF.md` and `DISPATCH.json`, Q03 D18, Q19/Q20 REPORT and REGISTRY, Q29's independent review, and the literal manuscript paragraphs:

| Original source | Read location | SHA256 |
|---|---|---|
| `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex` | 207–210, 238–254 | `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd` |
| `../chen-imbalanced-semiprimes/paper/source/modules/distribution-medium-completion-20261010.txt` | 325–424, especially 349–380 | `93c7f00f3b2c147fde73105fdbd6d7cb56b78ca6ba241901bf0ca729ecfaaad7` |
| `../chen-imbalanced-semiprimes/paper/source/modules/final-classical-input-correspondence-20261010.txt` | 23–82 | `9604bfb8fdf7325205c8ebe431c7c5e977a3e5bea07e79b8d209548e1a4069db` |

The original calls for a smooth compact test with a common completed-variable interval and additive phase. Q19's exact Fourier expansion retained the literal arithmetic cap `c <= floor(10*C)`, although the separated chi test has wider support. This is **class (2), a fillable omitted conversion**, rather than a manuscript counterexample. Elaboration/import installation is still class (1). The genuine trace and spectral inputs remain the separate class (3) obligations recorded by Q29.

## Actual conversion, and why it is not a modewise cutoff deletion

Here `C = D.cScale`, while `N` in the Q code is a c-smoothing scale, one of `C, 2*C, 4*C`; it is not the manuscript's global size variable. The original positive b-smoothing scale `M` is also unchanged.

1. **First enlarge the unseparated source.** `enlargedModuli D` is the single finite set `Ioc 0 floor(128*C)`, fixed before z,n,p,j, either sign, either Z chart or Fourier mode. The existing actual bump has center 3/2 and outer radius 1, hence its nonzero support has `c/N <= 5/2`. Since `N <= 4*C`, any nonzero original cutoff has `c <= 10*C`, including the `N=4*C` piece and all floor endpoints. `cutoff_zero_outside_original` and `normalizedFrequency_zero_outside_original` prove every newly adjoined **unseparated** term is zero. The existing physical coordinate identity is extended from the needlessly capped c-domain to every positive c; its scalar theorem is reused.

2. **Then reconstruct the entire enlarged family.** `fullChart_hasSum` applies Q19's `original_chart_atom_hasSum` at every enlarged z/n/c/p point and takes finite HasSum sums. No premise supplies a Fourier dictionary, summability, an energy bound, or an unknown source equality. Both fixed Z values remain precisely `S^2` and `2*S^2`.

3. **Only now identify each mode with a full-modulus series.** For actual normalized coordinates `v,w,zeta` in `[1,2]`, the exact identity gives

   `t = q/Y0 = sqrt(v*w/zeta)/(c/N) <= 2*N/c`.

   Nonzero `spectralTest` requires `t > 1/16`, hence `c < 32*N <= 128*C`. This bound is independent of the mode. `fullModulusRow_hasSum` therefore proves actual convergence of

   `sum' (c : Nat), if 0<c and c.Coprime z then Q.chartModeAtom ... c ... else 0`

   to its enlarged finite sum. The c=0 term and the nonunit terms are explicitly zero. `fullChartMode_eq_enlarged` also reorders the finite c/p sums so that each trace call is a whole-modulus row for fixed z,n,p.

4. **The change in individual modes is explicit.** `full_minus_capped_chart_hasSum_zero` proves that the actualCoeff-weighted difference between the new full modes and Q's capped modes has HasSum zero. It does **not** assert equality of individual modes, nor discard their difference after an absolute value. The enlargement adds no error budget because the complete Fourier correction is exactly zero.

5. **Return the full original source.** `original_six_eq_remainder_and_full_modulus` proves

   `(smoothSix D r : Complex) = Q.sixRemainder D r J + tsum (fullSixMode D r J)`

   at the original `J = globalCutoff D x epsilon`. All six original `(M,N)` choices, all original primary/y-sign keys, both Poisson signs and all common dyadic m blocks are present. Its only source restriction beyond OriginalData is the original `a != 0`; the six positivity and `N<=4*C` facts are derived in the theorem.

The arithmetic summand remains Q's exact `sourceKloosterman`: signed m, signed y, `inverseResidue c z`, original c-unit filter, original beta multiplicity, and the outside `M*sqrt(Z)/(c*sqrt(z))`. There is no c-to-q integral or discrete Jacobian substitution. The common weight still is `1_(p in commonMBlock J j) e(ell_1*p/(64*2^j))`; the beta modulation has no future m, c or spectral-height input. No oldform dilation or multiplier is changed or removed here.

## Admissibility, endpoint jets, derivative costs

The test is still the actual production function

`phi(q) = spectralTest ell Y0 q = chi(q/Y0) * e(ell_0*q/(64*Y0))`.

`original_spectral_scale_pos` proves the actual `Y0 > 0`. `original_trace_test_admissible` supplies global C-infinity and compact support in `[Y0/16,16*Y0]`. The separate jet file strengthens this to **topological support strictly inside** `(Y0/16,16*Y0)` by using the actual bump's tsupport. Thus `spectralTest_all_endpoint_jets` proves that every fixed-order derivative vanishes at and beyond both endpoints, including q=0. `spectralTest_div_q_integrable` proves the actual dq/q test is integrable, using its zero collar. This is support/regularity of the literal test, not an invented admissibility record containing the desired trace as a field.

The existing M `Part3ActualExceptionalJLargeTransform.lean` already supplies the actual phase derivative and frequency norm, and its first/second derivative and J-transform proofs are not repeated. The new general-order deduction gives the literal Leibniz expansion and

`norm (phi^(n)(q)) <= testJetConstant(n) * (1+abs(ell_0))^n / Y0^n`.

The constant is selected from the fixed chi and n **before** ell,Y0,rho,sigma or any arithmetic source. `actual_weighted_test_jets_budget` charges the entire actual Fourier derivative mass to

`testJetConstant(n) / Y0^n * actualW(rho,sigma,n)`.

`actual_uniform_test_jets_budget` actually consumes production's `actual_uniform_weighted_l1` and yields a constant times `(1+rho)^(4*(n+3))/Y0^n`. Absolute summability is proved, not assumed. Thus derivative/Fourier mode costs are visible. In particular **order four still costs 28 eta at the W level**; it is not replaced by W0's 12 eta or folded into the previous q=14 budget. Choosing the derivative order before eta/kappa and the final threshold remains R24's original obligation. This conversion does not charge a second 5*kappa or a second occupied D.

The primary external test-class check was [Pascadi v3, Proposition E and Lemma D](https://arxiv.org/html/2404.04239v3#S3.SS3): the trace uses compact smooth tests; uniform transform estimates retain derivative constants. The local source supplies those conditions for this actual phi. No external theorem was installed as an axiom or counted as a Lean proof.

## Zero/tail budget and remaining boundary

The exact final theorem deliberately uses the **old Q `sixRemainder` unchanged**:

- y=0 contains all m;
- m=0 occurs only in nonzero-y primary blocks;
- the global-J hard tail stays the original outside-window summable series.

There is no new endpoint tail from the c extension and no overlap between the first two lanes. Their numerical/analytic payments, source-mass binding at all six scales, common derivative-order schedule, and final 7/32 result remain R24's task. Existing true six-kernel hard-tail suppliers and production source tail/rawLabelBudget were identified by Q29 and are not re-proved or assigned new credit here.

R21 has been given the exact `fullModulusRow`/`fullChartMode` declarations. It reported consuming them in `actual_kuznetsov/Part3OriginalFullModulusCuspInput.lean` for the existing cusp-one arithmetic conversion. That independently authored file is not certified by this report. The remaining genuine normalized trace, signed spectral reflection and full cusp spectral products are still OPEN; so are R22's actual oldclass/continuous fibers, R23's A/J/regular/gap inputs and R24's genuine Eq.(24) source estimate. No `hTrace`, `hEnergy`, arbitrary PacketData, raw-rho replacement, empty spectrum or goal-equivalent premise has been introduced.

## Reuse, provenance, static validation

Searches covered production `ImbalancedChen`, **all** `docs/source-only`, and ignored `.lake/proof-continuation/source-reviews/drafts` with `rg --hidden --no-ignore` over Lean/Lean-text sources. Q19's own finite-c boundary and Q29's review were read before implementation. Searches located the existing native chi, scalar chart identity, weighted Fourier budget, I's sharper physical cutoff support and M's actual phase/second-jet proofs; these were reused or used as boundary evidence rather than claimed as new theorems. No earlier actual whole-family common enlargement plus full-positive-modulus association was found in the inspected source set. This is a bounded search claim.

The production `Part3CommonSmoothCutoff.lean` documents its extraction from the fixed goldbach pin `09b97db5764ade1246bfb77206baa1b124760958`. The actual local bump definitions and proof bodies were read. A root-path raw lookup for the named historical source returned 404 and the remote tree API was rate limited; R02 had no verified upstream path. No remote path or bytes were guessed, and no missing native definition was replaced. The local production source is the proof dependency.

Three exact mathlib source snapshots were fetched read-only from the manifest pin `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` to inspect derivative-support, Leibniz and scaling APIs. They are `MATHLIB_*.source.txt` evidence files, not new project theorem modules and not extra formal credit. Source paths, raw hashes, imported declarations, direct imports and proposed installation mappings are in REGISTRY.json.

| New Lean source | Intended module | SHA256 |
|---|---|---|
| `Part3OriginalFullModulusSupport.lean` | `ImbalancedChen.Part3OriginalFullModulusSupport` | `d6b50adc19fa821ae11f410e0cbdc27dd1e82d84f65c346686957963c18f8cbf` |
| `Part3OriginalFullModulusAssembly.lean` | `ImbalancedChen.Part3OriginalFullModulusAssembly` | `9f8ed52f1cae06208830c7f98d148e9fbbf2e8ce6c3931ca9bcee9d0f01fa121` |
| `Part3OriginalFullModulusTestJets.lean` | `ImbalancedChen.Part3OriginalFullModulusTestJets` | `cf4c4840f8bcdfa778848bb1ded656636dccf5e249e9f957092955a5f7b262dd` |

The Q/P/O/M proposed modules must be staged in their existing dependency order; import names do not mean production installation. Raw-hash/line/import enumeration and scans for prohibited admissions/evaluation are static checks only. They are not elaboration, recursive import-closure verification or kernel acceptance. R30's independent review is separate and owns its own disposition.

Actually removed source obligations: the original finite-c to whole-modulus test association; its c-series convergence and finite/Fourier exchange; original scale positivity and smooth compact test/endpoint qualification; explicit all-order derivative-weight summability and the exact zero extension correction. **Removed genuine spectral-energy premises: zero.**
