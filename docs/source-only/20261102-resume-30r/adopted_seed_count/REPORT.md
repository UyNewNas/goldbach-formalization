# R13 / D11 — actual classical-tail count starting point

**PARTIAL SUPPLIER; complete D11 HOLD. SOURCE ONLY, UNCOMPILED, kernel_verified=false, formal_credit=0.**

This packet supplies a missing ordinary arithmetic count starting point on the original U3 classical tail: its full signed Rosser `rowError`, both deterministic li/centre atoms, the actual parent main-term normalization, and the true-li same-Q finite-family normalization. It reuses the existing immutable arithmetic recursion. It does **not** supply the adopted `2327/100000` seed, the original old H/h analytic licences, `hstarts`, `h5`, `h6`, or H430. The parent explicitly accepted this necessary D11 subproblem while retaining the complete D11 acceptance criterion.

No Lean, Lake, compiler, build, CI, finite-guard execution, numerical replay, Git operation, production edit, old-file edit, or child agent was used. All tactic bodies are unevaluated source. Only the assigned `30r/adopted_seed_count` directory was written. The first desktop interruption happened before any R13 source had been written; restoration checked the empty directory, then resumed the same task.

## Original source and scope

The original current manuscript `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex` has SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`.

- Body 795–806 requires a finite nonnegative marked family with one physical Q and its actual singular-factor/totient/log-residual Theta. A profile integral alone is not a count estimate.
- Body 808–817 retains true alpha, full/selected squares, and physical ceilings on enhanced descendants. This packet changes none of those objects and makes no enhanced-descendant claim.
- Body 819–822 is the adopted four-round seed. Body 857–865 requires predecessor-only arithmetic induction and keeps the designated 248 occurrences distinct from seed-only430.
- Body 887–892 keeps the causal starts, removes the entire former H248 correction when replacing the second start, and retains the real max-two U3/U4 clamp.
- The fuller source `proof-library/source/global-chen-lower-completion-20261010.txt:175–193` distinguishes positive-family normalizers, signed ordinary coefficients, enhanced states, and complete classical levels below half. Its 254–256 explicitly assigns the U3 tail to the limit of level one half from below and retains the physical clamp.
- `second-seed-certified-finite-feedback.tex:13–30,113–145` requires the admitted stable-prefix comparison cutoff and named analytic inputs before the four finite rounds. `second-seed-stable-prefix-extension.tex:18–28,52–74,131–178` supplies the declared prime-box source class, the classical complete-modulus alternative, and the admitted below-two child comparison. These are not replaced by a weaker Wu source.

The local difficulty is class **II**, a fillable source deduction: Q13 paid only the true-li AP component of the actual initial classical-tail row; the deterministic recentering and parent main normalization were still explicit remaining obligations. Class **I** remains for installation/elaboration. The full adopted seed and old-H/h source realization remain class **III** uncompleted suppliers under the manuscript's named analytic inputs. No counterexample to the manuscript is asserted.

## Reuse audit

Q10/Q11 REPORT and REGISTRY, Q12 REPORT, final Q25 bank/enhanced review, Q13 REPORT/REGISTRY, and final Q26 H430 review were read. Production, all source-only batches, and ignored `.lake/proof-continuation/source-reviews/drafts` were searched for the actual count, adopted seed, full tail error, and parent-normalization statements. The inspected duplicates are recorded in REGISTRY; this is a scoped search result, not a claim about every possible external theorem.

The existing count induction is I `w2_feedback/P2AllW2ImmutableCountRecursion.iterate_encloses:128`. K `h430_count/Part5OriginalU34SameQCountEntrance.row_seed_and_joint_count:140` already inserts the actual original receiver into that recursion. It keeps the exact initial signed errors. Neither theorem is rewritten or newly credited here. Q10's W2 mother/count tuple conversions and the P/Q profile/mass work are also not repeated.

Q13 `Part5OriginalH430ClassicalTailBV` is used directly for `originalU3Primes`, `tailActive`, `tail_complete_modulus`, `eventually_tailSignedPrimeAP_log_saving`, and `rowError_eq_trueLi_components`. Its BV proof already pools complete p*q moduli without an outer-cardinality loss and does not assume p²≤Q. K's actual row support/cardinality and selector cardinality bounds are reused for the deterministic costs. Production's actual centre-prime/divisor bounds, power/log budgets, singular-normalization lower bound, and true-li normalization are also reused directly.

The native Mertens supplier is `MathlibNt.Wu2008DoubleSieve.LocalProductReal.eventually_localSieveProduct_relative`, for every positive even integer M in a fixed polynomial cutoff envelope. The native `PhiBounded.canonical_upper_bounded_normalization_budget` and `canonical_lower_bounded_normalization_budget` retain the genuine A/a-bar functions and the sign of the lower main. These suppliers do not require Wu box membership. This packet proves their actual original-row support conditions instead of invoking `classical_two_sided_count_seed` with its inappropriate tail-root squared-prefix condition.

Reliable remote reuse was checked at the exact primary revision `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. The raw HTTPS bytes of `LocalProductReal.lean` (9578 bytes, `6fda487bc4dee90eabb6a2c26ff82055773bfac475a5cbaafd198071ab305e62`), `PhiBounded.lean` (19765 bytes, `e5b8686e4ae3bd6e3a3794182df9197080388a40ad87e9dba4f7812bc1c36ff8`), and `PositiveGainActual.lean` (3392 bytes, `5ff57708ba4a3e1ff0aa4b0eb25dee7f314e2c12bf45bcb25960353036eabcef`) were fetched read-only and match the native UNC source bytes exactly. The configured revision and directly read native HEAD agree. No remote source was guessed, modified, or imported as an axiom.

The adoption boundary was rechecked in production `P2OriginalPositiveSeedLicense`: `actual_short_support_uniform_count:98` is the fixed-below-half Wu source, and `positiveSeedNumerator_lt_adopted:181` proves that its amount is smaller. Hidden `P2HistoricHBankZeroPrefix.bank_cell49_actual_h:43` proves only the zero lower boundary; `PositiveSuffixLicences:56` still states the positive suffix target. Hidden `P2ActualW1SeedLowerH.actual_h_lower_from_w1_seed:23` transfers only `1/5000`. None is substituted for the adopted seed or original immutable analytic history.

## New proof bodies

### `Part5OriginalClassicalTailFullError.lean`

Intended module `ImbalancedChen.Part5OriginalClassicalTailFullError`; raw SHA256 `8468a3e9130655546a55477113e5c76e8f1dad968318c68fb86c06ca65c407dd`; 14182 bytes.

`tailPrimes` is the original U3 half-open prime selector filtered by the inclusive tail boundary `tailCutoff <= primeCoordinate`. `tailRowError_eq_trueLi_components` proves the exact identity

    tailRowError = tailSignedPrimeAP + tailLiCentreCorrection,

where every signed Rosser atom in the second term is

    rowWeight(p,q) * ((2/log 2)/phi(p*q) - centrePrimeAPCount(N,N,p*q)).

The negative centre term is retained under its signed coefficient. No source equality or error estimate is a premise. The complete modulus remains p*q, and target deletion and the physical cutoff come from the unchanged source.

`tailLiCentreCorrection_abs_le` uses the existing centre-prime logarithmic bound, phi(m)>=1, |rowWeight|<=1, the actual active-row cardinality bound N^(1/2), and the actual outer-selector bound N^(1/3). The resulting concrete bound is

    (2/log 2) * N^(5/6) * (1 + log N).

The two inherited power/log suppliers pay its constant and logarithmic parts at arbitrary log accuracy and at epsilon times `singularNormalization N`. This deterministic threshold is uniform before tau in `[0,1/12]` and both signs. `eventually_tailRowError_normalized` combines that payment with Q13's actual BV supplier, at **fixed** `0<tau<=1/12`; no uniformity as tau tends to zero is claimed.

`eventually_tail_count_initial_enclosure` applies K's already proved finite count enclosure to the actual tail primes and pays both signed errors. It places the literal original quotient-prime count between the unchanged lower/upper arithmetic iterates, bounded externally by their actual initial Rosser main terms plus/minus epsilon times the original root normalization. The arbitrary bank/finite round arguments are quantified after the threshold. Their inclusion reuses an established arithmetic invariant; it does not identify any iterate with an H247/H248/H430 table or claim a newly proved positive gain.

### `Part5OriginalClassicalTailThetaSeed.lean`

Intended module `ImbalancedChen.Part5OriginalClassicalTailThetaSeed`; raw SHA256 `ceffb77d6d451516f3e5da5493d90fa3dd247c636e0bf6f427edc953aa9c76ed`; 18595 bytes.

`original_row_cutoff_envelope` derives from the unchanged U3 geometry

    cutoff >= N^(1/24),   p*N <= N^2 <= cutoff^48.

The native uniform real-cutoff Mertens theorem can therefore be applied at B=48, with one threshold before tau and p. The exact logarithm identity converts its strict-cutoff denominator to the actual `log(rowQ/p)/s`. `eventually_original_row_seed_Theta` then consumes the two existing native sign-safe normalization budgets. This step is valid on the full original U3 row band as a **main-term identity/estimate**; only the classical tail has its AP error paid here.

`tailTheta_eq_sum_parentTheta` uses Q13's actual `tail_row_Q` to obtain one common physical `Q=N^(1/2-tau)`. Its normalizer retains the original singular series C(pN), phi(p), log(Q/p), and every selected prime label. `tail_upperCoefficient_eq_one` derives the actual tail query range `[2,3]`; the max-two clamp remains present. The resulting ordinary literal-li count has upper main `(1+15 eta)*tailTheta` and lower main `tailLowerMain-15 eta*tailTheta`.

The installed `logarithmicIntegral` differs from the manuscript's true-li convention by `2/log 2`. Paying the AP recentering alone does not fix the main-term normalizer. The final part separately instantiates production `uniform_trueTheta_relative_error` on (i) the original unit-marked tail and (ii) the same family marked by its actual nonnegative a-bar(s). Positivity of these marks and physical residual positivity are proved from the original source. Its threshold precedes the N-dependent family and marks.

`eventually_original_tail_ordinary_trueTheta_count` supplies

    trueTailLowerMain/(1+eta) - 15 eta*trueTailTheta - epsilon*singularNormalization
      <= actual lower arithmetic state <= actual tail count
      <= actual upper arithmetic state
      <= (1+15 eta)*trueTailTheta + epsilon*singularNormalization.

Here `0<eta<=1`, `epsilon>0`, and fixed `0<tau<=1/12` are chosen before N; eta may subsequently tend to zero in the inherited order. No division by Theta or family mass occurs. Empty tails are included. The theorem uses the same receiver and root cutoff throughout and assumes no analytic count licence.

## Premises actually removed and remaining full target

Removed on this precise original classical-tail starting point:

1. A separate unpaid bound on the literal-li constant and centre-prime deletion in the original `rowError`.
2. A full initial-tail `rowError` estimate as a prospective count-consumer input.
3. A caller-supplied actual row local-product normalization or an invalid squared-prefix admission for applying Wu-box normalization in the tail.
4. A caller-supplied identity between the actual tail parent masses and its common-Q Theta.
5. A caller-supplied literal-li/true-li transport for this root main, including the lower a-bar mark.

The full D11 target remains HOLD:

- No adopted enhanced `1/50` source seed or four source-level W2 feedback rounds have been derived. The literal base `actualJ2omega >= 20249/10^6` and feedback `lambda > 13/100` remain genuine numerical proof bindings; integral identities and recurrence arithmetic do not supply them.
- The original positive switched costs and same-rho PP/moving-residue inputs still have to be applied to the actual D09 causal families. R12/D10 costs and D17 PP are not assumed or claimed consumed by this ordinary tail result.
- No old-generation analytic `H/h` licences for the original marked stable families, fixed H247/H248 history, or seed-only430 interpretation are proved here. Existing raw immutable count induction is retained, not relabelled as any table licence.
- No full descendant count/normalization construction, common 441-generation approximation, or actual H430 improvement is supplied. The residual bound, true alpha, comparison admission, full/selected history, and selected ceilings must be supplied on their actual callers.
- The actual causal grouped starts `3*U1+U2`, including all original replacements/restorations and removal of the former H248 term, remain open; no `hstarts` is exported. `h5` and `h6` also remain open.
- The ordinary tail count is not the full U3/U4 endpoint or its continuous H430 root amplitude integral. It cannot close `h34`, `hLower`, or `P5.6.eight_suppliers`.

## Installation, validation and review

The existing Q13/K/J/I staged import closure must be materialized at its recorded intended modules. Install the new FullError module before ThetaSeed. The two native direct imports use the exact pinned goldbach revision. No installation was performed; the existence of raw source does not prove elaboration of its staged import graph.

Validation consisted only of source reading, scoped text/declaration/import searches, raw-byte SHA256/size comparisons, JSON metadata parsing, and forbidden-placeholder scans. No numeric guard or Lean proof body was evaluated. The two files contain no axiom, sorry, admit, unsafe escape, native_decide, or #eval. REGISTRY lists exact declaration lines, direct imports, source pins, removed premises and remaining obligations.

R27 independently read both new proof bodies, Q13/K source, the deterministic centre/log budgets, and the exact native Mertens/upper/lower budget definitions. The reviewer requested an explicit true-li main transport; it is now supplied in the final three declarations. The final frozen review status is recorded in REGISTRY when returned. Source review does not confer kernel acceptance.
