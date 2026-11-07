# P task 15: primitive scale and complete conductor payment

**Broad node `P3.6.same_rho_PP` remains OPEN.** Three new strict Lean source candidates are confined to this P directory. They have `compiled=false`, `kernel_verified=false`, `formal_credit=0`; finite guards remain UNEVALUATED. No Lean, lake, compiler, CI, numerical replay, mathematical evaluator, Git executable or child agent was run. Validation here is textual source review and metadata/hash checking only.

The genuine increment is the deduction of the high-conductor hypotheses from the two original L2 estimates and complete product scale, extension from the special `.45` level to every fixed below-half gap, payment of the common rounded cutoff by the **implemented** variable-prime small-conductor theorem, and transport of thresholds/error units to the original target scale. There is no premise asserting the requested discrepancy bound, complete Gamma BV, or an auxiliary SW theorem.

## Deduplication and retained suppliers

BRIEF and PRIOR_TASK were read first. All four O files for this task were read; that O directory has no REPORT or REGISTRY to reuse. The O small-conductor REPORT/REGISTRY and its prime/profile/sum sources, the M primitive induction/large-sieve sources, production scale/logarithm modules, and other source-only occurrences of `rowEnergy`, `energyProduct`, power/log absorption and original/local scale transport were searched. None supplies this complete primitive-scale deduction and the final common-cutoff local saving. O remains imported, unmodified: its finite ledger is sufficient and is not repaired or duplicated.

The following exact sources are reused. Full SHA256 values for every listed source, all six O small-conductor modules, and selected native APIs are in REGISTRY.

| Source relative to repository | Exact reused declarations | SHA256 |
| --- | --- | --- |
| `docs/source-only/20261102-resume-30m/gamma_short_fibre_bv/P2GammaInducedCharacterDictionary.lean` | `inv_totient_product_le:88`, `original_Gamma_nonprincipal_dictionary:157` | `6de294cd9e011611228de996b711df5c13e766997124f730da82477e89ce1e64` |
| `docs/source-only/20261102-resume-30m/gamma_short_fibre_bv/P2GammaConvolutionLargeConductor.lean` | `inducedShell_largeSieve:102`, `sum_inv_mul_totient_le_eight:187`, `induced_quotient_charge:202` | `fc80465d0075961adce74c1f65ff800c1b2d9934e33b7dcc8674acf725923db9` |
| `docs/source-only/20261102-resume-30o/gamma_conductor_sum/P2GammaExactConductorRegrouping.lean` | `existsUnique_primitive_induction:73`, `sum_nonprincipal_induced:82`, `sum_conductor_quotient:120`, `allNonprincipalMajorant_eq_inducedTotal:239` | `ee2a4746b25e3d40a44be2773254de69dec4f1ad77a6475bb9beac4094cff264` |
| `docs/source-only/20261102-resume-30o/gamma_conductor_sum/P2GammaDyadicConductorSum.lean` | `sum_high_eq_dyadic:55`, `inducedShell_expanded:168`, `fixed_quotient_high_le:225`, `highConductorTotal_le:292` | `91a0483f754855a158505f4662e3cf02011f236f215e918b1f01b79cbc161b4c` |
| `docs/source-only/20261102-resume-30o/gamma_conductor_sum/P2GammaConductorScaleThreshold.lean` | `inducedTotal_eq_low_add_high:103`, `highConductorTotal_scale_le:177`, `cutoffExponent_bounds:243`, `eventually_one_add_log_power_le_fixed_power:279` | `b473ae98b28ae05655e0f1dfe93963be2c28a5b2af36bf64c94e155c585ce748` |
| `docs/source-only/20261102-resume-30o/gamma_conductor_sum/P2GammaSmallConductorIntervalBridge.lean` | `paddedRow_transform:46`, `naturalRectangleDiscrepancy_eq_character:90`, `lowConductorTotal_eq_smallConductorContribution:130`, `natural_rectangle_norm_sum_le_character_sum:220` | `683f048040e03060f8db4845cee47af3eb458378f60f636502cdeb8a1142b5ea` |
| `docs/source-only/20261102-resume-30o/gamma_small_conductors/P2GammaVariablePrimeSmallConductor.lean` | `variable_target_prime_character_completeScale:25`, `variable_profile_small_conductors:119`, `variable_profile_small_conductors_logSaving:183` | `4150ffe8c21aee467acde952d514caec4935043f982f23e37f3e4953a59a719e` |

The actual small-conductor supplier in the new composition is the last theorem in that table, not its estimate as an assumed hypothesis. Its existing chain invokes `complex_profile_prime_SW:66` in `P2GammaVariablePrimeProfile.lean`, which calls the genuine native `primeSW_uniform_real:46` in `MathlibNt/AnalyticNumberTheory/LargeSieve/LiLiuFouvryPrimeSWFamily.lean`. The latter source was inspected directly at the native package path recorded in REGISTRY. These are existing source bodies, not a claim that their imports have been compiled.

## New deductions

`P2GammaPrimitiveScaleThreshold.lean` supplies `primitive_scale_bounds:38`. Let `x=M*N`, `x^eta<=M,N`, and use fixed nonnegative constants `ea,eb,c`. From the physical bounds

```
La <= c^2 M,        Lb <= c^2 N,
Ea <= ea^2 M l^C,   Eb <= eb^2 N l^C,
```

it derives, with `d=c^2+2c`,

```
sqrt(Ea) sqrt(Eb) <= ea eb sqrt(x) l^C,
sqrt(La) sqrt(Lb) <= d sqrt(x),
sqrt(La)+sqrt(Lb) <= d sqrt(x)/x^(eta/2).
```

Here M and N are support scales. No positive lower bound is imposed on the prime subinterval length, La or Lb. Squared constants merely parameterize arbitrary fixed nonnegative norm/support constants. The two energy estimates and complete-scale identity replace O's previously combined hypotheses; this is not another wrapper assuming their conclusion.

`exists_primitive_high_conductor_threshold:119` fixes A,C,eta,epsilon and the constants before one x0, then quantifies over x,M,N, both rows, integer translations, caps and Q. It allows `Q<=x^(1/2-epsilon)` for every fixed positive epsilon. It invokes O's proved absorption at exponents eta/2 and epsilon and O's finite `highConductorTotal_scale_le`. It concludes the high ledger is at most `highCoefficient(ea,eb,c)*x/log(x)^A`. The coefficient retains

```
lsLogCoefficient = 18+4/log 2,
dyadicCountCoefficient = 1+1/log 2,
highCoefficient = ea*eb*(8*d + 8*(lsLogCoefficient+1)*dyadicCountCoefficient*d
                             +64*lsLogCoefficient).
```

The original large-sieve factor remains `L+(2*ceil(log(Q^2)/log 2)+12)*Q^2` before O's explicit log majorization. Unique primitive induction, both quotient unit gates, the original `1/phi(r*k)` denominator, the `U+V/k` shape and final `sum 1/(k phi(k))<=8` all remain in the imported chain. No coprimality between r and k is introduced and no sharp `L+Q^2` sieve is substituted.

`P2GammaPrimeLocalConductorSaving.lean` supplies `cutoff_le_log_power:29` and `exists_actual_prime_local_conductor_saving:57`. For a requested **real** accuracy A set

```
An = Nat.ceil A,   H = An+C+3,   B = H+1.
```

The same dyadic cutoff satisfies `R0<=2*(1+log x)^H<=log(x)^B` once `log x>=2^(H+1)`. The actual small-conductor theorem is called at accuracy `An+Hmass`, after B is fixed; its internal prime accuracy is therefore `An+Hmass+2B+2`. The complementary physical mass `rowMass<=em*N*log(x)^Hmass` then pays its L1 factor using M*N=x. Taking the maximum of the high, actual-prime-small and cutoff thresholds yields one threshold before every moving profile, endpoint, target, complementary row, level and residue function z. The conclusion is the full local sum of rectangle-character norms with constant `Cs*em+highCoefficient+1`, at accuracy `log(x)^(-A)`. The final real-accuracy conversion uses `An>=A` and `log x>=1` explicitly.

The prime coefficient is the actual `targetDeleted target (profilePrimeCoefficient f)` on `primeSWInterval u v`. The support bridge and exact low carrier are O's proved theorems. Both quotient masks and exact induced-level weights survive. The same bound holds for every moving z chosen after the rows and scale. O's already proved natural-kernel identity attaches this character rectangle to the literal Gamma kernel on coprime target moduli; that identity was not rewritten here.

`P2GammaOriginalScaleTransport.lean` adds elementary original-target transport, keeping T and x distinct. `eventually_power_le_fixed_multiple_power` absorbs a fixed positive chart constant in `c0*T^beta` by choosing a strictly smaller exponent. `exists_original_scale_common_threshold` gives one original T threshold before every x satisfying `T^beta<=x`. `local_log_unit_le_original` proves, for real A>=0 and physical `T^beta<=x<=c*T`,

```
x/log(x)^A <= (c/beta^A)*T/log(T)^A.
```

These theorems remove the elementary threshold/log transport, while still requiring an actual chart to supply its stated physical scale comparisons. They do not claim that an arbitrary complete product lies near the target.

## Manuscript correspondence and difficulty classification

Manuscript `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex` at 264-278 states only `product=O(N)`, fixed polylogarithmic geometric control, and the same-rho PP conclusion. Lines 334-337 route low ranks to below-half BV. Its SHA256 remains `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`.

The explicit local note at 9-34 fixes the original two energies and `x=M*N`; 89-92 contains the omitted length/power-to-log step; 94-111 explains the cutoff-dependent stronger prime accuracy; 130-150 requires a complete-scale, rather than residual-quotient, comparison and a genuine post-loss level gap. Its SHA256 remains `88edfb5f605e65ad7f05a702a963b5dff1b21f0b4e757edbf4eaed304f4e8f56`.

1. **Lean expression/API:** all new bodies are uncompiled. The relevant square-root, rpow monotonicity/product, and rpow/log asymptotic signatures were inspected from the native mathlib source; elaboration and kernel checking remain user-owned.
2. **Fillable omitted deductions:** separate L2 to combined energy, two positive support scales to the length saving, arbitrary fixed below-half gap to logarithmic level, rounded cutoff to the fixed small-conductor range, stronger prime accuracy, real A conversion, and original/local threshold/log transport now have source bodies. No new analytic theorem is assumed to fill these steps.
3. **Possible substantive manuscript-interface gap:** `product=O(N)` alone does not supply a lower complete scale, the actual post-loss positive epsilon, or the physical norm/profile bounds for the original separated Gamma rows. The local note explicitly reserves these obligations at 132-138 and 148. Their absence would block application of this local theorem, not the elementary conductor algebra. This packet neither diagnoses an analytic contradiction nor manufactures those source obligations.

## Remaining obligations and verification boundary

The actual separated Gamma prime/complement dictionary must supply the two L2 bounds, complementary L1 mass, padded caps, all labelled multiplicities, target deletion convention, and uniform profile size/variation. The actual near-target chart must supply a fixed lower complete scale and the post-loss below-half gap. Excluded boundary/trim bands, complete-product/Mellin tails, chart/Fourier total variation, the singleton-prime case, and the bounded same-rho attachment remain outside these three files. The broad node and full task are therefore OPEN.

The new modules are not installed at their intended production import targets. REGISTRY records each exact path, install module, direct-import resolution, declaration line, bytes and SHA256. It also pins the O/M suppliers and selected native APIs. Metadata hashes and text scans do not certify elaboration, a clean package checkout, axiom freedom of all transitive imports, or kernel verification. No finite guard was evaluated.
