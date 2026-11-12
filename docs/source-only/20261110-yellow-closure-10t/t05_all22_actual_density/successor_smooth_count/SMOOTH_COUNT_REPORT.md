# Final finite coefficient on the smooth physical pair count

Author-frozen at the end of this round. Two source modules, zero new numerical inputs. The endpoint is a finite and eventual inequality for RealB on the final finite-bank rectangular coefficient. Independent review and Lean elaboration are pending.

## Actual endpoint

`ImbalancedChen.P4BOriginalFiniteSmoothSchedule.exists_same_coefficient_count` takes `1/2 < b < 1`, `0 < κ₀ < 1`, `19/96 < (1−κ₀)b/(1+b)` and arbitrary positive mass/endpoint tolerance η and maximum source smoothing width. It selects one positive smaller width cap and one natural threshold at least two. For every positive outer source width s at most that cap and every even N at least that threshold, the quantities are as follows.

- `T = 2N^(1−κ₀)` and `W_s = smoothPhysicalPairOuterRamp b N T s`. Its mass `X_s` is the sum over the actual labelled prime pairs.
- `ω = νβ²`, `w = N^ω` and `L = N^(νβ)`, with `ν > 0`, `0 < β ≤ 1` and `ω ≤ 19/96`.
- `Q = P4AOriginalFull87CompiledCounting.moduli N w` and `ρ = P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a ω N τ L`, with `τ = alignedWidth (jointIndex (bank m) (data e q a).m) k`.

The theorem gives `X_s ≥ 0`, `|X_s/(N/log N) − log(1/b)| < η`, and the following upper bound for every further choice of the displayed policy and rectangle parameters.

```text
(RealB b N : ℝ) ≤ X_s * physicalDensitySum Q ρ
                + Part3.primeProductSignedError 2 N N Q ρ W_s
                + η * singularNormalization N
```

The source width cap and threshold are uniform in m, r, n, e, q, a, k, ν and β. An independently fixed rectangle width therefore retains exactly the same coefficient in the density and the signed discrepancy. `original_product_gap` derives the strict exponent gate from the manuscript condition `0 < κ` and `κ₀ < κ/(4(1+κ))` when `b > 1/2`.

## Finite proof and charges

`P4BOriginalFiniteSmoothCount.realB_le_smooth_signed` has the literal final two summands `(Nat.ceil (cutoff N) : ℝ) + (T+1)`. At every nonzero product fibre each prime divisor exceeds `N^(19/96)`. Every modulus of Q divides the physical sieve product at the ceiling of this cutoff. The signed coprime correction is consequently zero on this same rectangle. The complete integer-shift carrier includes products larger than N. The prime-product discrepancy keeps both labelled orientations and the square case with their actual weights. Its sign is untouched.

The uniform schedule uses the existing four physical boundary-strip and source-mass estimates for the stated mass precision, and the joint endpoint estimate for the single additive `ηH_N`. These are separate conclusions at the supplied tolerance. The modules consume no further compiler or density reserve and require no active-modulus gate beyond the proved divisibility. T01's frozen common-coefficient endpoint still contains the actual early defect. This supplement supplies a count inequality for that very coefficient independently of any asserted K-density bound.

## Remaining same-coefficient arithmetic

The signed rank-two term above remains to be estimated on the chosen final ρ for every sufficiently large even N. The original prime-product completion, section 2, multiplies the incoming smooth profile by the separate smooth factor `η₀(product/N^(1−κ₀))`, zero through 1 and one from 2, before constructing complete dyadic boxes. Here `W_s` relaxes the lower product wall about `2N^(1−κ₀)`. Its nonzero support alone permits a factor `N^(−s)` below that wall. The earlier S19 small-product trim estimate uses `attachedUpperCoefficient` on its own support and has a primitive coefficient-size hypothesis. For this final rectangular ρ the signed transition to the complete-product chart profile, or a positive counting bound using that profile directly, is unpaid. The original hard pair source satisfies product at least `2N^(1−κ₀)`.

The Part 3 memberwise licences, bounded restoration sums, local low-rank distribution and medium and long production bounds must apply to this exact ρ and the retained profile. `P4AOriginalFiniteFallbackCommonGroups.high` reads `0 < ζ ≤ min(min(uniformMargin(m)/64, 1/400), e/32)`, `τ(J₀(ω)+1) ≤ ζ` and `2νβ ≤ ζ/16`, with its actual source membership and local complete-scale and Type II range. `P4AOriginalFiniteFallbackPPSchedule.joined` supplies a compiler-compatible β and k at a prescribed positive budget. Its existential β and k must be selected in the final common proof. The current ordinary coefficient endpoint already selects its own pair. These two existential statements do not identify their witnesses.

## Archive

The registry records both source files, every direct import, the principal arithmetic sources, the independent-scope historical S19 reference, the original committed manuscript sources and the current upstream coefficient manifests. There are no new certificate rows or test outputs. Only source declarations, provenance and file bytes were inspected. This checkpoint adds zero kernel-verified credit and zero whole-All22 or PP closures.
