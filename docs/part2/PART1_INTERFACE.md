# Part 1 / Part 2 integral interface

## Status and frozen references

This is a proposed interface contract, not a claim that another session
has acknowledged it. No shared definition or aggregate import is changed.

- Formalization baseline: `1a80c1bcce67886f699d097fc37fd245cd3620bf`.
- Manuscript source fixed by `docs/CURRENT_MANUSCRIPT_MAP.md`:
  `ba6ec11d800eccc54406490631895e174de85766`.
- Manuscript body blob: `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Mathlib pin: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
- Lean: `leanprover/lean4:v4.33.0-rc1`.
- Current constants: `K = 8452171/1250000`, `c = 49044063/25000000`.

The certificate catalog and manifest in this Part own source file hashes,
adoption evidence and row identities. A displayed or stored numerical
bound is not a proof of the corresponding integral.

## 1. Shared coordinates and exact ownership

For the existing selected-prefix mesh,

```lean
qLogPrimeMeshPoint a b m i = a + (i : ℚ) * ((b - a) / (m + 1 : ℚ))
```

An index `j : Fin d → Fin (m + 1)` owns the product of intervals whose
lower endpoint is `qLogPrimeMeshLo a b m j` and upper endpoint is
`qLogPrimeMeshHi a b m j`. Ownership is lower-inclusive and
upper-exclusive in every coordinate. The `m + 1` denominator must not be
silently replaced by `m`. Nonemptiness and endpoint order are proved
separately; `selectedBoxCapCheck` itself checks a strict cap interval,
not arbitrary endpoint order.

Prime histories are reverse-stored. The existing dictionary is
`primeHistoryTuple k history i = history.reverse.getD i.val 0` and
`primeHistoryLogCoordinates N k history i = log(p_i) / log N`.
The ordinary fifth-frontier processing order is `t0 > t1 > t2 > t3 > t4`.
No sorting or reversal may be hidden inside numerical decoding.

Part 1 preserves the exact arithmetic ownership and proves any required
boundary reserve before passing to Lebesgue integrals. Part 2 may use
null-boundary equalities only on the integral side.

## 2. Existing upper-policy interface and its scope

The baseline supplies the genuine cell integral

```lean
primeOwnCubeIcoIntegral a b lambda m j L c =
  ∫ t in logPrimeMeshCell a b m j ∩
      primeAffineGateRegion (primeOwnCubeGateForms L)
        (primeOwnCubeGateBounds lambda c),
    primeTupleMinusProfile lambda t * ∏ i, 1 / t i
```

Here `primeTupleOwnCubeForm t = (∑ i, t i) + 2 * t (Fin.last k)`.
The profile is the actual lower-residual limit

```lean
(2 * Real.exp (-Real.eulerMascheroniConstant) / t (Fin.last k)) *
  suzukiContinuousLowerFactor
    (max 2 ((lambda - ∑ i, t i) / t (Fin.last k)))
```

The maximum is a continuous extension. On the legal own-cube side it
agrees with the unextended expression by
`primeTupleMinusProfile_of_ownCube`.

The already-proved, minimal difference identity is:

```lean
theorem primeOwnCubeIcoIntegral_sub_eq_integral
    {k r : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (lambdaOld lambdaNew : ℝ) (m : ℕ)
    (j : Fin (k + 1) → Fin (m + 1))
    (L : Fin r → (Fin (k + 1) → ℝ) →L[ℝ] ℝ)
    (c : Fin r → ℝ) :
    primeOwnCubeIcoIntegral a b lambdaNew m j L c -
      primeOwnCubeIcoIntegral a b lambdaOld m j L c =
      ∫ t in logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c,
        (primeOwnCubeGatedProfile lambdaNew t -
          primeOwnCubeGatedProfile lambdaOld t) * ∏ i, 1 / t i
```

Both strict own-cube indicators remain separate. Replacing them by one
common indicator changes the mathematical object. The sign is new minus
old in this integral difference; its role as a saving in an upper-policy
density uses the separately proved tree identity.

`selectedPrefixUpperSavingIntegral` is a finite sum of these differences
with `ordinaryUpperFiveGateForms` and `ordinaryUpperFiveGateBounds old`.
`tendsto_actualSelectedPrefixUpperDensity_saving` connects that sum to the
literal selected tree once every selected cap check passes. This is a
single fifth-prefix replacement of the **ordinary** parent. It is not
the complete historical construction.

The ordinary inherited gates are `3*t0 < old` and
`t0+t1+3*t2 < old`. The fifth own-cube gate is not a condition of candidate
enumeration. For a historical table, Part 1 must instead supply the
joint-cell identity with the actual earlier selected ancestors, every
active historical gate, and the original outside fallback. A numerical
bound on the ordinary integral cannot discharge that missing identity.

The simpler `primeBoxInitialSavingProfile` is
`4*(lambdaNew-lambdaOld)/((lambdaOld-∑t)*(lambdaNew-∑t))`.
Its existing cube theorem explicitly permits repeated coordinates and has
no ordering or parent-admission filter. Use it only after proving that
the adopted cell has exactly that profile and region.

## 3. Adopted lower-correction fibre: independent analytic supplier

For the adopted same-mask refinement, the local coordinates are ordered
as `(t, u, z, w)`, with outer cell endpoints `(tl,tr,ul,ur)` and fibre

```text
tl < t < tr, ul < u < ur, a < w < z < Z,
Z = min(ul, (3/13)*(1-tr-ur)).
```

The relevant local gross increment has sign **positive** and kernel
`K / (80*t*u*z^2*w)`. The cutoff is frozen at the outer cell endpoints;
it is not recomputed at an arbitrary interior point. Its licensing
checks include `a < Z`, `Z ≤ ul`, and
`1-tr-ur-(13/3)*Z ≥ 0`.

`ImbalancedChen/Certificates/PairedFibreIntegral.lean` defines the literal
iterated Lebesgue integral:

```lean
pairedLocalIntegral K a tl tr ul ur Z =
  (K / 80) * ∫ t in tl..tr, ∫ u in ul..ur,
    ∫ z in a..Z, ∫ w in a..z, pairedFibreKernel t u z w

pairedFibreKernel t u z w = 1 / (t * u * z ^ 2 * w)
```

Its analytic supplier has the exact type:

```lean
theorem ImbalancedChen.Certificates.pairedLocalIntegral_eq
    (K : ℝ) {a tl tr ul ur Z : ℝ}
    (ha : 0 < a) (hAZ : a ≤ Z)
    (htl : 0 < tl) (htr : 0 < tr)
    (hul : 0 < ul) (hur : 0 < ur) :
    pairedLocalIntegral K a tl tr ul ur Z =
      (K / 80) * Real.log (tr / tl) * Real.log (ur / ul) *
        (1 / a - (1 + Real.log (Z / a)) / Z)
```

The intermediate theorem evaluates the actual integral
`∫z in a..Z, log(z/a)/z^2`. The inner `w`, outer `t`, and outer `u`
integrals use Mathlib's `intervalIntegral.integral_one_div_of_pos`.
The displayed closed form is a theorem conclusion, not the integral's
definition.

The first adopted-row specialization uses:

| Parameter | Exact value |
| --- | --- |
| `a` | `417/5000` |
| `tl` | `937361/4096000` |
| `tr` | `1875373/8192000` |
| `ul` | `194217/1280000` |
| `ur` | `388777/2560000` |
| `Z` | `76088109/532480000` |
| `K` | `8452171/1250000` |

This local gross fibre needs no theorem about the complete historical
tree. Part 2 still must prove its actual decoded row, region and mask
checks, then its rational enclosure. Part 5 receives the resulting local
integral bound and the full retained/subtracted ledger when available.

The 17,572-row same-mask-v2 data and `7/3` are lower-side adopted inputs.
They do not certify the whole upper constant `K`. The replaced `12/5`
increment must not be added again, and the withdrawn `1.9728` branch has
no role in this interface.

## 4. Finite checker obligations and arithmetic trust

The required chain is:

1. Decode the frozen bytes to exact integer/rational Lean data, with an
   unambiguous coordinate and row dictionary.
2. Prove checker success for that data using kernel-checked arithmetic.
3. Prove checker soundness over actual real coordinates, including all
   denominator, sign, endpoint and gate conditions.
4. Apply a proved semantic equality for the actual integral.
5. Sum the disjoint owned contributions and every retained/subtracted
   error term with the correct signs.

Existing reusable envelope checks include
`VariableEnvelope.ScaledBox.marginCheck_sound` and
`extendedBelowCheck_sound`. They certify nonempty effective boxes and
strict pointwise envelope surplus, not integral values. The clipped
upper endpoint only bounds the clipped envelope `min(NT/D, original)`.
The extended adapter additionally requires its actual below-mu dispatch.

For exact real logarithms use the locked Mathlib APIs
`Real.sum_range_le_log_div` and `Real.log_div_le_sum_range_add`, with
`x = (q-1)/(q+1)` for `q ≥ 1`. Their finite odd series is rational. The
upper remainder is exactly `x^(2*n+1)/(1-x^2)`.
Use rational numerators/denominators, `norm_num`, ordinary `decide`,
casts and algebraic lemmas. External floating-point evaluations and
stored JSON bounds provide evidence to check; they do not replace
proof terms.

For a lower enclosure of the paired closed form, the logarithm in the
subtracted fibre bracket requires an **upper** enclosure. The two outer
logarithms require lower enclosures and nonnegativity. The coefficient
and the resulting lower fibre bracket must also be nonnegative before
multiplying inequalities.

## 5. Minimal remaining inputs

- Upper historical route: the actual joint-cell history/region equality
  and its explicit residual profile; ordinary-parent equality is
  insufficient. This is received from Part 1, not assumed as a final gain.
- Lower local route: adopted-row decoding, cell/mask membership, licence
  checks and the kernel enclosure are supplied by Part 2.
- Whole lower ledger: all retained gains, replaced gains, discarded
  old-cell floors, rounding reserves and their exact subtraction signs
  remain explicit until the complete ledger is proved.
- The new integral file's validation state is reported in the Part 2
  handoff. An uncompiled source candidate is not a proved supplier.

No interface accepts the final manuscript gain or the desired numerical
integral inequality as an analytic assumption.
