import ImbalancedChen.P1OriginalHistoricalPhysicalCoefficient
import ImbalancedChen.P3ActualU8CommonCarrierPP
import ImbalancedChen.P3ActualU8AttachedPhysical
import Mathlib.Tactic

/-!
P3.6 / SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

Specialization to the LITERAL original historical fifth-capped upper policy,
not to an arbitrary retained predicate or to the unbuilt full 87-domain
dynamic parent. The finalPolicy here includes the original firstStop,
activated third ancestor, original fourth continuation and fifth lookup.

The genuine rough coefficient is INTEGER valued and equals its own fixed
odd-test first-exit coefficient even off support. Its small/rough physical
attachment is REAL valued; no integer-valued physical rho_T is inferred.
The full labelled sharp-K U8 PP uses exactly that same physical rho as
the sieve and primitive-density terms, including the p2=q boundary.
The rho_0=19/96 eventual count retains the direct unit-quotient payment.

No final whole-domain compiler, analytic signed PP saving, or W_T Fourier
admissibility is supplied by these finite identifications.
-/

namespace ImbalancedChen.P3ActualU8OriginalFifthPolicyPP

noncomputable section
open Filter Topology
open scoped BigOperators

/-- The literal fifth-capped first-exit integer lookup, cast into ℝ,
agrees with its original odd-test fixed rough coefficient at ALL d,
including off-carrier zero, and has the same original support. This
does not replace or construct any excluded 87-domain dynamic parent. -/
theorem original_fifth_rough_fixed_identification
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Fin 4 → Fin (m + 1)))
    (cap4 : (Fin 4 → Fin (m + 1)) → ℚ)
    (J5 : Finset (Fin 5 → Fin (m + 1)))
    (cap5 : (Fin 5 → Fin (m + 1)) → ℚ)
    (N cap : ℕ) (w z : ℝ) :
    let P := P1OriginalHistoricalPhysicalCoefficient.finalPolicy
      e chi m omega J4 cap4 J5 cap5 (N : ℝ)
    P1OriginalHistoricalPhysicalCoefficient.roughSupport
        e chi m omega J4 cap4 J5 cap5 N cap w z =
      fixedRoughSupport (P false) N cap w z ∧
    (fun d => (P1OriginalHistoricalPhysicalCoefficient.roughCoefficientInt
      e chi m omega J4 cap4 J5 cap5 N cap w z d : ℝ)) =
      fixedRoughCoefficient (P false) N cap w z := by
  dsimp
  constructor
  · exact P1OriginalHistoricalPhysicalCoefficient.roughSupport_eq_fixed
      e chi m omega J4 cap4 J5 cap5 N cap w z
  · funext d
    exact P1OriginalHistoricalPhysicalCoefficient.roughCoefficient_eq_fixed
      e chi m omega J4 cap4 J5 cap5 N cap w z d

/-- On every genuinely containing rough carrier, the original historical
fifth-policy physical coefficient is EXACTLY the common-carrier zero
extension. The original U8 rank-three signed PP is unchanged, with its
complete product, ordered labels, repeated terminal prime and exact
coprime mean; no coefficient-delta or logarithmic estimate is assumed. -/
theorem original_fifth_u8_common_carrier_PP
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Fin 4 → Fin (m + 1)))
    (cap4 : (Fin 4 → Fin (m + 1)) → ℚ)
    (J5 : Finset (Fin 5 → Fin (m + 1)))
    (cap5 : (Fin 5 → Fin (m + 1)) → ℚ)
    (N cap : ℕ) (w z L : ℝ) (rough : Finset ℕ)
    (hcover : P1OriginalHistoricalPhysicalCoefficient.roughSupport
      e chi m omega J4 cap4 J5 cap5 N cap w z ⊆ rough) :
    Part3.primeProductSignedError 3 N N
      (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
      (smallRoughRho (actualSmallRosserSupport N cap w) rough
        (fun d => (P1OriginalHistoricalPhysicalCoefficient.roughCoefficientInt
          e chi m omega J4 cap4 J5 cap5 N cap w z d : ℝ))
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L))
      (P5U8SharpKSource.physicalWeight N) =
    Part3.primeProductSignedError 3 N N
      (P1OriginalHistoricalPhysicalCoefficient.physicalModuli
        e chi m omega J4 cap4 J5 cap5 N cap w z)
      (P1OriginalHistoricalPhysicalCoefficient.rho
        e chi m omega J4 cap4 J5 cap5 N cap w z L)
      (P5U8SharpKSource.physicalWeight N) := by
  let P := P1OriginalHistoricalPhysicalCoefficient.finalPolicy
    e chi m omega J4 cap4 J5 cap5 (N : ℝ)
  have hident := original_fifth_rough_fixed_identification
    e chi m omega J4 cap4 J5 cap5 N cap w z
  dsimp only at hident
  have hcoverRaw : fixedRoughSupport (P false) N cap w z ⊆ rough := by
    rw [← hident.1]
    exact hcover
  have hbase := P3ActualU8CommonCarrierPP.actual_u8_rank3_PP_common_eq_raw
    (P false) N cap w z L rough hcoverRaw
  simpa only [P1OriginalHistoricalPhysicalCoefficient.physicalModuli,
    P1OriginalHistoricalPhysicalCoefficient.rho, hident.2] using hbase

/-- A single eventual threshold precedes every original fifth-policy
choice, including m and both J4/J5 tables. This is a finite source-count
insertion at the true physical rho and real 19/96 presieve cutoff.
It neither establishes the full-domain causal compiler nor estimates
the signed prime-product discrepancy written on the right. -/
theorem eventually_u8_original_fifth_rho0
    (epsilon : ℝ) (hε : 0 < epsilon) (hεone : epsilon ≤ 1)
    (hεr : epsilon ^ 2 ≤ (19 / 96 : ℝ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
        (J4 : Finset (Fin 4 → Fin (m + 1)))
        (cap4 : (Fin 4 → Fin (m + 1)) → ℚ)
        (J5 : Finset (Fin 5 → Fin (m + 1)))
        (cap5 : (Fin 5 → Fin (m + 1)) → ℚ)
        (cap : ℕ),
        (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
          let Q := P1OriginalHistoricalPhysicalCoefficient.physicalModuli
            e chi m omega J4 cap4 J5 cap5 N cap
              ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ))
          let rho := P1OriginalHistoricalPhysicalCoefficient.rho
            e chi m omega J4 cap4 J5 cap5 N cap
              ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ))
              ((N : ℝ) ^ epsilon)
          currentChenUpsilon8 N ≤
            p5z_labelledMass (Finset.range N)
              (P5U8SharpKSource.productWeight N) *
                physicalDensitySum Q rho +
            p5z_labelledCoprimeCorrection (Finset.range N) id
              (P5U8SharpKSource.productWeight N) Q rho +
            Part3.primeProductSignedError 3 N N Q rho
              (P5U8SharpKSource.physicalWeight N) +
            δ * singularNormalization N := by
  filter_upwards
    [P3ActualU8AttachedPhysical.eventually_u8_at_manuscript_rho0
      epsilon hε hεone hεr δ hδ]
    with N hN e chi m omega J4 cap4 J5 cap5 cap hcap
  let retain : ℕ → List ℕ → Bool :=
    fun _ => (P1OriginalHistoricalPhysicalCoefficient.finalPolicy
      e chi m omega J4 cap4 J5 cap5 (N : ℝ)) false
  let capFn : ℕ → ℕ := fun _ => cap
  have h := hN retain capFn (by simpa only [capFn] using hcap)
  dsimp [attachedUpperModuli, attachedUpperCoefficient,
    P1OriginalHistoricalPhysicalCoefficient.physicalModuli,
    P1OriginalHistoricalPhysicalCoefficient.rho, retain, capFn] at h ⊢
  simpa only [one_mul] using h

end

end ImbalancedChen.P3ActualU8OriginalFifthPolicyPP
