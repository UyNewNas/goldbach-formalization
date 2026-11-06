import ImbalancedChen.P3FourierCoordinateIBP
import ImbalancedChen.P3OriginalWIntegratedDerivative
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
P3.6 / MANUSCRIPT-INTERNAL / SOURCE_ONLY / UNCOMPILED.

The actual product-volume chart between the ORIGINAL Point d and the
Euclidean Fourier domain is measure preserving, not merely a linear
coordinate bijection. This file transfers the literal doubled-mixed
derivative L1 ledger `originalWD` to the genuine Fourier `derivativeD`,
and then pays the conditional physical-frequency numerator using the
previous primitive integrated original-W source bound.

No physical W_T family membership or smoothness is invented here.
No modulus, rho, auxiliary level, source label, or arithmetic estimate
is changed. No Fourier-tail or distribution theorem is asserted.
-/

namespace ImbalancedChen.P3FourierPhysicalMeasureD
noncomputable section

open MeasureTheory
open scoped Classical BigOperators FourierTransform RealInnerProductSpace
open P3AffineTransitionJets P3U5ChartMixedL1Budget
open P3U5OriginalWMixedL1 P3OriginalWIntegratedDerivative
open P3FourierDPointwise P3FourierRealComplex
open P3FourierPointCoordinateBridge P3FourierCoordinateIBP
open P3PhysicalOriginalW

/-- Pinned mathlib: PiLp.volume_preserving_ofLp.
For Point d = Fin d → Real the old chart and the Fourier Euclidean
chart have EXACTLY equal volume, including d=0. No Jacobian factor. -/
theorem chart_measure_preserving (d : ℕ) :
    MeasurePreserving (chartEquiv d) := by
  change MeasurePreserving
    (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ))
  exact PiLp.volume_preserving_ofLp (Fin d)

/-- Exact transfer for arbitrary real test functions, without imposing an
unneeded integrability assumption (both sides are Bochner integrals). -/
theorem integral_chart (d : ℕ) (f : Point d → ℝ) :
    (∫ x : FourierSpace d, f (chartEquiv d x)) =
      ∫ p : Point d, f p := by
  exact (chart_measure_preserving d).integral_comp
    (chartEquiv d).toHomeomorph.measurableEmbedding f

/-- The literal old ordered doubled mixed derivative has the same L1
integral as its actual complex-cast Euclidean Fourier-space function.
This is an identity of measures and integrands, not a D-bound premise. -/
theorem mixed_L1_chart {d : ℕ}
    (w : Point d → ℝ) (S : Finset (Fin d)) :
    (∫ x : FourierSpace d, ‖actualMixedFamily w S x‖) =
      ∫ p : Point d, |mixed (doubled S) w p| := by
  have hpoint : ∀ x : FourierSpace d,
      ‖actualMixedFamily w S x‖ =
        |mixed (doubled S) w (chartEquiv d x)| := by
    intro x
    change ‖(↑(mixed (doubled S) w
      (chartEquiv d x)) : ℂ)‖ =
        |mixed (doubled S) w (chartEquiv d x)|
    simp only [Complex.norm_real, Real.norm_eq_abs]
  simp_rw [hpoint]
  exact integral_chart d (fun p => |mixed (doubled S) w p|)

/-- No alternative test family: both sides enumerate precisely the same
finset of S and the same actual ordered 2S original derivatives. -/
theorem actual_derivativeD_eq_pointD {d : ℕ} (w : Point d → ℝ) :
    derivativeD d (actualMixedFamily w) =
      ∑ S : Finset (Fin d),
        ∫ p : Point d, |mixed (doubled S) w p| := by
  unfold derivativeD
  apply Finset.sum_congr rfl
  intro S _
  exact mixed_L1_chart w S

/-- The independent originalWD ledger from the old HB physical W module
IS the actual Euclidean Fourier numerator D for the unchanged multiplier. -/
theorem originalWD_eq_actual_derivativeD {d g : ℕ}
    (W : Point d → ℝ) (a ell : ℝ)
    (R : Fin 2 → ℝ) (slot : Fin d → Option (Fin 2))
    (group : Fin d → Fin g) (b : Fin g → ℝ) (trim : ℝ)
    (u : Fin d → ℝ) (v : Fin g → ℝ) (pick : Fin g → Fin d)
    (m : ℕ) (l : Lane) :
    originalWD W a ell R slot group b trim u v pick m l =
      derivativeD d (actualMixedFamily
        (withOriginalW W a ell R slot group b trim u v pick m l)) := by
  unfold originalWD
  exact (actual_derivativeD_eq_pointD
    (withOriginalW W a ell R slot group b trim u v pick m l)).symm

/-- Actual labelled W_T and ALL original HB variables. The only
additional assumptions are (i) the already explicit primitive physical W
integrated class, and (ii) genuine finite-order ContDiff/integrability
needed by the pinned Fourier derivative theorem. Their verification for
the complete original family is NOT supplied by this theorem.

The conclusion is an absolute Fourier pointwise numerator estimate. It
is not yet the truncated PP discrepancy or even an L1 Fourier tail. -/
theorem exists_physicalW_fourier_product_polylog (d g E B : ℕ)
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ,
      1 ≤ Real.log (N : ℝ) →
      ∀ U : Fin d → ℝ, (∀ i, 0 < U i) →
      ∀ W : (Fin g → ℝ) → ℝ,
      ∀ group : Fin d → Fin g,
      ∀ pair : Fin 2 → Fin g, pair 0 ≠ pair 1 →
      ∀ R : Fin 2 → ℝ, ∀ b : Fin g → ℝ,
      ∀ trim : ℝ, ∀ u : Fin d → ℝ, ∀ v : Fin g → ℝ,
      ∀ pick : Fin g → Fin d, ∀ m : ℕ,
      (m+1 : ℝ) ≤ (Real.log (N : ℝ))^B →
      ∀ l : Lane, ∀ A : ℝ, 0 ≤ A →
      PhysicalIntegratedClass W U group (2*d)
        (A*(Real.log (N : ℝ))^E) →
      ∀ (hsmooth : ∀ S : Finset (Fin d),
        ContDiff ℝ ((doubled S).length : ℕ∞)
          (chartLift (withOriginalW (pulledOriginalW W U group) a
            (Real.log (N : ℝ)) R
            (P3U5PhysicalProductChart.pairSlots group pair)
            group b trim u v pick m l))),
      (∀ S : Finset (Fin d), ∀ k : ℕ,
        k ≤ (doubled S).length →
          Integrable (iteratedFDeriv ℝ k
            (complexChartLift (withOriginalW (pulledOriginalW W U group) a
              (Real.log (N : ℝ)) R
              (P3U5PhysicalProductChart.pairSlots group pair)
              group b trim u v pick m l)))) →
      ∀ eta : FourierSpace d,
      physicalDenom (physicalFrequency (fun i => eta i)) *
        ‖𝓕 (actualMixedFamily
          (withOriginalW (pulledOriginalW W U group) a
            (Real.log (N : ℝ)) R
            (P3U5PhysicalProductChart.pairSlots group pair)
            group b trim u v pick m l) ∅) eta‖ ≤
        C*A*(Real.log (N : ℝ))^(E+B*(2*d)) := by
  obtain ⟨C, hC, hBudget⟩ :=
    exists_physicalW_integrated_polylog d g E B a ha
  refine ⟨C, hC, ?_⟩
  intro N hN U hU W group pair hpair R b trim u v pick m hm l A hA hW
    hsmooth hintegrable eta
  let w : Point d → ℝ :=
    withOriginalW (pulledOriginalW W U group) a
      (Real.log (N : ℝ)) R
      (P3U5PhysicalProductChart.pairSlots group pair)
      group b trim u v pick m l
  have hmeasure :
      derivativeD d (actualMixedFamily w) =
        originalWD (pulledOriginalW W U group) a
          (Real.log (N : ℝ)) R
          (P3U5PhysicalProductChart.pairSlots group pair)
          group b trim u v pick m l :=
    (originalWD_eq_actual_derivativeD
      (pulledOriginalW W U group) a (Real.log (N : ℝ)) R
      (P3U5PhysicalProductChart.pairSlots group pair)
      group b trim u v pick m l).symm
  have hpoint := actual_mixed_physical_product_bound
    w hsmooth hintegrable eta
  have hb := hBudget N hN U hU W group pair hpair R b trim u v
    pick m hm l A hA hW
  change physicalDenom (physicalFrequency (fun i => eta i)) *
    ‖𝓕 (actualMixedFamily w ∅) eta‖ ≤ _
  exact hpoint.trans (hmeasure.le.trans hb)

end
end ImbalancedChen.P3FourierPhysicalMeasureD
