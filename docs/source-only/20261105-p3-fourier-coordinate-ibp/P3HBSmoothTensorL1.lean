import ImbalancedChen.P3HBSmoothLogTensorRestoration
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Constructions.Pi

/-!
P3.6 — genuine six-dimensional L1/Fubini bridge for the ORIGINAL
three-way smooth HB logarithmic subweights.

SOURCE_ONLY / NOT ELABORATED / KERNEL_UNVERIFIED.
Frozen manuscript: chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §2 and §4 (F).
Pinned Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

Unlike the previous pointwise 729-child C_K^6 estimate, this file pays
actual Lebesgue integrability and an EXACT six-axis product-measure L1
factorization, then integrates the entire original 3^6 labelled family.
The resulting formula is valid for the literal dyadic-labelled family
because the normalized log-coordinate functions agree identically.

This is a SEPARATED HB subweight L1 calculation: it neither asserts
that a coupled physical W_T mixed derivative factors, nor pays the
full W_T U5/trim mixed norm, Fourier H-tail, arithmetic discrepancy,
exceptional complete product T, or complete same-rho PP.
-/

namespace ImbalancedChen.P3HBSmoothTensorL1
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothLogScaleBudget
open ImbalancedChen.P3HBLogDerivativeGlobalSupport
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo

/-- Every finite derivative of an actual original three-way HB log child
is Lebesgue-integrable. This discharges a genuine one-coordinate L1
premise from C-infinity and the EXACT original compact support. -/
theorem logChild_derivative_integrable
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (a : Fin 3) (k : ℕ) :
    Integrable (iteratedDeriv k (logChild chi a)) := by
  have hc : Continuous (iteratedDeriv k (logChild chi a)) :=
    (logChild_contDiff chi hchi a).continuous_iteratedDeriv k le_top
  have hs : HasCompactSupport (iteratedDeriv k (logChild chi a)) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (logChild_iteratedDeriv_support_subset chi a k hsmall hlarge)
  exact hc.integrable_of_hasCompactSupport hs

/-- The SIX original coordinate derivative norms form a genuinely
integrable function on the standard Lebesgue product chart. No abstract
integrability interface or changed support family is assumed. -/
theorem logTensorMixed_norm_integrable
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3) :
    Integrable (fun u : Fin 6 → ℝ =>
      ‖logTensorMixed chi orders child u‖) := by
  have haxis : ∀ i : Fin 6,
      Integrable (fun t : ℝ =>
        ‖iteratedDeriv (orders i) (logChild chi (child i)) t‖) := by
    intro i
    exact (logChild_derivative_integrable chi hchi hsmall hlarge
      (child i) (orders i)).norm
  have hpi :
      Integrable (fun u : Fin 6 → ℝ =>
        ∏ i : Fin 6,
          ‖iteratedDeriv (orders i) (logChild chi (child i)) (u i)‖)
        (Measure.pi (fun _ : Fin 6 => (volume : Measure ℝ))) :=
    Integrable.fintype_prod haxis
  have hvol :
      Integrable (fun u : Fin 6 → ℝ =>
        ∏ i : Fin 6,
          ‖iteratedDeriv (orders i) (logChild chi (child i)) (u i)‖) := by
    simpa only [volume_pi] using hpi
  simpa only [logTensorMixed, norm_prod] using hvol

/-- EXACT six-dimensional absolute L1 mass, with all six ORIGINAL
positions and derivatives. The product volume is the real chart volume,
not a fabricated substitute integration measure. -/
theorem logTensorMixed_norm_integral_eq_prod
    (chi : ℝ → ℂ) (orders : Fin 6 → ℕ)
    (child : Fin 6 → Fin 3) :
    (∫ u : Fin 6 → ℝ, ‖logTensorMixed chi orders child u‖) =
      ∏ i : Fin 6,
        (∫ t : ℝ,
          ‖iteratedDeriv (orders i) (logChild chi (child i)) t‖) := by
  simpa only [logTensorMixed, norm_prod] using
    (integral_fintype_prod_volume_eq_prod
      (ι := Fin 6)
      (f := fun i : Fin 6 => fun t : ℝ =>
        ‖iteratedDeriv (orders i) (logChild chi (child i)) t‖))

/-- The entire 3^6 LABELLED absolute tensor cost is Lebesgue-integrable,
including repeated slots and arbitrary finite derivative orders. -/
theorem all_logTensorMixed_children_norm_integrable
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (orders : Fin 6 → ℕ) :
    Integrable (fun u : Fin 6 → ℝ =>
      ∑ child ∈ smoothChildren, ‖logTensorMixed chi orders child u‖) := by
  apply integrable_finsetSum smoothChildren
  intro child _
  exact logTensorMixed_norm_integrable chi hchi hsmall hlarge orders child

/-- Genuine Fubini and finite integration/sum exchange for the original
729 positional smooth children. Every summand is proved integrable
above, rather than postulating absolute Fourier convergence. -/
theorem all_logTensorMixed_children_norm_integral_eq
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (orders : Fin 6 → ℕ) :
    (∫ u : Fin 6 → ℝ,
      ∑ child ∈ smoothChildren, ‖logTensorMixed chi orders child u‖) =
      ∑ child ∈ smoothChildren,
        ∏ i : Fin 6,
          (∫ t : ℝ,
            ‖iteratedDeriv (orders i) (logChild chi (child i)) t‖) := by
  have hparts : ∀ child ∈ smoothChildren,
      Integrable (fun u : Fin 6 → ℝ =>
        ‖logTensorMixed chi orders child u‖) := by
    intro child _
    exact logTensorMixed_norm_integrable chi hchi hsmall hlarge orders child
  calc
    (∫ u : Fin 6 → ℝ,
      ∑ child ∈ smoothChildren, ‖logTensorMixed chi orders child u‖) =
        ∑ child ∈ smoothChildren,
          (∫ u : Fin 6 → ℝ, ‖logTensorMixed chi orders child u‖) := by
            exact integral_finsetSum smoothChildren hparts
    _ = ∑ child ∈ smoothChildren,
        ∏ i : Fin 6,
          (∫ t : ℝ,
            ‖iteratedDeriv (orders i) (logChild chi (child i)) t‖) := by
          apply Finset.sum_congr rfl
          intro child _
          exact logTensorMixed_norm_integral_eq_prod chi orders child

/-- Same EXACT integrated budget for literal dyadic labels, not a
different or silently reweighted prime source. The reduction uses the
previous equality of every finite derivative in the normalized log chart. -/
theorem all_scaledTensorMixed_children_norm_integral_eq
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (label orders : Fin 6 → ℕ) :
    (∫ u : Fin 6 → ℝ,
      ∑ child ∈ smoothChildren,
        ‖scaledTensorMixed chi label orders child u‖) =
      ∑ child ∈ smoothChildren,
        ∏ i : Fin 6,
          (∫ t : ℝ,
            ‖iteratedDeriv (orders i) (logChild chi (child i)) t‖) := by
  simp_rw [scaledTensorMixed_eq_logTensorMixed]
  exact all_logTensorMixed_children_norm_integral_eq
    chi hchi hsmall hlarge orders

end
end ImbalancedChen.P3HBSmoothTensorL1
