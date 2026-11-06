import ImbalancedChen.P3FourierAutomaticMeasurability
import ImbalancedChen.P3FourierBoxTailAlgebra
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.Linarith

/-!
P3.6 manuscript section 4 (F). SOURCE_ONLY, UNCOMPILED, KERNEL_UNVERIFIED.
Actual physical frequency xi = 2*pi*eta, and the original Point d
and Euclidean Fourier Haar volume. Use the half-open box (-H,H]
so the complement is exactly Iic (-H) union Ioi H.
No W_T admission, Fourier truncation error or arithmetic PP is claimed.
-/

namespace ImbalancedChen.P3FourierRestrictedBox
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
open P3AffineTransitionJets P3FourierPointCoordinateBridge
open P3FourierPhysicalMeasureD P3FourierProductFubini
open P3FourierCauchyAxis P3FourierBoxTailAlgebra

/-- A genuine restricted one-axis function, not just a scalar budget. -/
def scaledAxisInside (H eta : ℝ) : ℝ :=
  ((Set.Ioc (-H) H).indicator axisKernel) (2 * Real.pi * eta)

/-- Actual Cauchy set integral on the unscaled interval. -/
theorem unscaled_inside_mass (H : ℝ) (hH : 0 ≤ H) :
    (∫ xi in Set.Ioc (-H) H, axisKernel xi) =
      Real.pi - axisPairTail H := by
  have hc : (Set.Ioc (-H) H)ᶜ =
      Set.Iic (-H) ∪ Set.Ioi H := by
    ext xi
    simp only [Set.mem_compl_iff, Set.mem_Ioc, Set.mem_union,
      Set.mem_Iic, Set.mem_Ioi]
    constructor
    · intro hx
      rcases not_and_or.mp hx with hl | hr
      · exact Or.inl (le_of_not_gt hl)
      · exact Or.inr (lt_of_not_ge hr)
    · rintro (hl | hr) hx
      · exact not_lt_of_ge hl hx.1
      · exact not_le_of_gt hr hx.2
  have hd : Disjoint (Set.Iic (-H)) (Set.Ioi H) := by
    apply Set.disjoint_left.mpr
    intro xi hl hr
    have hl' : xi ≤ -H := hl
    have hr' : H < xi := hr
    linarith
  have ht : (∫ xi in (Set.Ioc (-H) H)ᶜ, axisKernel xi) =
      axisPairTail H := by
    rw [hc]
    change (∫ xi in Set.Iic (-H) ∪ Set.Ioi H, axisKernel xi) =
      (∫ xi in Set.Iic (-H), axisKernel xi) +
      (∫ xi in Set.Ioi H, axisKernel xi)
    exact setIntegral_union hd measurableSet_Ioi
      axisKernel_integrable.integrableOn
      axisKernel_integrable.integrableOn
  have hp := integral_add_compl (s := Set.Ioc (-H) H)
    (f := axisKernel) measurableSet_Ioc axisKernel_integrable
  rw [ht, axisKernel_full_mass] at hp
  linarith

/-- Exact 2*pi frequency change of variables, preserving the endpoint
convention and the true Lebesgue integral. -/
theorem scaledAxisInside_mass (H : ℝ) (hH : 0 ≤ H) :
    (∫ eta : ℝ, scaledAxisInside H eta) =
      normalizedAxisInside H := by
  have hp : 0 < (2 * Real.pi : ℝ) := by positivity
  have hs := Measure.integral_comp_mul_left
    ((Set.Ioc (-H) H).indicator axisKernel) (2 * Real.pi)
  rw [abs_of_pos (inv_pos.mpr hp), smul_eq_mul] at hs
  change (∫ eta : ℝ, scaledAxisInside H eta) =
    (2 * Real.pi)⁻¹ *
      (∫ xi : ℝ, ((Set.Ioc (-H) H).indicator axisKernel) xi) at hs
  rw [integral_indicator measurableSet_Ioc,
    unscaled_inside_mass H hH] at hs
  calc
    (∫ eta : ℝ, scaledAxisInside H eta) =
      (2 * Real.pi)⁻¹ * (Real.pi - axisPairTail H) := hs
    _ = normalizedAxisInside H := by
      unfold normalizedAxisInside normalizedAxisRemoved
      have hne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp
      <;> ring

/-- The restricted function is genuinely Lebesgue integrable. -/
theorem scaledAxisInside_integrable (H : ℝ) :
    Integrable (scaledAxisInside H) := by
  have hf : Integrable
      ((Set.Ioc (-H) H).indicator axisKernel) :=
    axisKernel_integrable.integrableOn.integrable_indicator measurableSet_Ioc
  have hn : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (by positivity)
  change Integrable (fun eta : ℝ =>
    ((Set.Ioc (-H) H).indicator axisKernel) (2 * Real.pi * eta))
  exact (integrable_comp_mul_left_iff _ hn).2 hf

/-- Original Point coordinates and original physical Cauchy factors. -/
def pointInsideKernel (d : ℕ) (H : ℝ) (p : Point d) : ℝ :=
  ∏ i : Fin d, scaledAxisInside H (p i)

def pointBox (d : ℕ) (H : ℝ) : Set (Point d) :=
  ⋂ i : Fin d, {p : Point d |
    (2 * Real.pi * p i) ∈ Set.Ioc (-H) H}

theorem pointBox_measurable (d : ℕ) (H : ℝ) :
    MeasurableSet (pointBox d H) := by
  unfold pointBox
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_Ioc.preimage
    (measurable_const.mul (measurable_pi_apply i))

/-- Pointwise identification with the *actual* box indicator. -/
theorem pointInsideKernel_eq_indicator (d : ℕ) (H : ℝ)
    (p : Point d) :
    pointInsideKernel d H p =
      (pointBox d H).indicator (pointKernel d) p := by
  classical
  by_cases h : p ∈ pointBox d H
  · rw [Set.indicator_of_mem h]
    have hm : ∀ i : Fin d,
        (2 * Real.pi * p i) ∈ Set.Ioc (-H) H := by
      simpa only [pointBox, Set.mem_iInter, Set.mem_setOf_eq] using h
    unfold pointInsideKernel pointKernel
    apply Finset.prod_congr rfl
    intro i hi
    simp only [scaledAxisInside, Set.indicator_of_mem (hm i)]
  · rw [Set.indicator_of_notMem h]
    have hm : ∃ i : Fin d,
        (2 * Real.pi * p i) ∉ Set.Ioc (-H) H := by
      simpa only [pointBox, Set.mem_iInter, Set.mem_setOf_eq,
        not_forall] using h
    obtain ⟨i, hi⟩ := hm
    unfold pointInsideKernel
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [scaledAxisInside, Set.indicator_of_notMem hi]

/-- Finite Fubini with the same genuine product volume, including d=0. -/
theorem pointInsideKernel_mass (d : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    (∫ p : Point d, pointInsideKernel d H p) =
      (normalizedAxisInside H) ^ d := by
  have hf := integral_fintype_prod_volume_eq_pow
    (ι := Fin d) (f := scaledAxisInside H)
  change (∫ p : Point d, ∏ i : Fin d, scaledAxisInside H (p i)) =
    (normalizedAxisInside H) ^ d
  rw [hf, scaledAxisInside_mass H hH, Fintype.card_fin]

theorem pointBox_mass (d : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    (∫ p in pointBox d H, pointKernel d p) =
      (normalizedAxisInside H) ^ d := by
  calc
    (∫ p in pointBox d H, pointKernel d p) =
        ∫ p : Point d, (pointBox d H).indicator (pointKernel d) p :=
      (integral_indicator (pointBox_measurable d H)).symm
    _ = ∫ p : Point d, pointInsideKernel d H p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p =>
        (pointInsideKernel_eq_indicator d H p).symm)
    _ = (normalizedAxisInside H) ^ d :=
      pointInsideKernel_mass d H hH

/-- Transfer the actual physical H-box by the previous isometric chart. -/
def fourierBox (d : ℕ) (H : ℝ) : Set (FourierSpace d) :=
  (chartEquiv d) ⁻¹' pointBox d H

theorem fourierBox_measurable (d : ℕ) (H : ℝ) :
    MeasurableSet (fourierBox d H) := by
  exact (pointBox_measurable d H).preimage
    (chartEquiv d).continuous.measurable

theorem fourierBox_mass (d : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    (∫ eta in fourierBox d H, fourierKernel d eta) =
      (normalizedAxisInside H) ^ d := by
  have hident : ∀ eta : FourierSpace d,
      (fourierBox d H).indicator (fourierKernel d) eta =
        (pointBox d H).indicator (pointKernel d)
          (chartEquiv d eta) := by
    intro eta
    by_cases h : chartEquiv d eta ∈ pointBox d H
    · simp [fourierBox, fourierKernel, h]
    · simp [fourierBox, fourierKernel, h]
  calc
    (∫ eta in fourierBox d H, fourierKernel d eta) =
        ∫ eta : FourierSpace d,
          (fourierBox d H).indicator (fourierKernel d) eta :=
      (integral_indicator (fourierBox_measurable d H)).symm
    _ = ∫ eta : FourierSpace d,
        (pointBox d H).indicator (pointKernel d)
          (chartEquiv d eta) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hident
    _ = ∫ p : Point d, (pointBox d H).indicator (pointKernel d) p :=
      integral_chart d ((pointBox d H).indicator (pointKernel d))
    _ = (normalizedAxisInside H) ^ d := by
      rw [integral_indicator (pointBox_measurable d H)]
      exact pointBox_mass d H hH

/-- The genuine Fourier-space H-box complement mass: no scalar surrogate. -/
theorem fourierBox_complement_mass (d : ℕ) (H : ℝ)
    (hH : 0 ≤ H) :
    (∫ eta in (fourierBox d H)ᶜ, fourierKernel d eta) =
      separatedBoxMassLoss d H := by
  calc
    (∫ eta in (fourierBox d H)ᶜ, fourierKernel d eta) =
        (∫ eta : FourierSpace d, fourierKernel d eta) -
        (∫ eta in fourierBox d H, fourierKernel d eta) :=
      setIntegral_compl (fourierBox_measurable d H)
        (fourierKernel_integrable d)
    _ = separatedBoxMassLoss d H := by
      rw [fourierKernel_mass, fourierBox_mass d H hH]
      rfl

/-- Dimension-linear mass loss with physical cutoff H, no H^d factor. -/
theorem fourierBox_complement_le_dim_div (d : ℕ) (H : ℝ)
    (hH : 0 < H) :
    (∫ eta in (fourierBox d H)ᶜ, fourierKernel d eta) ≤
      (d : ℝ) / H := by
  rw [fourierBox_complement_mass d H hH.le]
  exact separatedBoxMassLoss_le_dim_div d hH

end
end ImbalancedChen.P3FourierRestrictedBox
