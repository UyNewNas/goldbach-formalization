import ImbalancedChen.CurrentChenBuchstabRefinement
import ImbalancedChen.CurrentNumericalTransfer
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Original U7 exponent geometry and actual Buchstab integral dictionary

The original exponent region is d <= t <= u < (1-t)/2, d=59/250.
Its argument (1-t-u)/u lies in (1,132/59], not in a Buchstab tail.
The closed envelope is used only to include integration endpoints.
The two actual Buchstab formulas meet at u=(1-t)/3, where s=2.

The displayed integral is a genuine integral of the actual Buchstab
function.  Its explicit elementary dictionary is proved pointwise and
under both integrals.  No arithmetic mean, sharp coefficient estimate,
same-rho distribution supplier, or numerical certificate is assumed.
Source only; no compiler or runtime was invoked.
-/

namespace ImbalancedChen

noncomputable section

open Set MeasureTheory LiLiuPrereqBuchstab

def p5U7OmegaSupport (t u : ℝ) : Prop :=
  (59 / 250 : ℝ) ≤ t ∧ t ≤ u ∧ u < (1 - t) / 2

def p5U7OmegaClosedSupport (t u : ℝ) : Prop :=
  (59 / 250 : ℝ) ≤ t ∧ t ≤ u ∧ u ≤ (1 - t) / 2

def p5U7OmegaArgument (t u : ℝ) : ℝ := (1 - t - u) / u

/-- The closed integration envelope has positive denominators everywhere. -/
theorem p5U7Omega_closed_geometry {t u : ℝ} (h : p5U7OmegaClosedSupport t u) :
    0 < t ∧ 0 < u ∧ 0 < 1 - t - u ∧ t ≤ (1 / 3 : ℝ) ∧
      1 ≤ p5U7OmegaArgument t u ∧ p5U7OmegaArgument t u ≤ (132 / 59 : ℝ) := by
  obtain ⟨ht, htu, hu⟩ := h
  have htpos : 0 < t := by linarith
  have hup : 0 < u := htpos.trans_le htu
  refine ⟨htpos, hup, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · apply (le_div_iff₀ hup).mpr
    linarith
  · apply (div_le_iff₀ hup).mpr
    nlinarith only [ht, htu]

/-- The original upper wall is strict. The maximum argument is inclusive. -/
theorem p5U7Omega_strict_geometry {t u : ℝ} (h : p5U7OmegaSupport t u) :
    (59 / 250 : ℝ) ≤ t ∧ t < (1 / 3 : ℝ) ∧
      1 < p5U7OmegaArgument t u ∧ p5U7OmegaArgument t u ≤ (132 / 59 : ℝ) := by
  have hc : p5U7OmegaClosedSupport t u := ⟨h.1, h.2.1, h.2.2.le⟩
  have hg := p5U7Omega_closed_geometry hc
  refine ⟨h.1, ?_, ?_, hg.2.2.2.2.2⟩
  · linarith [h.2.1, h.2.2]
  · apply (lt_div_iff₀ hg.2.1).mpr
    linarith [h.2.2]

/-- Equality in the upper argument bound really occurs in the strict region. -/
theorem p5U7Omega_maximum_attained :
    p5U7OmegaSupport (59 / 250) (59 / 250) ∧
      p5U7OmegaArgument (59 / 250) (59 / 250) = (132 / 59 : ℝ) := by
  norm_num [p5U7OmegaSupport, p5U7OmegaArgument]

theorem p5U7Omega_argument_le_two_iff {t u : ℝ}
    (h : p5U7OmegaClosedSupport t u) :
    p5U7OmegaArgument t u ≤ 2 ↔ (1 - t) / 3 ≤ u := by
  have hup := (p5U7Omega_closed_geometry h).2.1
  constructor
  · intro hs
    have hs' := (div_le_iff₀ hup).mp hs
    linarith
  · intro hu
    apply (div_le_iff₀ hup).mpr
    linarith

theorem p5U7Omega_argument_gt_two_iff {t u : ℝ}
    (h : p5U7OmegaClosedSupport t u) :
    2 < p5U7OmegaArgument t u ↔ u < (1 - t) / 3 := by
  have he := p5U7Omega_argument_le_two_iff h
  constructor
  · intro hs
    by_contra hnot
    exact (not_le_of_gt hs) (he.mpr (le_of_not_gt hnot))
  · intro hu
    exact lt_of_not_ge (fun hs => (not_le_of_gt hu) (he.mp hs))

/-- Complete disjoint segment classification with the literal strict and
inclusive endpoints, including the attainable upper endpoint 132/59. -/
theorem p5U7Omega_strict_segment_partition {t u : ℝ}
    (h : p5U7OmegaSupport t u) :
    ((1 - t) / 3 ≤ u ∧ 1 < p5U7OmegaArgument t u ∧
      p5U7OmegaArgument t u ≤ 2) ∨
    (u < (1 - t) / 3 ∧ 2 < p5U7OmegaArgument t u ∧
      p5U7OmegaArgument t u ≤ (132 / 59 : ℝ)) := by
  have hc : p5U7OmegaClosedSupport t u := ⟨h.1, h.2.1, h.2.2.le⟩
  have hg := p5U7Omega_strict_geometry h
  by_cases hu : (1 - t) / 3 ≤ u
  · exact Or.inl ⟨hu, hg.2.2.1, (p5U7Omega_argument_le_two_iff hc).mpr hu⟩
  · have hu' := lt_of_not_ge hu
    exact Or.inr ⟨hu', (p5U7Omega_argument_gt_two_iff hc).mpr hu', hg.2.2.2⟩

/-- The integration domain is exactly the closed original triangle. -/
theorem p5U7Omega_closed_support_iff_nested {t u : ℝ} :
    p5U7OmegaClosedSupport t u ↔
      t ∈ Icc (59 / 250 : ℝ) (1 / 3) ∧ u ∈ Icc t ((1 - t) / 2) := by
  constructor
  · intro h
    exact ⟨⟨h.1, (p5U7Omega_closed_geometry h).2.2.2.1⟩, h.2⟩
  · rintro ⟨ht, hu⟩
    exact ⟨ht.1, hu.1, hu.2⟩

/-- The second segment is absent for t >= 1/4. -/
theorem p5U7Omega_second_segment_outer_lt_quarter {t u : ℝ}
    (h : p5U7OmegaClosedSupport t u) (hu : u < (1 - t) / 3) :
    t < (1 / 4 : ℝ) := by
  linarith [h.2.1]

/-- The exact dividing wall belongs to the first formula. -/
theorem p5U7Omega_argument_at_split {t : ℝ} (ht : t < 1) :
    p5U7OmegaArgument t ((1 - t) / 3) = 2 := by
  unfold p5U7OmegaArgument
  have hne : 1 - t ≠ 0 := ne_of_gt (by linarith)
  field_simp [hne]
  <;> ring

theorem p5U7Omega_buchstab_first {t u : ℝ}
    (h : p5U7OmegaClosedSupport t u) (hu : (1 - t) / 3 ≤ u) :
    buchstab (p5U7OmegaArgument t u) = 1 / p5U7OmegaArgument t u := by
  exact buchstab_eq_one_div (p5U7Omega_closed_geometry h).2.2.2.2.1
    ((p5U7Omega_argument_le_two_iff h).mpr hu)

theorem p5U7Omega_buchstab_second {t u : ℝ}
    (h : p5U7OmegaClosedSupport t u) (hu : u < (1 - t) / 3) :
    buchstab (p5U7OmegaArgument t u) =
      (1 + Real.log (p5U7OmegaArgument t u - 1)) / p5U7OmegaArgument t u := by
  have hs2 := (p5U7Omega_argument_gt_two_iff h).mpr hu
  have hsmax := (p5U7Omega_closed_geometry h).2.2.2.2.2
  exact buchstab_eq_log_div hs2.le (hsmax.trans (by norm_num))

def p5U7OmegaKernel (K t u : ℝ) : ℝ :=
  K * buchstab (p5U7OmegaArgument t u) / (t * u ^ 2)

def p5U7OmegaFirstKernel (K t u : ℝ) : ℝ := K / (t * u * (1 - t - u))

def p5U7OmegaSecondKernel (K t u : ℝ) : ℝ :=
  K * (1 + Real.log ((1 - t - 2 * u) / u)) / (t * u * (1 - t - u))

/-- Exact first-segment dictionary, including s=1 and s=2. -/
theorem p5U7Omega_kernel_first (K : ℝ) {t u : ℝ}
    (h : p5U7OmegaClosedSupport t u) (hu : (1 - t) / 3 ≤ u) :
    p5U7OmegaKernel K t u = p5U7OmegaFirstKernel K t u := by
  have hg := p5U7Omega_closed_geometry h
  rw [p5U7OmegaKernel, p5U7Omega_buchstab_first h hu]
  dsimp [p5U7OmegaArgument, p5U7OmegaFirstKernel]
  field_simp [hg.1.ne', hg.2.1.ne', hg.2.2.1.ne']
  <;> ring

/-- Exact second-segment dictionary; its logarithm has positive argument. -/
theorem p5U7Omega_kernel_second (K : ℝ) {t u : ℝ}
    (h : p5U7OmegaClosedSupport t u) (hu : u < (1 - t) / 3) :
    1 < (1 - t - 2 * u) / u ∧
      p5U7OmegaKernel K t u = p5U7OmegaSecondKernel K t u := by
  have hg := p5U7Omega_closed_geometry h
  have harg : p5U7OmegaArgument t u - 1 = (1 - t - 2 * u) / u := by
    dsimp [p5U7OmegaArgument]
    field_simp [hg.2.1.ne']
    <;> ring
  refine ⟨?_, ?_⟩
  · rw [← harg]
    have hs := (p5U7Omega_argument_gt_two_iff h).mpr hu
    linarith
  · rw [p5U7OmegaKernel, p5U7Omega_buchstab_second h hu, harg]
    dsimp [p5U7OmegaArgument, p5U7OmegaSecondKernel]
    field_simp [hg.1.ne', hg.2.1.ne', hg.2.2.1.ne']
    <;> ring

/-- Both elementary formulas agree at the exact s=2 wall. -/
theorem p5U7Omega_kernels_agree_at_split (K : ℝ) {t : ℝ} (ht : t < 1) :
    p5U7OmegaSecondKernel K t ((1 - t) / 3) =
      p5U7OmegaFirstKernel K t ((1 - t) / 3) := by
  have hne : 1 - t ≠ 0 := ne_of_gt (by linarith)
  have hlogarg : (1 - t - 2 * ((1 - t) / 3)) / ((1 - t) / 3) = 1 := by
    field_simp [hne]
    <;> ring
  simp only [p5U7OmegaSecondKernel, p5U7OmegaFirstKernel, hlogarg,
    Real.log_one, add_zero, mul_one]

theorem p5U7Omega_kernel_nonneg {K t u : ℝ} (hK : 0 ≤ K)
    (h : p5U7OmegaClosedSupport t u) : 0 ≤ p5U7OmegaKernel K t u := by
  have hg := p5U7Omega_closed_geometry h
  have hb : 0 ≤ buchstab (p5U7OmegaArgument t u) :=
    (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (one_half_le_buchstab hg.2.2.2.2.1)
  exact div_nonneg (mul_nonneg hK hb) (mul_nonneg hg.1.le (sq_nonneg u))

/-- Continuity is for the actual Buchstab kernel on the positive quadrant,
and therefore includes both sides of the branch seam. -/
theorem p5U7Omega_kernel_continuousOn_positive (K : ℝ) :
    ContinuousOn (fun x : ℝ × ℝ => p5U7OmegaKernel K x.1 x.2)
      {x | 0 < x.1 ∧ 0 < x.2} := by
  have hs : ContinuousOn (fun x : ℝ × ℝ => p5U7OmegaArgument x.1 x.2)
      {x | 0 < x.1 ∧ 0 < x.2} :=
    ((continuousOn_const.sub continuous_fst.continuousOn).sub
      continuous_snd.continuousOn).div continuous_snd.continuousOn
      (fun x hx => hx.2.ne')
  exact (continuousOn_const.mul (continuous_buchstab.comp_continuousOn hs)).div
    (continuous_fst.continuousOn.mul (continuous_snd.continuousOn.pow 2))
    (fun x hx => mul_ne_zero hx.1.ne' (pow_ne_zero 2 hx.2.ne'))

theorem p5U7Omega_kernel_continuousOn_closed (K : ℝ) :
    ContinuousOn (fun x : ℝ × ℝ => p5U7OmegaKernel K x.1 x.2)
      {x | p5U7OmegaClosedSupport x.1 x.2} := by
  apply (p5U7Omega_kernel_continuousOn_positive K).mono
  intro x hx
  exact ⟨(p5U7Omega_closed_geometry hx).1, (p5U7Omega_closed_geometry hx).2.1⟩

theorem p5U7Omega_row_intervalIntegrable (K : ℝ) {t : ℝ}
    (ht : t ∈ Icc (59 / 250 : ℝ) (1 / 3)) :
    IntervalIntegrable (fun u => p5U7OmegaKernel K t u) volume t ((1 - t) / 2) := by
  have htpos : 0 < t := by linarith [ht.1]
  have hle : t ≤ (1 - t) / 2 := by linarith [ht.2]
  have hc : ContinuousOn (fun u => p5U7OmegaKernel K t u) (Icc t ((1 - t) / 2)) :=
    (p5U7Omega_kernel_continuousOn_positive K).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu => ⟨htpos, htpos.trans_le hu.1⟩)
  exact ContinuousOn.intervalIntegrable_of_Icc hle hc

/-- The genuine original U7 functional, before any arithmetic mean theorem. -/
def p5U7OriginalOmegaIntegral (K : ℝ) : ℝ :=
  ∫ t in (59 / 250 : ℝ)..(1 / 3 : ℝ),
    ∫ u in t..((1 - t) / 2), p5U7OmegaKernel K t u

/-- Its elementary dictionary chooses the s<=2 formula at the seam. -/
def p5U7OriginalElementaryIntegral (K : ℝ) : ℝ :=
  ∫ t in (59 / 250 : ℝ)..(1 / 3 : ℝ),
    ∫ u in t..((1 - t) / 2),
      if (1 - t) / 3 ≤ u then p5U7OmegaFirstKernel K t u
      else p5U7OmegaSecondKernel K t u

theorem p5U7OriginalOmegaIntegral_eq_elementary (K : ℝ) :
    p5U7OriginalOmegaIntegral K = p5U7OriginalElementaryIntegral K := by
  unfold p5U7OriginalOmegaIntegral p5U7OriginalElementaryIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (59 / 250 : ℝ) ≤ 1 / 3)] at ht
  apply intervalIntegral.integral_congr
  intro u hu
  have hle : t ≤ (1 - t) / 2 := by linarith [ht.2]
  rw [uIcc_of_le hle] at hu
  have h : p5U7OmegaClosedSupport t u := ⟨ht.1, hu.1, hu.2⟩
  by_cases hcut : (1 - t) / 3 ≤ u
  · rw [if_pos hcut]
    exact p5U7Omega_kernel_first K h hcut
  · rw [if_neg hcut]
    exact (p5U7Omega_kernel_second K h (lt_of_not_ge hcut)).2

/-- The fixed manuscript K is kept literally, with no new normalization. -/
def p5U7CurrentOriginalOmegaIntegral : ℝ := p5U7OriginalOmegaIntegral currentK

theorem p5U7CurrentOriginalOmegaIntegral_dictionary :
    p5U7CurrentOriginalOmegaIntegral = p5U7OriginalElementaryIntegral currentK := by
  exact p5U7OriginalOmegaIntegral_eq_elementary currentK

theorem p5U7CurrentOmega_kernel_nonneg {t u : ℝ}
    (h : p5U7OmegaClosedSupport t u) : 0 ≤ p5U7OmegaKernel currentK t u := by
  exact p5U7Omega_kernel_nonneg (by norm_num [currentK]) h

end

end ImbalancedChen
