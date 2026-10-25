import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
The missing coordinate factorization for actual exponential-cosh totality:
every continuous compactly supported even complex function on R is
exp(-cosh u) times a continuous function of exp(-cosh u) on [0,exp(-1)].
This is a coordinate theorem, not a totality or Plancherel premise.
-/

noncomputable section

namespace ImbalancedChen.Part3.ActualKCompactCoordinateFactorSourceOnly

open Set

/-- Clamp the inverse coordinate below the positive support threshold.
The denominator never vanishes, including at coordinate zero. -/
def compactCoordinateFactor (R : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  f (Real.arcosh (-Real.log (max x (Real.exp (-Real.cosh R))))) /
    (max x (Real.exp (-Real.cosh R)) : ℂ)

private theorem threshold_le_endpoint (R : ℝ) :
    Real.exp (-Real.cosh R) ≤ Real.exp (-1) :=
  Real.exp_le_exp.mpr (neg_le_neg (Real.one_le_cosh R))

/-- Continuity uses arcosh on [1,infinity); the clamp stays strictly
positive, so no endpoint-zero singularity is hidden. -/
theorem compactCoordinateFactor_continuousOn (R : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) :
    ContinuousOn (compactCoordinateFactor R f) (Icc 0 (Real.exp (-1))) := by
  let δ : ℝ := Real.exp (-Real.cosh R)
  have hδ : 0 < δ := Real.exp_pos _
  have hm : Continuous (fun x : ℝ => max x δ) := continuous_id.max continuous_const
  have hmpos (x : ℝ) : 0 < max x δ := hδ.trans_le (le_max_right x δ)
  have hl : Continuous (fun x : ℝ => -Real.log (max x δ)) :=
    (hm.log (fun x => ne_of_gt (hmpos x))).neg
  have ha : ContinuousOn (fun x : ℝ => Real.arcosh (-Real.log (max x δ)))
      (Icc 0 (Real.exp (-1))) := by
    apply Real.continuousOn_arcosh.comp hl.continuousOn
    intro x hx
    have hb : max x δ ≤ Real.exp (-1) :=
      max_le hx.2 (threshold_le_endpoint R)
    have hlog : Real.log (max x δ) ≤ -1 :=
      (Real.log_le_iff_le_exp (hmpos x)).2 hb
    change 1 ≤ -Real.log (max x δ)
    linarith
  have hfOn : ContinuousOn f (Set.univ : Set ℝ) := hf.continuousOn
  have hn := hfOn.comp ha (fun _ _ => Set.mem_univ _)
  have hd : ContinuousOn (fun x : ℝ => (max x δ : ℂ))
      (Icc 0 (Real.exp (-1))) :=
    (Complex.continuous_ofReal.comp hm).continuousOn
  exact hn.div hd (fun x _ => Complex.ofReal_ne_zero.mpr (ne_of_gt (hmpos x)))

private theorem arcosh_cosh_abs (u : ℝ) : Real.arcosh (Real.cosh u) = |u| := by
  by_cases hu : 0 ≤ u
  · rw [Real.arcosh_cosh hu, abs_of_nonneg hu]
  · have hu' : 0 ≤ -u := by linarith
    rw [← Real.cosh_neg u, Real.arcosh_cosh hu', abs_of_neg (lt_of_not_ge hu)]

/-- Exact factorization from the elementary support-radius condition.
The witness is explicit and has already been proved continuous on the
whole compact coordinate interval, including both endpoints. -/
theorem compactCoordinateFactor_eq {f : ℝ → ℂ}
    (heven : ∀ u : ℝ, f (-u) = f u) {R : ℝ} (hR : 0 ≤ R)
    (hzero : ∀ u : ℝ, R ≤ |u| → f u = 0) (u : ℝ) :
    f u = (Real.exp (-Real.cosh u) : ℂ) *
      compactCoordinateFactor R f (Real.exp (-Real.cosh u)) := by
  have hfu : f |u| = f u := by
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu]
    · rw [abs_of_neg (lt_of_not_ge hu), heven]
  have hfR : f R = 0 := hzero R (by rw [abs_of_nonneg hR])
  by_cases hx : Real.exp (-Real.cosh R) ≤ Real.exp (-Real.cosh u)
  · unfold compactCoordinateFactor
    rw [max_eq_left hx, Real.log_exp, neg_neg, arcosh_cosh_abs, hfu]
    field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos (-Real.cosh u)))]
  · have hcosh : Real.cosh R < Real.cosh u := by
      have h := Real.exp_lt_exp.mp (lt_of_not_ge hx)
      linarith
    have hRu : R ≤ |u| := by
      have h := Real.cosh_lt_cosh.mp hcosh
      rw [abs_of_nonneg hR] at h
      exact h.le
    rw [hzero u hRu]
    unfold compactCoordinateFactor
    rw [max_eq_right (le_of_lt (lt_of_not_ge hx)), Real.log_exp, neg_neg,
      Real.arcosh_cosh hR, hfR, zero_div, mul_zero]

/-- The actual coordinate-factorization obligation for compactly supported
continuous even functions; no coordinate factor is supplied as a premise. -/
theorem exists_continuous_coordinate_factor {f : ℝ → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f)
    (heven : ∀ u : ℝ, f (-u) = f u) :
    ∃ φ : ℝ → ℂ, ContinuousOn φ (Icc 0 (Real.exp (-1))) ∧
      ∀ u : ℝ, f u = (Real.exp (-Real.cosh u) : ℂ) *
        φ (Real.exp (-Real.cosh u)) := by
  obtain ⟨B, hB⟩ := (show IsCompact (tsupport f) from hc).isBounded.exists_norm_le
  let R : ℝ := max B 0 + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hBR : B < R := by
    dsimp [R]
    linarith [le_max_left B 0]
  have hz : ∀ u : ℝ, R ≤ |u| → f u = 0 := by
    intro u hu
    by_contra hn
    have hmem : u ∈ tsupport f := subset_closure hn
    have hb : |u| ≤ B := by simpa only [Real.norm_eq_abs] using hB u hmem
    linarith
  exact ⟨compactCoordinateFactor R f, compactCoordinateFactor_continuousOn R hf,
    compactCoordinateFactor_eq heven hR hz⟩

end ImbalancedChen.Part3.ActualKCompactCoordinateFactorSourceOnly
