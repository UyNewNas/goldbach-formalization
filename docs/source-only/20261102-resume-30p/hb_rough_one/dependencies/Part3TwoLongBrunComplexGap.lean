import Mathlib

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The algebraic two-long Brun step in the 10 October prime-product completion
note, (E2)--(E3), and direct Brun root note, (10)--(12).
The lower Brun polynomial is allowed to be negative.
The downstream analytic input is the primitive fixed-short-product smooth
core obtained from double Poisson periodization and composite Weil.
No rough-product theorem is assumed here.
-/

namespace ImbalancedChen.Part3.TwoLongBrunComplexGap

open Finset
open scoped BigOperators

noncomputable section

/-- The product upper bound and the valid two-variable lower sandwich. -/
theorem twoLongSandwich
    (rough₁ rough₂ upper₁ upper₂ gap₁ gap₂ : ℝ)
    (hr₁ : 0 ≤ rough₁) (hr₂ : 0 ≤ rough₂)
    (hu₁ : rough₁ ≤ upper₁) (hu₂ : rough₂ ≤ upper₂)
    (hg₁ : upper₁ - rough₁ ≤ gap₁)
    (hg₂ : upper₂ - rough₂ ≤ gap₂) :
    0 ≤ upper₁ * upper₂ - rough₁ * rough₂ ∧
      upper₁ * upper₂ - rough₁ * rough₂ ≤
        gap₁ * upper₂ + upper₁ * gap₂ := by
  have hU₁ : 0 ≤ upper₁ := le_trans hr₁ hu₁
  have hU₂ : 0 ≤ upper₂ := le_trans hr₂ hu₂
  have hA : 0 ≤ (upper₁ - rough₁) * upper₂ :=
    mul_nonneg (sub_nonneg.mpr hu₁) hU₂
  have hB : 0 ≤ rough₁ * (upper₂ - rough₂) :=
    mul_nonneg hr₁ (sub_nonneg.mpr hu₂)
  have hC : 0 ≤ (gap₁ - (upper₁ - rough₁)) * upper₂ :=
    mul_nonneg (sub_nonneg.mpr hg₁) hU₂
  have hD : 0 ≤ upper₁ * (gap₂ - (upper₂ - rough₂)) :=
    mul_nonneg hU₁ (sub_nonneg.mpr hg₂)
  have hE : 0 ≤ (upper₁ - rough₁) * (upper₂ - rough₂) :=
    mul_nonneg (sub_nonneg.mpr hu₁) (sub_nonneg.mpr hu₂)
  constructor <;> nlinarith

/-- The lower polynomial may be negative. -/
theorem twoLongSandwichFromLower
    (rough₁ rough₂ upper₁ upper₂ lower₁ lower₂ : ℝ)
    (hr₁ : 0 ≤ rough₁) (hr₂ : 0 ≤ rough₂)
    (hl₁ : lower₁ ≤ rough₁) (hl₂ : lower₂ ≤ rough₂)
    (hu₁ : rough₁ ≤ upper₁) (hu₂ : rough₂ ≤ upper₂) :
    0 ≤ upper₁ * upper₂ - rough₁ * rough₂ ∧
      upper₁ * upper₂ - rough₁ * rough₂ ≤
        (upper₁ - lower₁) * upper₂ +
          upper₁ * (upper₂ - lower₂) := by
  apply twoLongSandwich rough₁ rough₂ upper₁ upper₂
    (upper₁ - lower₁) (upper₂ - lower₂) hr₁ hr₂ hu₁ hu₂
  · linarith
  · linarith

/-- Complex weights are controlled by a positive gap before summation. -/
theorem complexWeightedTwoLongGap
    {ι : Type*} (S : Finset ι) (alpha : ι → ℂ)
    (rough₁ rough₂ upper₁ upper₂ gap₁ gap₂ : ι → ℝ)
    (hr₁ : ∀ i ∈ S, 0 ≤ rough₁ i)
    (hr₂ : ∀ i ∈ S, 0 ≤ rough₂ i)
    (hu₁ : ∀ i ∈ S, rough₁ i ≤ upper₁ i)
    (hu₂ : ∀ i ∈ S, rough₂ i ≤ upper₂ i)
    (hg₁ : ∀ i ∈ S, upper₁ i - rough₁ i ≤ gap₁ i)
    (hg₂ : ∀ i ∈ S, upper₂ i - rough₂ i ≤ gap₂ i) :
    ‖∑ i ∈ S, alpha i *
        (((upper₁ i * upper₂ i - rough₁ i * rough₂ i : ℝ) : ℂ))‖
      ≤ ∑ i ∈ S, ‖alpha i‖ *
        (gap₁ i * upper₂ i + upper₁ i * gap₂ i) := by
  calc
    _ ≤ ∑ i ∈ S, ‖alpha i *
        (((upper₁ i * upper₂ i - rough₁ i * rough₂ i : ℝ) : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ S, ‖alpha i‖ *
        (gap₁ i * upper₂ i + upper₁ i * gap₂ i) := by
      apply sum_le_sum
      intro i hi
      obtain ⟨hzero, hupper⟩ :=
        twoLongSandwich (rough₁ i) (rough₂ i) (upper₁ i) (upper₂ i)
          (gap₁ i) (gap₂ i) (hr₁ i hi) (hr₂ i hi)
          (hu₁ i hi) (hu₂ i hi) (hg₁ i hi) (hg₂ i hi)
      rw [norm_mul]
      have hnorm :
          ‖(((upper₁ i * upper₂ i - rough₁ i * rough₂ i : ℝ) : ℂ))‖ =
            upper₁ i * upper₂ i - rough₁ i * rough₂ i := by
        simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hzero]
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left hupper (norm_nonneg _)

/-- Separate sharp individual intervals can be replaced by smooth cutoffs
using two positive endpoint strips. This is pointwise and does not
differentiate a coupled product wall. -/
theorem individualIntervalProductStrip
    (indicator₁ indicator₂ smooth₁ smooth₂ strip₁ strip₂ : ℝ)
    (hi₁ : 0 ≤ indicator₁) (hi₁' : indicator₁ ≤ 1)
    (hi₂ : 0 ≤ indicator₂) (hi₂' : indicator₂ ≤ 1)
    (hs₁ : 0 ≤ smooth₁) (hs₁' : smooth₁ ≤ 1)
    (hs₂ : 0 ≤ smooth₂) (hs₂' : smooth₂ ≤ 1)
    (hk₁ : |indicator₁ - smooth₁| ≤ strip₁)
    (hk₂ : |indicator₂ - smooth₂| ≤ strip₂) :
    |indicator₁ * indicator₂ - smooth₁ * smooth₂| ≤
      strip₁ + strip₂ := by
  have h₁ := (abs_le.mp hk₁)
  have h₂ := (abs_le.mp hk₂)
  have hk₁₀ : 0 ≤ strip₁ := le_trans (abs_nonneg _) hk₁
  have hk₂₀ : 0 ≤ strip₂ := le_trans (abs_nonneg _) hk₂
  have hA : 0 ≤ (strip₁ - (indicator₁ - smooth₁)) * indicator₂ :=
    mul_nonneg (by linarith [h₁.2]) hi₂
  have hB : 0 ≤ (strip₁ + (indicator₁ - smooth₁)) * indicator₂ :=
    mul_nonneg (by linarith [h₁.1]) hi₂
  have hC : 0 ≤ (strip₂ - (indicator₂ - smooth₂)) * smooth₁ :=
    mul_nonneg (by linarith [h₂.2]) hs₁
  have hD : 0 ≤ (strip₂ + (indicator₂ - smooth₂)) * smooth₁ :=
    mul_nonneg (by linarith [h₂.1]) hs₁
  have hE : 0 ≤ strip₁ * (1 - indicator₂) :=
    mul_nonneg hk₁₀ (by linarith)
  have hF : 0 ≤ strip₂ * (1 - smooth₁) :=
    mul_nonneg hk₂₀ (by linarith)
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Exact finite coprime mean comparison after the two long variables have
been restricted to coprime integers. The two terms on the right are the
actual products of one-variable coprime sums; no unrestricted Euler mean
is substituted. The factor 1/phi(q) and a nonnegative short coefficient
may be multiplied into this inequality downstream. -/
theorem exactCoprimeMeanGap
    {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (F : ι → ℝ) (G : κ → ℝ)
    (rough₁ upper₁ gap₁ : ι → ℝ)
    (rough₂ upper₂ gap₂ : κ → ℝ)
    (hF : ∀ i ∈ S, 0 ≤ F i)
    (hG : ∀ j ∈ T, 0 ≤ G j)
    (hr₁ : ∀ i ∈ S, 0 ≤ rough₁ i)
    (hr₂ : ∀ j ∈ T, 0 ≤ rough₂ j)
    (hu₁ : ∀ i ∈ S, rough₁ i ≤ upper₁ i)
    (hu₂ : ∀ j ∈ T, rough₂ j ≤ upper₂ j)
    (hg₁ : ∀ i ∈ S, upper₁ i - rough₁ i ≤ gap₁ i)
    (hg₂ : ∀ j ∈ T, upper₂ j - rough₂ j ≤ gap₂ j) :
    (∑ i ∈ S, ∑ j ∈ T,
      F i * G j * (upper₁ i * upper₂ j - rough₁ i * rough₂ j))
      ≤ (∑ i ∈ S, F i * gap₁ i) *
          (∑ j ∈ T, G j * upper₂ j) +
        (∑ i ∈ S, F i * upper₁ i) *
          (∑ j ∈ T, G j * gap₂ j) := by
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ T,
        F i * G j * (gap₁ i * upper₂ j + upper₁ i * gap₂ j) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (twoLongSandwich (rough₁ i) (rough₂ j) (upper₁ i)
          (upper₂ j) (gap₁ i) (gap₂ j) (hr₁ i hi)
          (hr₂ j hj) (hu₁ i hi) (hu₂ j hj)
          (hg₁ i hi) (hg₂ j hj)).2
        (mul_nonneg (hF i hi) (hG j hj))
    _ = (∑ i ∈ S, F i * gap₁ i) *
          (∑ j ∈ T, G j * upper₂ j) +
        (∑ i ∈ S, F i * upper₁ i) *
          (∑ j ∈ T, G j * gap₂ j) := by
      simp only [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      ring

end

end ImbalancedChen.Part3.TwoLongBrunComplexGap
