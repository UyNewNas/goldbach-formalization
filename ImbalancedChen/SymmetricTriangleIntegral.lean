/-
SPDX-License-Identifier: Apache-2.0

HELD SOURCE CANDIDATE. This file has not been compiled or kernel checked.
Target: mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1,
Lean v4.33.0-rc1.

The diagonal is discarded only by the null-singleton property of Lebesgue
measure and Fubini. There is no positivity or diagonal-zero hypothesis.
This analytic diagonal argument is independent of any finite prime sum.
-/
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Tactic.Ring

namespace ImbalancedChen.SymmetricTriangleIntegral

noncomputable section

open Set Function Filter MeasureTheory
open scoped Topology

/-- A continuous real kernel can be integrated in either rectangular order.
The weak endpoint inequalities also cover degenerate rectangles. -/
theorem rectangle_integral_swap
    {K : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hK : ContinuousOn (uncurry K) (Icc a b ×ˢ Icc c d)) :
    (∫ x in a..b, ∫ y in c..d, K x y) =
      ∫ y in c..d, ∫ x in a..b, K x y := by
  apply MeasureTheory.intervalIntegral_intervalIntegral_swap
  rw [uIoc_of_le hab, uIoc_of_le hcd]
  exact (hK.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- The measure-theoretic core: an integrable symmetric square kernel has
one half of its integral in the lower order triangle. Integrability is on
the genuine square, rather than an assumed integral identity. -/
theorem half_square_eq_triangle_of_integrable
    {K : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hK : IntegrableOn (uncurry K) (Ioc a b ×ˢ Ioc a b)
      ((volume : Measure ℝ).prod volume))
    (hSym : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, K x y = K y x) :
    (1 / 2 : ℝ) * (∫ x in a..b, ∫ y in a..b, K x y) =
      ∫ t in a..b, ∫ u in a..t, K t u := by
  classical
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  let L : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.2 ≤ p.1}.indicator (uncurry K)
  have hKi : Integrable (uncurry K) (μ.prod μ) := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact hK
  have hL : Integrable L (μ.prod μ) :=
    hKi.indicator (isClosed_le continuous_snd continuous_fst).measurableSet
  have hmem : ∀ᵐ p ∂μ.prod μ, p ∈ Ioc a b ×ˢ Ioc a b := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hne : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, p.1 ≠ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (μ := μ) (ν := μ)
      (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).2
    exact Eventually.of_forall fun x =>
      (Measure.ae_ne μ x).mono fun _ h => h.symm
  have hsplit : uncurry K =ᵐ[μ.prod μ] fun p => L p + L p.swap := by
    filter_upwards [hmem, hne] with p hp hneq
    have hs : K p.1 p.2 = K p.2 p.1 :=
      hSym p.1 ⟨hp.1.1.le, hp.1.2⟩ p.2 ⟨hp.2.1.le, hp.2.2⟩
    by_cases hle : p.2 ≤ p.1
    · have hnle : ¬p.1 ≤ p.2 := fun h => hneq (le_antisymm h hle)
      simp [L, Function.uncurry, hle, hnle]
    · have hrev : p.1 ≤ p.2 := (lt_of_not_ge hle).le
      simp [L, Function.uncurry, hle, hrev, hs]
  have hdouble : (∫ p, uncurry K p ∂μ.prod μ) =
      2 * ∫ p, L p ∂μ.prod μ := by
    calc
      (∫ p, uncurry K p ∂μ.prod μ) =
          ∫ p, (L p + L p.swap) ∂μ.prod μ := integral_congr_ae hsplit
      _ = (∫ p, L p ∂μ.prod μ) + ∫ p, L p.swap ∂μ.prod μ :=
        integral_add hL hL.swap
      _ = 2 * ∫ p, L p ∂μ.prod μ := by
        rw [MeasureTheory.integral_prod_swap (μ := μ) (ν := μ) L]
        ring
  have hsquare : (∫ x in a..b, ∫ y in a..b, K x y) =
      ∫ p, uncurry K p ∂μ.prod μ := by
    simp_rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.integral_integral hKi
  have htriangle : (∫ t in a..b, ∫ u in a..t, K t u) =
      ∫ p, L p ∂μ.prod μ := by
    calc
      (∫ t in a..b, ∫ u in a..t, K t u) =
          ∫ t in a..b, ∫ u in a..b, L (t, u) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
        change (∫ u in a..t, K t u) =
          ∫ u in a..b, ({u : ℝ | u ≤ t}.indicator (K t)) u
        exact (intervalIntegral.integral_indicator ht').symm
      _ = ∫ p, L p ∂μ.prod μ := by
        simp_rw [intervalIntegral.integral_of_le hab]
        exact (MeasureTheory.integral_prod L hL).symm
  rw [hsquare, htriangle, hdouble]
  ring

/-- A continuous symmetric real kernel on a closed square integrates to
twice its integral over the order triangle. No condition is imposed on
`K x x`, and the kernel may change sign. -/
theorem half_square_eq_triangle
    {K : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hK : ContinuousOn (uncurry K) (Icc a b ×ˢ Icc a b))
    (hSym : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, K x y = K y x) :
    (1 / 2 : ℝ) * (∫ x in a..b, ∫ y in a..b, K x y) =
      ∫ t in a..b, ∫ u in a..t, K t u := by
  apply half_square_eq_triangle_of_integrable hab ?_ hSym
  exact (hK.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

end

end ImbalancedChen.SymmetricTriangleIntegral
