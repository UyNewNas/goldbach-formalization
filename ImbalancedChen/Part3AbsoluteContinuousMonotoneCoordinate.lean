import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

An actual absolutely continuous function remains absolutely continuous under
a continuous strictly increasing coordinate that is Lipschitz on the compact
source interval. Disjoint interval images and the epsilon-delta definition
are proved explicitly. This supplies the nonsmooth exponential-coordinate
composition step without assuming a weak chain rule or graph approximation.
-/

namespace ImbalancedChen.Part3.AbsoluteContinuousMonotoneCoordinate20261026b
noncomputable section
open Set Filter MeasureTheory
open AbsolutelyContinuousOnInterval

theorem image_uIoc_strictMono {φ : ℝ → ℝ} (hc : Continuous φ) (hm : StrictMono φ)
    (a b : ℝ) : φ '' uIoc a b = uIoc (φ a) (φ b) := by
  rcases le_total a b with hab | hba
  · rw [uIoc_of_le hab, uIoc_of_le (hm.monotone hab)]
    exact hc.image_Ioc_of_strictMono hm
  · rw [uIoc_of_ge hba, uIoc_of_ge (hm.monotone hba)]
    exact hc.image_Ioc_of_strictMono hm

theorem absolutelyContinuous_comp_strictMono_lipschitz {F : Type*} [PseudoMetricSpace F]
    {u : ℝ → F} {φ : ℝ → ℝ} {a b : ℝ} {K : ℝ≥0}
    (hu : AbsolutelyContinuousOnInterval u (φ a) (φ b))
    (hc : Continuous φ) (hm : StrictMono φ)
    (hK : LipschitzOnWith K φ (uIcc a b)) :
    AbsolutelyContinuousOnInterval (u ∘ φ) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hu ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδprop⟩ := hu ε hε
  refine ⟨δ / ((K : ℝ) + 1), by positivity, ?_⟩
  intro E hE hsmall
  let E' : ℕ × (ℕ → ℝ × ℝ) :=
    (E.1, fun i => (φ (E.2 i).1, φ (E.2 i).2))
  have hE' : E' ∈ disjWithin (φ a) (φ b) := by
    constructor
    · intro i hi
      exact ⟨hm.monotone.mapsTo_uIcc (hE.1 i hi).1,
        hm.monotone.mapsTo_uIcc (hE.1 i hi).2⟩
    · intro i hi j hj hij
      change Disjoint (uIoc (φ (E.2 i).1) (φ (E.2 i).2))
        (uIoc (φ (E.2 j).1) (φ (E.2 j).2))
      rw [← image_uIoc_strictMono hc hm, ← image_uIoc_strictMono hc hm]
      exact (disjoint_image_iff hm.injective).mpr (hE.2 hi hj hij)
  have hlength : (∑ i ∈ Finset.range E.1, dist (φ (E.2 i).1) (φ (E.2 i).2)) ≤
      (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (E.2 i).1 (E.2 i).2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact hK.dist_le_mul (hE.1 i hi).1 (hE.1 i hi).2
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hsmall' : (∑ i ∈ Finset.range E'.1, dist (E'.2 i).1 (E'.2 i).2) < δ := by
    have hmultiply := (lt_div_iff₀ (by positivity : 0 < (K : ℝ) + 1)).mp hsmall
    have hn : 0 ≤ ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 :=
      Finset.sum_nonneg (fun _ _ => dist_nonneg)
    change (∑ i ∈ Finset.range E.1, dist (φ (E.2 i).1) (φ (E.2 i).2)) < δ
    nlinarith
  exact hδprop E' hE' hsmall'

/-- Exponential physical height is a genuine AC coordinate on every finite
log interval. The compact Lipschitz bound is derived from smoothness. -/
theorem absolutelyContinuous_comp_scaled_exp {F : Type*} [PseudoMetricSpace F]
    {u : ℝ → F} {a : ℝ} (ha : 0 < a) (r s : ℝ)
    (hu : AbsolutelyContinuousOnInterval u (Real.exp r / a) (Real.exp s / a)) :
    AbsolutelyContinuousOnInterval (fun t => u (Real.exp t / a)) r s := by
  let φ : ℝ → ℝ := fun t => Real.exp t / a
  have hc : Continuous φ := Real.continuous_exp.div_const a
  have hm : StrictMono φ := fun x y hxy =>
    (div_lt_div_iff_of_pos_right ha).mpr (Real.exp_lt_exp.mpr hxy)
  have hd : ContDiffOn ℝ 1 φ (uIcc r s) := by
    exact (Real.contDiff_exp.div_const a).contDiffOn
  obtain ⟨K, hK⟩ := hd.exists_lipschitzOnWith (by norm_num)
    (by simpa only [uIcc] using (convex_Icc (min r s) (max r s))) isCompact_uIcc
  exact absolutelyContinuous_comp_strictMono_lipschitz hu hc hm hK

end
end ImbalancedChen.Part3.AbsoluteContinuousMonotoneCoordinate20261026b
