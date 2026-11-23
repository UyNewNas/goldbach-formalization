import ImbalancedChen.Part3RoughAuxiliarySWChart
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Continuous variation budget for the chart rough-slot estimate

The medium profile is sampled at the original carrier integers. Its total
variation on the whole dyadic slot controls the variation of those samples.
The chart cutoff uses the larger original chart scale throughout.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Filter Finset
open scoped BigOperators

/-- The cutoff fixed on the original chart before selecting the medium slot. -/
def roughChartCutoff (kStar : ℕ) (Xplus : ℝ) : ℝ :=
  let v := (2 : ℝ) ^ (6 * kStar + 2) * Xplus
  v ^ (1 / (Real.log (Real.log v)) ^ 3)

private theorem sampled_complex_variation_le {f : ℝ → ℂ} {a b R : ℝ} {L H : ℕ}
    (hL : a ≤ ((L + 1 : ℕ) : ℝ)) (hH : (H : ℝ) ≤ b) (hR : 0 ≤ R)
    (hv : eVariationOn f (Set.Icc a b) ≤ ENNReal.ofReal R) :
    (∑ n ∈ Ioc L (H - 1), ‖f ((n + 1 : ℕ) : ℝ) - f (n : ℝ)‖) ≤ R := by
  have hI : Ioc L (H - 1) = Ico (L + 1) H := by
    ext n
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hI]
  have hs := eVariationOn.sum_le_of_monotoneOn_Icc
    (f := f) (s := Set.Icc a b) (m := L + 1) (n := H) (u := fun n => (n : ℝ))
    (fun _ _ _ _ hij => Nat.cast_le.mpr hij)
    (fun i hi => ⟨hL.trans (Nat.cast_le.mpr hi.1), (Nat.cast_le.mpr hi.2).trans hH⟩)
  apply (ENNReal.ofReal_le_ofReal_iff hR).mp
  have heq : ENNReal.ofReal (∑ n ∈ Ico (L + 1) H, ‖f ((n + 1 : ℕ) : ℝ) - f (n : ℝ)‖) =
      ∑ n ∈ Ico (L + 1) H, edist (f ((n + 1 : ℕ) : ℝ)) (f (n : ℝ)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => norm_nonneg _)]
    simp only [edist_dist, dist_eq_norm]
  exact heq.trans_le (hs.trans hv)

private theorem variation_log_power_bound {B C l V t : ℝ}
    (hC : 0 ≤ C) (hl : C + 2 ≤ l) (hV : V ≤ C * l ^ B) (ht : |t| ≤ l ^ B) :
    1 + V + |t| ≤ l ^ (max B 0 + 1) := by
  have hl1 : 1 ≤ l := by linarith
  have hl0 : 0 < l := zero_lt_one.trans_le hl1
  have hpow : l ^ B ≤ l ^ max B 0 := Real.rpow_le_rpow_of_exponent_le hl1 (le_max_left _ _)
  have hpow1 : 1 ≤ l ^ max B 0 := Real.one_le_rpow hl1 (le_max_right _ _)
  calc
    _ ≤ 1 + C * l ^ B + l ^ B := add_le_add (add_le_add le_rfl hV) ht
    _ ≤ l ^ max B 0 + C * l ^ max B 0 + l ^ max B 0 :=
      add_le_add (add_le_add hpow1 (mul_le_mul_of_nonneg_left hpow hC)) hpow
    _ = (C + 2) * l ^ max B 0 := by ring
    _ ≤ l * l ^ max B 0 := mul_le_mul_of_nonneg_right hl (Real.rpow_nonneg hl0.le _)
    _ = _ := by rw [Real.rpow_add hl0, Real.rpow_one, mul_comm]

/-- The chart's continuous profile and Mellin frequency bounds give full
auxiliary Siegel–Walfisz for the medium slot on its original interval. The
chart scale, coefficient, and variation hypotheses hold beyond one family
threshold. All progression parameters are selected after the SW threshold. -/
theorem uniformAuxiliarySW_of_chart_mellin_totalVariation {ι : Type*}
    (F : ι → MediumAtom) (kStar : ℕ) (Xplus t : ι → ℝ) (signed : ι → Bool)
    (f : ι → ℝ → ℂ) (B C X : ℝ) (hC : 0 ≤ C)
    (hU : ∀ i, X ≤ (F i).scale → 1 < (F i).U)
    (hV : ∀ i, X ≤ (F i).scale → 1 ≤ (F i).V)
    (hscale : ∀ i, X ≤ (F i).scale → (F i).scale ≤ (2 : ℝ) ^ (6 * kStar + 2) * Xplus i)
    (hprofile : ∀ i, X ≤ (F i).scale → ∀ n ∈ (F i).alphaCarrier, ‖f i (n : ℝ)‖ ≤ 1)
    (hcoeff : ∀ i, X ≤ (F i).scale → ∀ n ∈ (F i).alphaCarrier, (F i).alpha n =
      (f i (n : ℝ) * (n : ℂ) ^ (Complex.I * (t i : ℂ))) *
        (if signed i then roughMoebiusSlot (roughChartCutoff kStar (Xplus i)) n
          else roughOneSlot (roughChartCutoff kStar (Xplus i)) n))
    (hvariation : ∀ i, X ≤ (F i).scale →
      eVariationOn (f i) (Set.Icc (F i).U (2 * (F i).U)) ≤
        ENNReal.ofReal (C * Real.log (F i).scale ^ B))
    (hfrequency : ∀ i, X ≤ (F i).scale → |t i| ≤ Real.log (F i).scale ^ B) :
    UniformAuxiliarySW F 1 := by
  obtain ⟨Xlog, hXlog⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (C + 2))
  let X' := max X (max (Real.exp (Real.exp 3)) Xlog)
  let I := {i : ι // X' ≤ (F i).scale}
  let F' (i : I) := F i.val
  have hX (i : I) : X ≤ (F' i).scale := (le_max_left _ _).trans i.property
  have hSW : UniformAuxiliarySW F' 1 := by
    apply uniformAuxiliarySW_of_chart_mellin_slot F'
      (fun i => roughChartCutoff kStar (Xplus i.val)) (fun i => t i.val)
      (fun i => signed i.val) (fun i n => f i.val (n : ℝ)) (max B 0 + 1) X'
    · exact fun i => hU i.val (hX i)
    · exact fun i => hV i.val (hX i)
    · intro i
      have hlarge : Real.exp (Real.exp 3) ≤ (F' i).scale :=
        ((le_max_left _ _).trans (le_max_right _ _)).trans i.property
      exact roughCutoff_mono_of_exp_exp_three hlarge (hscale i.val (hX i))
    · exact fun i => hprofile i.val (hX i)
    · exact fun i => hcoeff i.val (hX i)
    · intro i _
      have hlog : C + 2 ≤ Real.log (F' i).scale :=
        hXlog _ (((le_max_right _ _).trans (le_max_right _ _)).trans i.property)
      have hlog0 : 0 ≤ Real.log (F' i).scale := by linarith
      have hU0 : 0 < (F' i).U := zero_lt_one.trans (hU i.val (hX i))
      let L := max (⌈(F' i).U⌉₊ - 1) ⌊(F' i).intervalLo⌋₊
      let H := min ⌊2 * (F' i).U⌋₊ ⌊(F' i).intervalHi⌋₊
      have hceil : ⌈(F' i).U⌉₊ ≤ L + 1 := by
        have hleft : ⌈(F' i).U⌉₊ - 1 ≤ L := le_max_left _ _
        omega
      have hL : (F' i).U ≤ ((L + 1 : ℕ) : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hceil)
      have hH : (H : ℝ) ≤ 2 * (F' i).U :=
        (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le (mul_nonneg (by norm_num) hU0.le))
      have hav := sampled_complex_variation_le hL hH
        (mul_nonneg hC (Real.rpow_nonneg hlog0 B)) (hvariation i.val (hX i))
      exact variation_log_power_bound hC hlog hav (hfrequency i.val (hX i))
  intro A hA
  obtain ⟨D, hD, Y, hY, hbound⟩ := hSW A hA
  refine ⟨D, hD, max X' Y, hY.trans_le (le_max_right _ _), ?_⟩
  intro i hi
  exact hbound ⟨i, (le_max_left _ _).trans hi⟩ ((le_max_right _ _).trans hi)

end

end ImbalancedChen.Part3
