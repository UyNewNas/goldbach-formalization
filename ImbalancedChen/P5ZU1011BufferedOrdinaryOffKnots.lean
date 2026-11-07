import ImbalancedChen.P5ZU1011BufferedOrdinaryClamp
import ImbalancedChen.P5ZU1011H248CommonPartition

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
True upper-table physical-buffer comparison above the clamp, away from
the 150 HIGH knots j51,...,200. The clamp knot50 is handled on its entire
half-space by BufferedOrdinaryClamp. No table soundness/mean premise.
-/

namespace ImbalancedChen.P5Z.BufferedOrdinaryOffKnots

noncomputable section

open Set Part5UpperTables Part5OriginalUpsilon5CausalDictionary
open U11H248 U1011H248Clamp U1011H248Partition BufferedOrdinaryClamp

def HighOffKnots (s : ℝ) : Prop := ∀ j : Fin 150, s ≠ floorGrid (51 + j.val)

/-- Local exact lookup stability above two. This concerns an OPEN atom
or the exterior only; it makes no false absolute-continuity claim at the
full adjacent-min clamp state. -/
theorem exists_lookup_margin {s : ℝ} (hs : 2 < s) (hn : HighOffKnots s) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℝ, |q - s| < δ →
      H248 (max 2 q) = H248 (max 2 s) := by
  obtain ⟨state, hstate⟩ := exists_scalarCell s
  cases state with
  | none =>
      have hs5 := (mem_scalarCell_none_iff s).mp hstate
      refine ⟨(s - 5) / 2, by linarith only [hs5], ?_⟩
      intro q hq
      have hh := (abs_lt.mp hq).1
      have hq5 : 5 < q := by linarith only [hh, hs5]
      rw [H248_eq_stateValue ((mem_scalarCell_none_iff q).mpr hq5), H248_eq_stateValue hstate]
  | some atom =>
      cases atom with
      | inr j =>
          change max 2 s ∈ Icc (1 : ℝ) 5 ∧ max 2 s = floorGrid j.val at hstate
          have heq : s = floorGrid j.val := by simpa only [max_eq_right hs.le] using hstate.2
          have hJ : 51 ≤ j.val := by
            have hjReal : (50 : ℝ) < (j.val : ℝ) := by
              dsimp only [floorGrid] at heq
              linarith only [hs, heq]
            have hjNat : 50 < j.val := by exact_mod_cast hjReal
            omega
          let k : Fin 150 := ⟨j.val - 51, by have hh := j.isLt; omega⟩
          have hk : 51 + k.val = j.val := by dsimp only [k]; omega
          exact (hn k (by simpa only [hk] using heq)).elim
      | inl i =>
          change max 2 s ∈ Icc (1 : ℝ) 5 ∩
            Ioo (floorGrid i.val) (floorGrid (i.val + 1)) at hstate
          have hOpen : floorGrid i.val < s ∧ s < floorGrid (i.val + 1) := by
            simpa only [max_eq_right hs.le] using hstate.2
          let δ : ℝ := min (s - floorGrid i.val) (floorGrid (i.val + 1) - s) / 2
          have hd : 0 < δ := by
            exact div_pos (lt_min (sub_pos.mpr hOpen.1) (sub_pos.mpr hOpen.2)) (by norm_num)
          refine ⟨δ, hd, ?_⟩
          intro q hq
          have hdL : δ ≤ (s - floorGrid i.val) / 2 :=
            div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 2)
          have hdU : δ ≤ (floorGrid (i.val + 1) - s) / 2 :=
            div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 2)
          have hLower := (abs_lt.mp hq).1
          have hUpper := (abs_lt.mp hq).2
          have hqLo : floorGrid i.val < q := by linarith only [hLower, hdL, hOpen.1]
          have hqHi : q < floorGrid (i.val + 1) := by linarith only [hUpper, hdU, hOpen.2]
          have h2Hi : 2 < floorGrid (i.val + 1) := hs.trans hOpen.2
          have hGrid5 : floorGrid (i.val + 1) ≤ 5 := by
            have hiNat : i.val + 1 ≤ 200 := by have hh := i.isLt; omega
            have hiReal : ((i.val + 1 : ℕ) : ℝ) ≤ 200 := by exact_mod_cast hiNat
            dsimp only [floorGrid]
            linarith only [hiReal]
          have hqState : q ∈ scalarCell (some (.inl i)) := by
            change max 2 q ∈ Icc (1 : ℝ) 5 ∩
              Ioo (floorGrid i.val) (floorGrid (i.val + 1))
            have hqUpper : max 2 q < floorGrid (i.val + 1) := max_lt h2Hi hqHi
            exact ⟨⟨(by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _),
              hqUpper.le.trans hGrid5⟩, hqLo.trans_le (le_max_right _ _), hqUpper⟩
          rw [H248_eq_stateValue hqState]
          have hsState : s ∈ scalarCell (some (.inl i)) := hstate
          rw [H248_eq_stateValue hsState]

/-- Actual quantitative perturbation of the max-clamped physical query.
This estimate does not mention H, and is valid on either side of two. -/
theorem physical_query_error (R w τ ξ ρ : ℝ) (hw : 0 < w) (hR : 0 ≤ R)
    (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hξsmall : ξ ≤ w / 2) (hρ : 0 ≤ ρ) :
    |physicalQuery R w τ ξ ρ - max 2 (R / w)| ≤
      ρ + (2 * R / w ^ 2) * ξ + (2 / w) * τ := by
  have hd : 0 < w - ξ := by linarith only [hw, hξsmall]
  have hProd0 : 0 < w * (w - ξ) := mul_pos hw hd
  have hProd : w ^ 2 / 2 ≤ w * (w - ξ) := by
    have hh := mul_le_mul_of_nonneg_left hξsmall hw.le
    nlinarith only [hh]
  have hNum0 : 0 ≤ R * ξ + τ * w := add_nonneg (mul_nonneg hR hξ) (mul_nonneg hτ hw.le)
  have hAbs : |R * ξ - τ * w| ≤ R * ξ + τ * w := by
    simpa only [abs_of_nonneg (mul_nonneg hR hξ), abs_of_nonneg (mul_nonneg hτ hw.le)] using
      (abs_sub_le (R * ξ) (τ * w))
  have hEq : (R - τ) / (w - ξ) - R / w = (R * ξ - τ * w) / (w * (w - ξ)) := by
    field_simp [hw.ne', hd.ne']
    <;> ring
  have hRaw : |(R - τ) / (w - ξ) - R / w| ≤ (2 * R / w ^ 2) * ξ + (2 / w) * τ := by
    rw [hEq, abs_div, abs_of_pos hProd0]
    have hh := (div_le_div_of_nonneg_right hAbs hProd0.le).trans
      (div_le_div_of_nonneg_left hNum0 (by positivity : 0 < w ^ 2 / 2) hProd)
    convert hh using 1 <;> field_simp [hw.ne'] <;> ring
  have hMax := abs_max_sub_max_le_max (2 + ρ) ((R - τ) / (w - ξ)) 2 (R / w)
  have hRho : |(2 + ρ) - 2| = ρ := by
    have hh : (2 + ρ) - 2 = ρ := by ring
    rw [hh, abs_of_nonneg hρ]
  rw [hRho] at hMax
  have hRate0 : 0 ≤ (2 * R / w ^ 2) * ξ + (2 / w) * τ := by positivity
  have hh : max ρ |(R - τ) / (w - ξ) - R / w| ≤
      ρ + ((2 * R / w ^ 2) * ξ + (2 / w) * τ) := by
    apply max_le
    · linarith only [hRate0]
    · exact hRaw.trans (by linarith only [hρ])
  have hFinal := hMax.trans hh
  simpa only [physicalQuery, add_assoc] using hFinal

/-- Above the clamp and off the true high knots, one local margin works
before all buffers. With explicit smallness it gives the actual physical
upper-cost approximation, without any lookup-correctness supplier. -/
theorem exists_physical_upper_margin (R w : ℝ) (hw : 0 < w) (hR : 0 < R)
    (hs : 2 < R / w) (hn : HighOffKnots (R / w)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ ξ ρ c : ℝ,
      0 ≤ τ → 0 ≤ ξ → ξ ≤ w / 2 → 0 ≤ ρ →
      ρ + (2 * R / w ^ 2) * ξ + (2 / w) * τ < δ →
      0 < c → c ≤ R - τ →
      physicalCost R w τ ξ ρ ≤ originalCost R w + (4 / c ^ 2) * τ := by
  obtain ⟨δ, hd, hlookup⟩ := exists_lookup_margin hs hn
  refine ⟨δ, hd, ?_⟩
  intro τ ξ ρ c hτ hξ hξsmall hρ hsmall hc hRc
  have he := physical_query_error R w τ ξ ρ hw hR.le hτ hξ hξsmall hρ
  have he' : |physicalQuery R w τ ξ ρ - R / w| < δ := by
    simpa only [max_eq_right hs.le] using he.trans_lt hsmall
  have hEq := hlookup (physicalQuery R w τ ξ ρ) he'
  have hq2 : 2 ≤ physicalQuery R w τ ξ ρ :=
    (by linarith only [hρ] : (2 : ℝ) ≤ 2 + ρ).trans (le_max_left _ _)
  rw [max_eq_right hq2] at hEq
  have hCost := reciprocal_cost_upper hc hRc hτ (H248_bounds (max 2 (R / w)))
  simpa only [physicalCost, originalCost, hEq] using hCost

end

end ImbalancedChen.P5Z.BufferedOrdinaryOffKnots
