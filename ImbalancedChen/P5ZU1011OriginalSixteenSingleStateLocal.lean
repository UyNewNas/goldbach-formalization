import ImbalancedChen.P5ZU1011OriginalSixteenOrdinarySingleState

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Local automatic certification of one literal H248 state from ACTUAL raw
ratio separation from the 151 high knots. The complete sub-two clamp is
retained, as is the above-five exterior. No state/lookup agreement premise.
-/

namespace ImbalancedChen.P5Z.OriginalSixteenSingleStateLocal

noncomputable section

open Set U1011H248Partition
open Part5OriginalUpsilon5CausalDictionary
open LiteralH248IntervalBounds
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open OriginalSixteenOrdinaryBoxBounds OriginalSixteenOrdinarySingleState

/-- Exactly the actual lookup knots at 2,2+1/50,...,5. Low floor
knots below two are irrelevant because the full clamped state is kept. -/
def OffKnots (s : ℝ) : Prop := ∀ j : Fin 151, s ≠ (grid (50 + j.val) : ℝ)

private theorem offKnots_open_atom {s : ℝ} (hs : 2 < s) (hu : s ≤ 5)
    (hn : OffKnots s) :
    ∃ i : Fin 200, (grid i.val : ℝ) < s ∧ s < (grid (i.val + 1) : ℝ) := by
  obtain ⟨state, hstate⟩ := exists_scalarCell s
  cases state with
  | none =>
      have hh := (mem_scalarCell_none_iff s).mp hstate
      exact (not_lt_of_ge hu hh).elim
  | some atom =>
      cases atom with
      | inl i =>
          change max 2 s ∈ Icc (1 : ℝ) 5 ∩
            Ioo (floorGrid i.val) (floorGrid (i.val + 1)) at hstate
          rw [max_eq_right hs.le] at hstate
          exact ⟨i, by simpa only [grid_cast] using hstate.2.1,
            by simpa only [grid_cast] using hstate.2.2⟩
      | inr j =>
          change max 2 s ∈ Icc (1 : ℝ) 5 ∧ max 2 s = floorGrid j.val at hstate
          have heq : s = (grid j.val : ℝ) := by
            simpa only [max_eq_right hs.le, grid_cast] using hstate.2
          have hJ : 50 ≤ j.val := by
            have hjReal : (50 : ℝ) < (j.val : ℝ) := by
              rw [grid_cast] at heq
              dsimp only [floorGrid] at heq
              linarith only [hs, heq]
            have hjNat : 50 < j.val := by exact_mod_cast hjReal
            omega
          let k : Fin 151 := ⟨j.val - 50, by have hh := j.isLt; omega⟩
          have hk : 50 + k.val = j.val := by dsimp only [k]; omega
          exact (hn k (by simpa only [hk] using heq)).elim

/-- A genuine open-neighbourhood witness for rational endpoint tests.
At raw ratios below two, this proves the ENTIRE clamp test. At raw ratios
above five, it proves the actual zero exterior test. -/
theorem exists_scalar_margin {s : ℝ} (hn : OffKnots s) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ l u : ℚ,
      |(l : ℝ) - s| < δ → |(u : ℝ) - s| < δ →
        u ≤ 2 ∨ 5 < l ∨
          ∃ i : Fin 200, grid i.val < lowerQuery l ∧ upperQuery u < grid (i.val + 1) := by
  by_cases hsLo : s < 2
  · refine ⟨(2 - s) / 2, by linarith only [hsLo], ?_⟩
    intro l u _ hu
    have hUpper := (abs_lt.mp hu).2
    have hu2 : (u : ℝ) ≤ 2 := by linarith only [hUpper, hsLo]
    exact Or.inl (by exact_mod_cast hu2)
  · have hsNe : s ≠ 2 := by
      have hh := hn ⟨0, by norm_num⟩
      norm_num [grid] at hh
      exact hh
    have hs2 : 2 < s := lt_of_le_of_ne (le_of_not_gt hsLo) (Ne.symm hsNe)
    by_cases hsHi : 5 < s
    · refine ⟨(s - 5) / 2, by linarith only [hsHi], ?_⟩
      intro l u hl _
      have hLower := (abs_lt.mp hl).1
      have hl5 : (5 : ℝ) < l := by linarith only [hLower, hsHi]
      exact Or.inr (Or.inl (by exact_mod_cast hl5))
    · obtain ⟨i, hiL, hiU⟩ := offKnots_open_atom hs2 (le_of_not_gt hsHi) hn
      let δ : ℝ := min (s - (grid i.val : ℝ)) ((grid (i.val + 1) : ℝ) - s) / 2
      have hd : 0 < δ := by dsimp only [δ]; exact div_pos (lt_min (sub_pos.mpr hiL) (sub_pos.mpr hiU)) (by norm_num)
      refine ⟨δ, hd, ?_⟩
      intro l u hl hu
      have hdL : δ ≤ (s - (grid i.val : ℝ)) / 2 := by
        exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 2)
      have hdU : δ ≤ ((grid (i.val + 1) : ℝ) - s) / 2 := by
        exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 2)
      have hLower := (abs_lt.mp hl).1
      have hUpper := (abs_lt.mp hu).2
      have hlGrid : (grid i.val : ℝ) < (l : ℝ) := by linarith only [hLower, hdL, hiL]
      have huGrid : (u : ℝ) < (grid (i.val + 1) : ℝ) := by linarith only [hUpper, hdU, hiU]
      have h2Grid : (2 : ℝ) < (grid (i.val + 1) : ℝ) := hs2.trans hiU
      have hQL : (grid i.val : ℝ) < (lowerQuery l : ℝ) :=
        hlGrid.trans_le (by simp only [lowerQuery, Rat.cast_max, Rat.cast_ofNat]; exact le_max_right _ _)
      have hQU : (upperQuery u : ℝ) < (grid (i.val + 1) : ℝ) := by
        simp only [upperQuery, Rat.cast_max, Rat.cast_ofNat]
        exact max_lt h2Grid huGrid
      exact Or.inr (Or.inr ⟨i, by exact_mod_cast hQL, by exact_mod_cast hQU⟩)

/-- The actual policy ratio has a uniform scalar neighbourhood before
ANY candidate box, so owner-grid convergence can discharge SingleState. -/
theorem exists_singleState_margin (s : ℝ) (hn : OffKnots s) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Policy) (B : Box),
      |(ratioLower p B : ℝ) - s| < δ → |(ratioUpper p B : ℝ) - s| < δ → SingleState p B := by
  obtain ⟨δ, hd, hlocal⟩ := exists_scalar_margin hn
  refine ⟨δ, hd, ?_⟩
  intro p B hL hU
  rcases hlocal (ratioLower p B) (ratioUpper p B) hL hU with
    hclamp | hext | hopen
  · exact Or.inl hclamp
  · exact Or.inr (Or.inl hext)
  · exact Or.inr (Or.inr (Or.inl hopen))

end

end ImbalancedChen.P5Z.OriginalSixteenSingleStateLocal
