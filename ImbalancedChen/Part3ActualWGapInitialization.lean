import ImbalancedChen.Part3ActualPrefixWinnerComplement

/-!
# Actual W row and original-slot initialization

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

On the actual ordered full cell, the swapped W row is dominated by the
earlier unswapped row.  The least-winner tie rule therefore excludes row
5, including ties.  No reordering of the second and third prime is used.

For the actual row-4 gap decision, the first original prime fits group 2
and the second original prime is allocated by the existing deterministic
two-capacity run.  The third original prime has the strict late-slot gap.
All these inequalities are derived from the actual W whole-cell theorem.

The subsequent three-capacity first-overflow run is still missing.  This
initialization is not asserted to be a complete W selected complement or
a signed tensor/spectral license.
-/

namespace ImbalancedChen.Part3.ActualWGapInitialization

noncomputable section

open VariableEnvelope

/-- The actual order and mu ceiling reduce both W minima to B. -/
theorem swapped_W_row_le {m : ℕ} {j : ActualExtendedThirdDyadicLabel m}
    (hmu : actualExtendedThirdDyadicHi m j 0 ≤ mu)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    actualExtendedThirdRobustBaseBranch 5 t ≤ actualExtendedThirdRobustBaseBranch 4 t := by
  have hx := (ht.1 0 (Set.mem_univ _)).2.trans hmu
  have hy := ht.2.2.2.trans hx
  have hz := ht.2.2.1.trans hy
  have hy0 := ht.2.1.trans ht.2.2.1
  change max (v (t 0)) (wInner (t 0) (t 2) (t 1)) ≤
    max (v (t 0)) (wInner (t 0) (t 1) (t 2))
  rw [wInner_eq_B (t 0) hz hy0, wInner_eq_B (t 0) hy ht.2.1]
  apply max_le_max le_rfl
  dsimp [B]
  linarith [ht.2.2.1]

/-- A dominated later W row cannot be the actual least winner, even
when both complete-cell infima tie. -/
theorem actual_least_winner_ne_swapped_W {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (hne : (actualExtendedThirdPhysicalCell m j).Nonempty)
    (hmu : actualExtendedThirdDyadicHi m j 0 ≤ mu) :
    actualExtendedThirdLeastWinningIndex e m j ≠ 5 := by
  have hdom : actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 5) ≤
      actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 4) := by
    apply le_csInf (hne.image _)
    rintro _ ⟨t, ht, rfl⟩
    exact (actualExtendedThirdCellInf_le (continuous_actualExtendedThirdRobustBaseBranch 5) ht).trans
      (swapped_W_row_le hmu ht)
  intro hfive
  have hmax := mem_actualExtendedThirdWinningIndices.mp (actualExtendedThirdLeastWinningIndex_mem e m j)
  have hfour : (4 : Fin 8) ∈ actualExtendedThirdWinningIndices e m j := by
    apply mem_actualExtendedThirdWinningIndices.mpr
    intro l
    have hl := hmax l
    rw [hfive] at hl
    exact hl.trans hdom
  have hle := actualExtendedThirdLeastWinningIndex_le hfour
  rw [hfive] at hle
  norm_num at hle

/-- Actual least-winner dispatch has just one W row on the full domain. -/
theorem actual_full_winner_six_cases {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (hne : (actualExtendedThirdPhysicalCell m j).Nonempty)
    (hmu : actualExtendedThirdDyadicHi m j 0 ≤ mu) :
    actualExtendedThirdLeastWinningIndex e m j = 0 ∨
    actualExtendedThirdLeastWinningIndex e m j = 2 ∨
    actualExtendedThirdLeastWinningIndex e m j = 3 ∨
    actualExtendedThirdLeastWinningIndex e m j = 4 ∨
    actualExtendedThirdLeastWinningIndex e m j = 6 ∨
    actualExtendedThirdLeastWinningIndex e m j = 7 := by
  have hnot1 := actualExtendedThirdLeastWinningIndex_ne_singletonY (e := e) hne hmu
  have hnot5 := actual_least_winner_ne_swapped_W (e := e) hne hmu
  generalize hk : actualExtendedThirdLeastWinningIndex e m j = k
  fin_cases k <;> simp_all

/-- Genuine row-4 gap initialization.  The original first prime enters
group 2; only the original second prime is run through the deterministic
prefer-left allocator.  Capacities and the third-prime gap are proved,
not assumed.  The parameter is frozen at t for every p in the same cell. -/
theorem actual_W_gap_initial_two_slots {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hwinner : actualExtendedThirdLeastWinningIndex e m j = 4)
    (hgap : e / 4 < wInner (t 0) (t 1) (t 2) - v (t 0))
    (N : ℝ) (hN : 1 < N) (p : Fin 3 → ℕ) (hp : ∀ i, 0 < p i)
    (hs : actualSelectedPrimeCoordinates N p ∈ actualExtendedThirdPhysicalCell m j) :
    let theta := actualExtendedThirdRescueParameter e m j t
    let Bcap := N ^ (2 * theta - 1)
    let D := N ^ (theta - e / 32)
    1 / 2 ≤ theta ∧ theta < 5 / 8 ∧
      actualExtendedThirdPhysicalLevel e m j + e ≤ theta ∧
      (p 0 : ℝ) ≤ Bcap ∧
      (p 2 : ℝ) ≤ N ^ (actualSelectedSubproductUpper 1 theta - (2 * theta - 1) - e / 8) ∧
      ∀ A : ℝ, 1 ≤ A → A ≤ N ^ (1 / 3 : ℝ) →
        let Ccap := N ^ (1 - theta - e / 32) / A
        let ac := actualTwoCapacityFactors A [p 1]
        1 ≤ Bcap ∧ 1 ≤ Ccap ∧ A * Bcap * Ccap = D ∧
          ac.1 * p 0 * ac.2 = p 0 * p 1 ∧
          (ac.1 : ℝ) ≤ A ∧ (ac.2 : ℝ) ≤ Ccap := by
  rcases actualExtendedThirdSelectedRescue_wholeCell he0 he hmesh hfull ht false hwinner with
    ⟨hclose, _⟩ | ⟨_hgap, hlo, hhi, hlevel, hcell⟩
  · exact (not_lt_of_ge hclose hgap).elim
  · let theta := actualExtendedThirdRescueParameter e m j t
    have hNpos : 0 < N := zero_lt_one.trans hN
    obtain ⟨hgate, hW⟩ := hcell _ hs
    have hbelow : actualSelectedPrimeCoordinates N p 0 ≤ mu := by
      have hh := (hs.1 0 (Set.mem_univ _)).2.trans hfull
      linarith
    rw [v_eq_A hbelow] at hgate
    dsimp [A] at hgate
    change theta + e / 16 ≤ wInner _ _ _ at hW
    simp only [wInner, B, cap, le_min_iff] at hW
    obtain ⟨hW1, hW2, hW3⟩ := hW
    have hfirst : (p 0 : ℝ) ≤ N ^ (2 * theta - 1) := by
      rw [← rpow_actualSelectedPrimeCoordinates N hN p hp 0]
      exact Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
    have hsecond : (p 1 : ℝ) ^ 2 ≤ N ^ (1 - theta - e / 32) := by
      rw [← rpow_actualSelectedPrimeCoordinates N hN p hp 1,
        ← Real.rpow_mul_natCast hNpos.le]
      apply Real.rpow_le_rpow_of_exponent_le hN.le
      norm_num
      linarith
    have hlateLog : actualSelectedPrimeCoordinates N p 2 ≤
        actualSelectedSubproductUpper 1 theta - (2 * theta - 1) - e / 8 := by
      have hu : actualSelectedPrimeCoordinates N p 2 + (2 * theta - 1) + e / 8 ≤
          actualSelectedSubproductUpper 1 theta := by
        unfold actualSelectedSubproductUpper
        apply le_min <;> linarith
      linarith
    have hlate : (p 2 : ℝ) ≤
        N ^ (actualSelectedSubproductUpper 1 theta - (2 * theta - 1) - e / 8) := by
      rw [← rpow_actualSelectedPrimeCoordinates N hN p hp 2]
      exact Real.rpow_le_rpow_of_exponent_le hN.le hlateLog
    refine ⟨hlo, hhi, hlevel, hfirst, hlate, ?_⟩
    intro A hA hAupper
    have hApos : 0 < A := zero_lt_one.trans_le hA
    let P := N ^ (1 - theta - e / 32)
    let Ccap := P / A
    have hPupper : A ≤ P := hAupper.trans
      (Real.rpow_le_rpow_of_exponent_le hN.le (by dsimp [theta]; linarith))
    have hC : 1 ≤ Ccap := (le_div_iff₀ hApos).mpr (by simpa using hPupper)
    have hAC : A * Ccap = P := by dsimp [Ccap]; field_simp [hApos.ne'] <;> ring
    have hsupport : actualDwellSupport (A * Ccap) [p 1] := by
      intro i hi
      have hi0 : i = 0 := by simp only [List.length_singleton] at hi; omega
      subst i
      simpa only [hAC, List.take_zero, List.map_nil, List.prod_nil,
        List.getElem_cons_zero, one_mul] using hsecond
    obtain ⟨hprod, hleft, hright⟩ := actualTwoCapacityFactors_correct hA hC [p 1] hsupport
    have hB : 1 ≤ N ^ (2 * theta - 1) := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hN.le
        (show 0 ≤ 2 * theta - 1 by dsimp [theta]; linarith)
    refine ⟨hB, hC, ?_, ?_, hleft, hright⟩
    · calc
        A * N ^ (2 * theta - 1) * Ccap = N ^ (2 * theta - 1) * P := by rw [← hAC]; ring
        _ = N ^ (theta - e / 32) := by
          dsimp [P]
          rw [← Real.rpow_add hNpos]
          congr 1
          ring
    · simpa only [List.prod_singleton, mul_assoc, mul_comm, mul_left_comm] using
        congrArg (fun n : ℕ => n * p 0) hprod

end

end ImbalancedChen.Part3.ActualWGapInitialization
