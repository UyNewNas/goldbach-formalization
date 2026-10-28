import ImbalancedChen.P2CompactThirdHistorySelection
import ImbalancedChen.P1ActualCoarseLowRankSupport

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.

The compact choice constructs actual selected-third support and the
first-four valid selection.  Literal primality, target-prime deletion,
the physical logarithmic point and the inert enumeration cap construct
the ordered six-label sublist of the same original rough-prime carrier.
These discharge the two upstream premises left by the preceding batch's
retained-sixth construction.  No adopted-cell integral, SW, or full PP
estimate is assumed or concluded.
-/

namespace ImbalancedChen.P2CompactOriginalRetainedSixth

noncomputable section
open Classical
open scoped BigOperators
open VariableEnvelope HistoricalThirdCoarse
open P2OriginalFourthCapProducerInterface P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation
open Certificates.P2OriginalSixthElevenLogSemantics
open P2ActualFifthBufferedParentWitness P2CompactThirdHistorySelection

/-- This is the lower bound for the actual third lookup itself, before
either fourth or fifth finite maximum.  It pays the third own test used
to construct the upstream valid selection. -/
theorem selected_third_exponent_ge_buffered_R0
    (e : ℚ) (chi : ℝ) (mesh : ℕ) (c : Cell) (t : Physical)
    (hc : PhysicalCell c t) (j : HistoricalThirdCoarse.Cell mesh)
    (hj : j ∈ cells (e : ℝ) chi mesh)
    (ht : thirdCoordinates t ∈ logPrimeMeshCell 0 (19 / 96) mesh j) :
    R0 t - historyLoss (e : ℝ) chi ≤
      exponent (e : ℝ) chi mesh (thirdCoordinates t) := by
  have hb := inBox_of_cell ht
  have hw := ((mem_cells (e : ℝ) chi mesh j).mp hj).2.2.2.2.2
  have hwQ := (box mesh j).coordinate_widths_le.1
  have hwR : ((box mesh j).ux : ℝ) - (box mesh j).lx ≤
      ((box mesh j).width : ℝ) := by exact_mod_cast hwQ
  have herr := rationalInterval_v_error hb.1 hb.2.1
  have hx : thirdCoordinates t 0 ≤ VariableEnvelope.mu := hc.largest.le
  rw [v_eq_A hx] at herr
  have hbase : (qVLo (box mesh j).lx (box mesh j).ux : ℝ) ≤
      (gamma (e : ℝ) (box mesh j) : ℝ) := by
    exact_mod_cast baseline_le_gamma (e : ℝ) (box mesh j)
  rw [exponent_on_cell (e : ℝ) chi mesh (thirdCoordinates t) j hj ht]
  dsimp only [R0, historyLoss, levelExponent]
  dsimp only [A, thirdCoordinates, historicalPrefixProject] at herr
  linarith

variable {C : Set Physical} (D : CompactThirdChoice C)

private theorem literal_third_projection (N : ℝ) (p1 p2 p3 p4 p5 p6 : ℕ) :
    thirdCoordinates (primeHistoryLogCoordinates N 6 [p6,p5,p4,p3,p2,p1]) =
      primeHistoryLogCoordinates N 3 [p3,p2,p1] := by
  ext i
  fin_cases i <;> rfl

/-- The rough activation and actual third selected owner follow from
the common compact choice.  No supported/active predicate is a premise. -/
theorem actual_third_supported
    (N : ℕ) (hN : 1 < N) (omega : ℝ) (homega : omega ≤ D.roughFloor)
    (p1 p2 p3 p4 p5 p6 : ℕ)
    (hpos : ∀ p ∈ [p6,p5,p4,p3,p2,p1], 0 < p)
    (c : Cell)
    (hc : PhysicalCell c (primeHistoryLogCoordinates (N : ℝ) 6 [p6,p5,p4,p3,p2,p1]))
    (ht : primeHistoryLogCoordinates (N : ℝ) 6 [p6,p5,p4,p3,p2,p1] ∈ C) :
    P1ThirdFallbackSupport.supported (D.e : ℝ) D.chi D.mesh omega (N : ℝ)
      [p3,p2,p1] := by
  let t := primeHistoryLogCoordinates (N : ℝ) 6 [p6,p5,p4,p3,p2,p1]
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hfloor := D.rough_margin t ht
  have hω : omega ≤ t 2 := by
    linarith [hc.order.1, hc.order.2.1, hc.order.2.2.1]
  have hpow3 : (N : ℝ)^t 2 = (p3 : ℝ) := by
    simpa [t, primeHistoryTuple] using
      rpow_primeHistoryLogCoordinates (N : ℝ) hNr (by simp) hpos (2 : Fin 6)
  have hrough : (N : ℝ)^omega ≤ (p3 : ℝ) := by
    rw [← hpow3]
    exact Real.rpow_le_rpow_of_exponent_le hNr.le hω
  obtain ⟨j, hj, hcell⟩ := D.selected_cover t ht
  refine (P1ThirdFallbackSupport.supported_triple (D.e : ℝ) D.chi D.mesh omega
    (N : ℝ) p1 p2 p3).mpr ⟨hrough, j, hj, ?_⟩
  simpa only [literal_third_projection] using hcell

/-- The actual first-stop, initial cube, third own first cube and third
own third cube construct the first four selections of policy5.  Neither
first-four validity nor any selected-third support is supplied by a caller. -/
theorem actual_first_four_valid
    (N : ℕ) (hN : 1 < N) (omega : ℝ) (homega : omega ≤ D.roughFloor)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 D.mesh)) (rows5 : Finset (FifthRow D.mesh))
    (p1 p2 p3 p4 p5 p6 : ℕ)
    (hprime : ∀ p ∈ [p1,p2,p3,p4,p5,p6], p.Prime)
    (h65 : p6 < p5) (h54 : p5 < p4) (h43 : p4 < p3)
    (h32 : p3 < p2) (h21 : p2 < p1)
    (c : Cell)
    (hc : PhysicalCell c (primeHistoryLogCoordinates (N : ℝ) 6 [p6,p5,p4,p3,p2,p1]))
    (ht : primeHistoryLogCoordinates (N : ℝ) 6 [p6,p5,p4,p3,p2,p1] ∈ C) :
    FirstExitValidSelection
      (policy5 D.e D.chi D.mesh omega (N : ℝ) rows4 licensed4 J5 rows5)
      [] true [p1,p2,p3,p4] := by
  let t := primeHistoryLogCoordinates (N : ℝ) 6 [p6,p5,p4,p3,p2,p1]
  have hp1 := hprime p1 (by simp)
  have hp2 := hprime p2 (by simp)
  have hp3 := hprime p3 (by simp)
  have hp4 := hprime p4 (by simp)
  have hp5 := hprime p5 (by simp)
  have hp6 := hprime p6 (by simp)
  have hpos : ∀ p ∈ [p6,p5,p4,p3,p2,p1], 0 < p := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp6.pos
    · exact hp5.pos
    · exact hp4.pos
    · exact hp3.pos
    · exact hp2.pos
    · exact hp1.pos
  have hs := actual_third_supported D N hN omega homega p1 p2 p3 p4 p5 p6
    hpos c hc ht
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have he : (0 : ℝ) < D.e := by exact_mod_cast D.e_pos
  obtain ⟨j, hj, hcell⟩ := D.selected_cover t ht
  have ht3 : primeHistoryLogCoordinates (N : ℝ) 3 [p3,p2,p1] ∈
      logPrimeMeshCell 0 (19 / 96) D.mesh j := by
    simpa only [literal_third_projection] using hcell
  have hrough := ((P1ThirdFallbackSupport.supported_triple (D.e : ℝ) D.chi
    D.mesh omega (N : ℝ) p1 p2 p3).mp hs).1
  have hstop := firstStop_of_triple_cell (D.e : ℝ) D.chi D.mesh (N : ℝ)
    p1 p2 p3 j hj ht3
  have hini := P1CoarseFirstCubeFallbackMargin.initial_first_exponent_strict
    (D.e : ℝ) he D.mesh (N : ℝ) [p1] (by simp) hstop
  have hinverse := P1CoarseFirstCubeFallbackMargin.rpow_first_coordinate
    (N : ℝ) hNr [p1] (show 0 < primeHistoryTuple 1 [p1] 0 from hp1.pos)
  have hinitialCube := first_cube_lt_level_of_exponent p1 hNr hinverse.ge hini
  have hthirdFirst := rawLevel_first_cube_on_cell (D.e : ℝ) D.chi he D.e_small
    D.chi_small D.mesh omega (N : ℝ) hNr p1 p2 p3 hp1.pos hrough j hj ht3
  have hlower := selected_third_exponent_ge_buffered_R0 D.e D.chi D.mesh c t hc j hj hcell
  have hbuf := D.history_buffer t ht
  have hallow : parentAllowance t ≤ R0 t - H3 t :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hmargin3 : H3 t < exponent (D.e : ℝ) D.chi D.mesh (thirdCoordinates t) := by
    linarith
  have hpow (i : Fin 6) : (N : ℝ)^t i =
      (primeHistoryTuple 6 [p6,p5,p4,p3,p2,p1] i : ℝ) :=
    rpow_primeHistoryLogCoordinates (N : ℝ) hNr (by simp) hpos i
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hcube : (N : ℝ)^(3 * t 2) = (p3 : ℝ)^3 := by
    rw [mul_comm, Real.rpow_mul_natCast hN0.le, hpow 2]
    rfl
  have hpowH3 : (N : ℝ)^H3 t = (p1 : ℝ)*p2*p3^3 := by
    simp only [H3, Real.rpow_add hN0, hcube, hpow]
    rfl
  have hraw : rawLevel (D.e : ℝ) D.chi D.mesh omega (N : ℝ) [p3,p2,p1] =
      (N : ℝ)^exponent (D.e : ℝ) D.chi D.mesh (thirdCoordinates t) := by
    rw [P1ThirdFallbackSupport.rawLevel_eq_ite_supported, if_pos hs]
    rw [literal_third_projection]
  have hthirdCube : (p1 : ℝ)*p2*p3^3 <
      rawLevel (D.e : ℝ) D.chi D.mesh omega (N : ℝ) [p3,p2,p1] := by
    rw [hraw, ← hpowH3]
    exact (Real.rpow_lt_rpow_left_iff hNr).mpr hmargin3
  have hpass1 : policy5 D.e D.chi D.mesh omega (N : ℝ) rows4 licensed4 J5 rows5
      false [p1] = true := by
    rw [policy5_through_four D.e D.chi D.mesh omega (N : ℝ) rows4 licensed4
      J5 rows5 false [p1] (by simp)]
    exact (P1ActualCoarseLowRankSupport.singleton_policy_iff_original_first_tests
      (D.e : ℝ) D.chi D.mesh omega N p1 hp1).mpr ⟨hstop, hinitialCube⟩
  have hpass3 : policy5 D.e D.chi D.mesh omega (N : ℝ) rows4 licensed4 J5 rows5
      false [p3,p2,p1] = true := by
    rw [policy5_through_four D.e D.chi D.mesh omega (N : ℝ) rows4 licensed4
      J5 rows5 false [p3,p2,p1] (by simp)]
    exact (policy_third_iff (D.e : ℝ) D.chi D.mesh omega (N : ℝ) p1 p2 p3
      hp3.pos h32 h21).mpr ⟨hthirdFirst, hthirdCube⟩
  have heven (pre : List ℕ) (hlen : pre.length ≤ 4) :
      policy5 D.e D.chi D.mesh omega (N : ℝ) rows4 licensed4 J5 rows5 true pre = true := by
    rw [policy5_through_four D.e D.chi D.mesh omega (N : ℝ) rows4 licensed4
      J5 rows5 true pre hlen]
    exact policy_even (D.e : ℝ) D.chi D.mesh omega (N : ℝ) pre
  simp only [FirstExitValidSelection, Bool.not_true, Bool.not_false]
  exact ⟨hpass1, heven _ (by simp), hpass3, heven _ (by simp), trivial⟩

/-- Primality, target-prime deletion and the actual logarithmic point
construct the six-label sublist of the original rough universe.  The
lower endpoint uses the same later-chosen omega; the upper endpoint is
the original 19/96 cutoff.  The natural enumeration bound is inert. -/
theorem actual_six_labels_sublist
    (N cap : ℕ) (hN : 1 < N) (omega : ℝ) (homega : omega ≤ D.roughFloor)
    (hcap : (N : ℝ)^(19 / 96 : ℝ) ≤ (cap : ℝ))
    (p1 p2 p3 p4 p5 p6 : ℕ)
    (hprime : ∀ p ∈ [p1,p2,p3,p4,p5,p6], p.Prime)
    (hdelete : ∀ p ∈ [p1,p2,p3,p4,p5,p6], ¬p ∣ N)
    (h65 : p6 < p5) (h54 : p5 < p4) (h43 : p4 < p3)
    (h32 : p3 < p2) (h21 : p2 < p1)
    (c : Cell)
    (hc : PhysicalCell c (primeHistoryLogCoordinates (N : ℝ) 6 [p6,p5,p4,p3,p2,p1]))
    (ht : primeHistoryLogCoordinates (N : ℝ) 6 [p6,p5,p4,p3,p2,p1] ∈ C) :
    [p1,p2,p3,p4,p5,p6] <+
      roughPrimeUniverse N cap ((N : ℝ)^omega) ((N : ℝ)^(19 / 96 : ℝ)) := by
  let t := primeHistoryLogCoordinates (N : ℝ) 6 [p6,p5,p4,p3,p2,p1]
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ p ∈ [p6,p5,p4,p3,p2,p1], 0 < p := by
    intro p hp
    have hp' : p ∈ [p1,p2,p3,p4,p5,p6] := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_comm, or_left_comm,
        or_assoc] using hp
    exact (hprime p hp').pos
  have hpow (i : Fin 6) : (N : ℝ)^t i =
      (primeHistoryTuple 6 [p6,p5,p4,p3,p2,p1] i : ℝ) :=
    rpow_primeHistoryLogCoordinates (N : ℝ) hNr (by simp) hpos i
  have hlo : (N : ℝ)^omega ≤ (p6 : ℝ) := by
    have hω : omega ≤ t 5 := (homega.trans (D.rough_margin t ht).le)
    have h := Real.rpow_le_rpow_of_exponent_le hNr.le hω
    simpa [hpow 5, primeHistoryTuple] using h
  have hupper : (p1 : ℝ) < (N : ℝ)^(19 / 96 : ℝ) := by
    have hx : t 0 < (19 / 96 : ℝ) := by
      have h := hc.largest
      norm_num [Certificates.P2OriginalSixthElevenLogSemantics.mu] at h
      linarith
    have h := (Real.rpow_lt_rpow_left_iff hNr).mpr hx
    simpa [hpow 0, primeHistoryTuple] using h
  have hsort : [p1,p2,p3,p4,p5,p6].Pairwise (· > ·) := by
    simp [List.pairwise_cons] <;> omega
  have hmem : ∀ p ∈ [p1,p2,p3,p4,p5,p6],
      p ∈ roughPrimeUniverse N cap ((N : ℝ)^omega) ((N : ℝ)^(19 / 96 : ℝ)) := by
    intro p hp
    have hp6 : p6 ≤ p := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hp1 : p ≤ p1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    exact (mem_roughPrimeUniverse_iff_of_cutoff_le_cap hcap).mpr
      ⟨hprime p hp, hdelete p hp, hlo.trans (by exact_mod_cast hp6),
        (show (p : ℝ) ≤ (p1 : ℝ) by exact_mod_cast hp1).trans_lt hupper⟩
  exact List.sublist_of_subperm_of_pairwise
    (List.subperm_of_subset hsort.nodup hmem) hsort (roughPrimeUniverse_pairwise_gt _ _ _ _)

/-- The compact original construction supplies supported, common buffer,
first-four validity and carrier sublist itself.  The arithmetic caller
keeps only the literal prime/target-deletion data and enumeration bound. -/
theorem exists_same_carrier_retained_sixth
    (N cap : ℕ) (hN : 1 < N) (omega : ℝ) (homega : omega ≤ D.roughFloor)
    (hcap : (N : ℝ)^(19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 D.mesh)) (rows5 : Finset (FifthRow D.mesh))
    (p1 p2 p3 p4 p5 p6 : ℕ)
    (hprime : ∀ p ∈ [p1,p2,p3,p4,p5,p6], p.Prime)
    (hdelete : ∀ p ∈ [p1,p2,p3,p4,p5,p6], ¬p ∣ N)
    (h65 : p6 < p5) (h54 : p5 < p4) (h43 : p4 < p3)
    (h32 : p3 < p2) (h21 : p2 < p1)
    (c : Cell)
    (hc : PhysicalCell c (primeHistoryLogCoordinates (N : ℝ) 6 [p6,p5,p4,p3,p2,p1]))
    (ht : primeHistoryLogCoordinates (N : ℝ) 6 [p6,p5,p4,p3,p2,p1] ∈ C)
    (h : ℕ → ℝ) :
    ∃ leaf ∈ firstExitRetainedLeaves
      (policy5 D.e D.chi D.mesh omega (N : ℝ) rows4 licensed4 J5 rows5) h [] true 1
      (roughPrimeUniverse N cap ((N : ℝ)^omega) ((N : ℝ)^(19 / 96 : ℝ))),
      leaf.selected = [p6,p5,p4,p3,p2,p1] := by
  have hpos : ∀ p ∈ [p6,p5,p4,p3,p2,p1], 0 < p := by
    intro p hp
    have hp' : p ∈ [p1,p2,p3,p4,p5,p6] := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_comm, or_left_comm,
        or_assoc] using hp
    exact (hprime p hp').pos
  have hs := actual_third_supported D N hN omega homega p1 p2 p3 p4 p5 p6 hpos c hc ht
  have hfour := actual_first_four_valid D N hN omega homega rows4 licensed4 J5 rows5
    p1 p2 p3 p4 p5 p6 hprime h65 h54 h43 h32 h21 c hc ht
  have hsub := actual_six_labels_sublist D N cap hN omega homega hcap
    p1 p2 p3 p4 p5 p6 hprime hdelete h65 h54 h43 h32 h21 c hc ht
  exact P2ActualFifthBufferedParentWitness.exists_retained_sixth_prefix_of_history_buffer
    D.e D.chi D.mesh omega (N : ℝ) rows4 licensed4 J5 rows5 p1 p2 p3 p4 p5 p6
    (by exact_mod_cast hN) (hprime p6 (by simp)).pos h65 h54 h43 h32 h21 c hc hs
    (D.history_buffer _ ht) _ h hsub hfour

end
end ImbalancedChen.P2CompactOriginalRetainedSixth
