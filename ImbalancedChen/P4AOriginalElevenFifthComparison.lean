import ImbalancedChen.P4AOriginalElevenSixthStage

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The actual fifth parent on a G7 cell is bounded by its original comparison
cap, for the actual supported third ancestor. This is generic in OriginalData
and therefore applies to the enriched old+new fifth bank without excluding
its new rows. It does not assert that compact supported ancestors occur;
that common-mesh realization remains a separate necessary theorem.
-/
namespace ImbalancedChen.P4AOriginalElevenFifthComparison
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
theorem tent_eq_v (s : ℝ) : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.tent s = v s := by
  rw [v_eq_min]
  dsimp [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.tent,A,C]
  congr 1
  ring

def slots (m : ℕ) : Finset (Fin 5) := Finset.univ.filter (fun j => ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.bit m j.val)
theorem slots_complete : ∀ I : Finset (Fin 5), ∃ m ∈ Finset.Icc 0 31, slots m = I := by decide

theorem source_all_subsets (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (t : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Physical) (hc : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t)
    (I : Finset (Fin 5)) : v (∑ j ∈ I, t j.castSucc) ≤ ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t := by
  obtain ⟨m,hm,rfl⟩ := slots_complete I
  have he : (∑ j ∈ slots m, t j.castSucc) = ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.subsetSum m t := by
    simp only [slots,Finset.sum_filter,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.subsetSum]
  rw [he]
  by_cases hz : m = 0
  · subst m
    simp only [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.subsetSum,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.bit,Nat.zero_div,Nat.zero_mod,decide_false,if_false,
      Finset.sum_const_zero]
    rw [v_eq_A (by norm_num [mu] : (0:ℝ) ≤ mu)]
    have hp := hc.coordinates_pos (0:Fin 6)
    have hcomp := hc.comparison
    dsimp [A,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0] at hcomp ⊢
    linarith
  · rw [← tent_eq_v]
    apply hc.raw_envelope.2.1 m
    have hu := (Finset.mem_Icc.mp hm).2
    simp only [Finset.mem_Icc]
    omega

theorem source_ancestor_tent (N : ℝ) (pre : List ℕ) (hlen : pre.length = 6)
    (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (hc : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (k : ℕ) (hk : k ≤ 5) (I : Finset (Fin k)) :
    v (∑ j ∈ I, primeHistoryLogCoordinates N k (rosserAncestor k pre) j) ≤
      ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  let emb : Fin k ↪ Fin 5 := ⟨fun j => j.castLE hk,by intro i j hij; exact Fin.ext (congrArg Fin.val hij)⟩
  have he : (∑ j ∈ I, primeHistoryLogCoordinates N k (rosserAncestor k pre) j) =
      ∑ j ∈ I.map emb, primeHistoryLogCoordinates N 6 pre j.castSucc := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j _
    exact primeHistoryLogCoordinates_ancestor N hlen (by omega : k ≤ 6) j
  rw [he]
  exact source_all_subsets c _ hc _

theorem source_original_third_le (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (t : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Physical) (hc : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t) :
    original (t 0) (t 1) (t 2) ≤ ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t := by
  have htents := hc.third_envelope.2.1
  simp_rw [tent_eq_v] at htents
  have h1 := htents 1 (by decide)
  have h3 := htents 3 (by decide)
  have h7 := htents 7 (by decide)
  have h5 := htents 5 (by decide)
  have h6 := htents 6 (by decide)
  norm_num [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.subsetSum,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.bit,Fin.sum_univ_succ] at h1 h3 h7 h5 h6
  have ho : Ordered (t 0) (t 1) (t 2) :=
    ⟨(hc.coordinates_pos 2).le,hc.order.2.2.2.1.le,hc.order.2.2.2.2.le,hc.largest.le⟩
  rw [original_eq_six ho]
  have hB : B (t 2) ≤ ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0 t := by
    have hBW : B (t 2)=ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.W t := by dsimp [B,cap,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.W]; ring
    rw [hBW]
    exact hc.oldW
  have hh : six (t 0) (t 1) (t 2) ≤ ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0 t :=
    max_le h1 (max_le h3 (max_le h7 (max_le hB (max_le h5 h6))))
  exact hh.trans hc.comparison

theorem actual_third_eq_supported_original (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 6) (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (hc : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c (primeHistoryLogCoordinates N 6 pre)) :
    lambda3 d N (rosserAncestor 4 pre) =
      P1CoarseFirstCubeFallbackMargin.effectiveExponent (d.e:ℝ) d.chi d.m d.omega N (rosserAncestor 3 pre) := by
  have hx := hc.largest.le
  have h2 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 2 ≤ 6) (0:Fin 2)
  have h3 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 6) (0:Fin 3)
  have hn2 : ¬P5OriginalAboveMuThirdLowerPhysicalCoefficient.secondGuard N (rosserAncestor 4 pre) := by
    intro hh
    have hh' := hh.1
    rw [rosserAncestor_nested 2 4 (by decide)] at hh'
    exact (not_lt_of_ge hx) (h2 ▸ hh')
  have hn3 : ¬P5OriginalAboveMuThirdLowerPhysicalCoefficient.thirdGuard N (rosserAncestor 4 pre) := by
    intro hh
    have hh' := hh.1
    rw [rosserAncestor_nested 3 4 (by decide)] at hh'
    exact (not_lt_of_ge hx) (h3 ▸ hh')
  simp only [lambda3,fallbackSeed,if_neg hn3,if_neg hn2,max_self,originalSeed,
    P1OriginalVariableFourthContinuation.seedExponent,rosserAncestor_nested 3 4 (by decide)]

theorem supported_third_le_comparison (d : OriginalData) (N : ℝ) (he : 0 ≤ d.e)
    (pre : List ℕ) (hlen : pre.length = 6) (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell)
    (hc : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (hs : P1ThirdFallbackSupport.supported (d.e:ℝ) d.chi d.m d.omega N (rosserAncestor 3 pre)) :
    lambda3 d N (rosserAncestor 4 pre) ≤ ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  have heR : (0:ℝ) ≤ d.e := by exact_mod_cast he
  rw [actual_third_eq_supported_original d N pre hlen c hc,
    P1CoarseFirstCubeFallbackMargin.effectiveExponent,if_pos hs]
  obtain ⟨j,hj,ht⟩ := hs.2
  rw [HistoricalThirdCoarse.exponent_on_cell _ _ _ _ j hj ht]
  let t := primeHistoryLogCoordinates N 6 pre
  have h0 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 6) (0:Fin 3)
  have h1 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 6) (1:Fin 3)
  have h2 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 6) (2:Fin 3)
  have hb := HistoricalThirdCoarse.inBox_of_cell ht
  rw [h0,h1,h2] at hb
  have ho : Ordered (t 0) (t 1) (t 2) :=
    ⟨(hc.coordinates_pos 2).le,hc.order.2.2.2.1.le,hc.order.2.2.2.2.le,hc.largest.le⟩
  have hg := HistoricalThirdCoarse.gamma_le_endpoint (d.e:ℝ) (HistoricalThirdCoarse.box d.m j)
    heR hb ho.1 ho.2.1 ho.2.2.1
  rw [HistoricalThirdCoarse.endpoint,if_pos ho.2.2.2] at hg
  have hh := source_original_third_le c t hc
  dsimp only [HistoricalThirdCoarse.levelExponent]
  linarith

/-- Includes every actual fourth and fifth row of d, hence also every
new fifth row in NewFifthUnion.data. No upper bound on that parent is an
input; it follows from the source's original all-subset licence. -/
theorem supported_fifth_le_comparison (d : OriginalData) (N : ℝ) (he : 0 ≤ d.e)
    (pre : List ℕ) (hlen : pre.length = 6) (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell)
    (hc : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (hs : P1ThirdFallbackSupport.supported (d.e:ℝ) d.chi d.m d.omega N (rosserAncestor 3 pre)) :
    actualParent5 d N pre ≤ ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  have h4len : (rosserAncestor 4 pre).length = 4 := by simp [hlen]
  have h5len : (rosserAncestor 5 pre).length = 5 := by simp [hlen]
  have h4 : exponent4 d N (rosserAncestor 4 pre) ≤ ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap c (primeHistoryLogCoordinates N 6 pre) := by
    rw [exponent4,if_pos h4len]
    apply finiteMax_le
    · exact supported_third_le_comparison d N he pre hlen c hc hs
    · intro r _ _
      rw [r.bufferedCandidate_eq]
      have hh := source_ancestor_tent N pre hlen c hc 4 (by decide) r.selected
      have heR : (0:ℝ) ≤ d.e := by exact_mod_cast he
      linarith
  change exponent5 d N (rosserAncestor 5 pre) ≤ _
  rw [exponent5,if_pos h5len,rosserAncestor_nested 4 5 (by decide)]
  apply finiteMax_le _ _ _ _ _ h4
  intro r _ _
  rw [P1OriginalVariableFifthContinuation.candidate,P1OriginalVariableFifthContinuation.envelope_eq_v]
  have hh := source_ancestor_tent N pre hlen c hc 5 (by decide) r.selected
  have heR : (0:ℝ) ≤ d.e := by exact_mod_cast he
  linarith

end
end ImbalancedChen.P4AOriginalElevenFifthComparison
