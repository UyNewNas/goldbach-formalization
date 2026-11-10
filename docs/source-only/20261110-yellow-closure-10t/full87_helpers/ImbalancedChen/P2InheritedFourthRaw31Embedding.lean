import ImbalancedChen.P1OriginalVariableFifthContinuation
import ImbalancedChen.P2OriginalSixthElevenLogSemantics
import ImbalancedChen.FirstExitHistoricalLevels

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.

Actual inherited fourth cap on a rank-six physical carrier. The selected
third coarse seed is bounded through its own ordered Gamma endpoint: five
original raw subset tents and the separate W3 branch. The fourth producer
then uses its actual finite maximum of the seed and every eligible producer
row. No fresh fifth candidate or fifth finite maximum is used here.
-/

namespace ImbalancedChen.P2InheritedFourthRaw31Embedding

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open HistoricalThirdCoarse
open P1ThirdFallbackSupport
open P1CoarseFirstCubeFallbackMargin
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation
open P2OriginalFourthCapProducerInterface
open Certificates.P2OriginalSixthElevenLogSemantics

private theorem v_eq_physical_tent (s : ℝ) : v s = tent s := by
  rw [v_eq_min]
  simp only [A, C, tent]
  congr 1
  ring

/-- The selected ordered third envelope embeds in raw31, with W3 separate. -/
theorem selected_third_original_le_oldCap (c : Cell) (t : Physical)
    (hc : PhysicalCell c t) :
    original (t 0) (t 1) (t 2) ≤ oldCap c t := by
  have hraw := hc.raw_envelope
  have h1 := hraw.2.1 1 (by decide : 1 ∈ Finset.Icc 1 31)
  have h3 := hraw.2.1 3 (by decide : 3 ∈ Finset.Icc 1 31)
  have h5 := hraw.2.1 5 (by decide : 5 ∈ Finset.Icc 1 31)
  have h6 := hraw.2.1 6 (by decide : 6 ∈ Finset.Icc 1 31)
  have h7 := hraw.2.1 7 (by decide : 7 ∈ Finset.Icc 1 31)
  have hs1 : subsetSum 1 t = t 0 := subsetSum_one t
  have hs3 : subsetSum 3 t = t 0 + t 1 := by
    norm_num [subsetSum, bit, Fin.sum_univ_succ]
  have hs5 : subsetSum 5 t = t 0 + t 2 := by
    norm_num [subsetSum, bit, Fin.sum_univ_succ]
  have hs6 : subsetSum 6 t = t 1 + t 2 := by
    norm_num [subsetSum, bit, Fin.sum_univ_succ]
  have hs7 : subsetSum 7 t = t 0 + t 1 + t 2 := by
    norm_num [subsetSum, bit, Fin.sum_univ_succ]
  have hW : B (t 2) = W t := by
    dsimp [B, cap, W]
    ring
  have hordered : Ordered (t 0) (t 1) (t 2) :=
    ⟨(hc.coordinates_pos 2).le, hc.order.2.2.2.1.le,
      hc.order.2.2.2.2.le, hc.largest.le⟩
  rw [original_eq_six hordered]
  change six (t 0) (t 1) (t 2) ≤ oldCap c t
  unfold six
  refine max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_))))
  · rw [v_eq_physical_tent, ← hs1]
    exact h1
  · rw [v_eq_physical_tent, ← hs3]
    exact h3
  · rw [v_eq_physical_tent, ← hs7]
    exact h7
  · rw [hW]
    exact hraw.1
  · rw [v_eq_physical_tent, ← hs5]
    exact h5
  · rw [v_eq_physical_tent, ← hs6]
    exact h6

/-- The actual supported third seed is below the same old physical cap. -/
theorem selected_third_seed_le_oldCap (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (c : Cell) (pre : List ℕ) (hlen : pre.length = 6)
    (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (he : 0 ≤ e)
    (hs : supported e chi m omega N (rosserAncestor 3 pre)) :
    seedExponent e chi m omega N (rosserAncestor 4 (rosserAncestor 5 pre)) ≤
      oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  let t := primeHistoryLogCoordinates N 6 pre
  let u := primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre)
  have hcoord (i : Fin 3) : u i = t (i.castLE (by omega : 3 ≤ 6)) := by
    have hp := congrFun
      (primeHistoryLogCoordinates_eq_historicalPrefixProject N
        (by omega : 3 ≤ 6) hlen) i
    simpa only [u, t, historicalPrefixProject] using hp
  have h0 : u 0 = t 0 := hcoord 0
  have h1 : u 1 = t 1 := hcoord 1
  have h2 : u 2 = t 2 := hcoord 2
  obtain ⟨j, hj, ht⟩ := hs.2
  have hbox := inBox_of_cell ht
  have hgamma := gamma_le_endpoint e (box m j) he hbox
    (by rw [h2]; exact (hc.coordinates_pos 2).le)
    (by rw [h2, h1]; exact hc.order.2.2.2.1.le)
    (by rw [h1, h0]; exact hc.order.2.2.2.2.le)
  have hendpoint : endpoint (u 0) (u 1) (u 2) =
      original (t 0) (t 1) (t 2) := by
    rw [h0, h1, h2]
    simp only [endpoint, if_pos hc.largest.le]
  have hthird : exponent e chi m u ≤ original (t 0) (t 1) (t 2) := by
    rw [exponent_on_cell e chi m u j hj ht]
    dsimp only [levelExponent]
    rw [hendpoint] at hgamma
    linarith only [hgamma, he]
  have hancestor :
      rosserAncestor 3 (rosserAncestor 4 (rosserAncestor 5 pre)) =
        rosserAncestor 3 pre := by
    rw [rosserAncestor_nested 3 4 (by omega),
      rosserAncestor_nested 3 5 (by omega)]
  change effectiveExponent e chi m omega N
    (rosserAncestor 3 (rosserAncestor 4 (rosserAncestor 5 pre))) ≤ _
  rw [hancestor, effectiveExponent, if_pos hs]
  exact hthird.trans (selected_third_original_le_oldCap c t hc)

/-- Every actual licensed producer row is compared through its raw mask. -/
theorem inherited_fourth_le_oldCap (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (c : Cell) (pre : List ℕ) (hlen : pre.length = 6)
    (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (he : 0 ≤ e)
    (hs : supported (e : ℝ) chi m omega N (rosserAncestor 3 pre))
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (hmask : ∀ r ∈ rows4, licensed4 r →
      (∑ i ∈ r.selected,
        (primeHistoryLogCoordinates N 6 pre) (i.castLE (by omega : 4 ≤ 6))) =
          subsetSum r.mask (primeHistoryLogCoordinates N 6 pre)) :
    inherited4 e chi m omega N rows4 licensed4 (rosserAncestor 5 pre) ≤
      oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  let t := primeHistoryLogCoordinates N 6 pre
  let parent4 := rosserAncestor 4 (rosserAncestor 5 pre)
  let u := primeHistoryLogCoordinates N 4 parent4
  have hlen4 : parent4.length = 4 := by
    simp only [parent4, rosserAncestor_length, rosserAncestor_length, hlen]
    omega
  have hanc4 : parent4 = rosserAncestor 4 pre := by
    simp only [parent4]
    rw [rosserAncestor_nested 4 5 (by omega)]
  have hcoord (i : Fin 4) : u i = t (i.castLE (by omega : 4 ≤ 6)) := by
    have hp := congrFun
      (primeHistoryLogCoordinates_eq_historicalPrefixProject N
        (by omega : 4 ≤ 6) hlen) i
    rw [← hanc4] at hp
    simpa only [u, t, historicalPrefixProject] using hp
  have hsum (r : ProducerRow) :
      (∑ i ∈ r.selected, u i) =
        (∑ i ∈ r.selected, t (i.castLE (by omega : 4 ≤ 6))) := by
    apply Finset.sum_congr rfl
    intro i _hi
    exact hcoord i
  have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hseed := selected_third_seed_le_oldCap (e : ℝ) chi m omega N
    c pre hlen hc heR hs
  have hrow : ∀ r ∈ rows4, producerEligible licensed4 r u →
      r.bufferedCandidate (e : ℝ) u ≤ oldCap c t := by
    intro r hr her
    have hgeom := hgeometry r hr her.1
    have hm : r.mask ∈ Finset.Icc 1 31 := by
      rcases hgeom with ⟨hlo, hhi, _⟩
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hvalue : r.bufferedCandidate (e : ℝ) u =
        tent (subsetSum r.mask t) - 2 * (e : ℝ) := by
      rw [r.bufferedCandidate_eq]
      rw [hsum r, hmask r hr her.1]
      rw [v_eq_physical_tent]
    calc
      r.bufferedCandidate (e : ℝ) u =
          tent (subsetSum r.mask t) - 2 * (e : ℝ) := hvalue
      _ ≤ tent (subsetSum r.mask t) := by linarith only [heR]
      _ ≤ oldCap c t := (hc.raw_envelope).2.1 r.mask hm
  change exponent4 (e : ℝ) chi m omega N rows4
    (producerEligible licensed4) (fun r => r.bufferedCandidate (e : ℝ)) parent4 ≤ _
  unfold exponent4
  rw [if_pos hlen4]
  exact finiteMax_le rows4 _ _ _ _ hseed hrow

end
end ImbalancedChen.P2InheritedFourthRaw31Embedding
