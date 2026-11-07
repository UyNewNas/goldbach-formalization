import ImbalancedChen.P2InheritedFourthRaw31Embedding
import ImbalancedChen.P2ActualFifthCandidateBelowSixthRaw31

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.

The missing producer-mask dictionary is a finite identity between the
literal `Nat.testBit` selection of a fourth ProducerRow and the original
five-bit raw31 subset.  It is proved here, rather than required from a
caller.  On the same selected rank-six physical history this discharges
the fourth seed ceiling and hence the actual fifth finite-maximum ceiling.

The resulting bound is on `level5`, the physical level; no auxiliary
factorization cover or replacement coefficient is introduced.  The
selected-third support and actual producer geometry remain explicit.
There is no assertion of an SW estimate, an active HB chart, a retained
carrier, or a completed prime-product insertion.
-/

namespace ImbalancedChen.P2ActualFifthRaw31SupportCeiling

noncomputable section
open Classical
open scoped BigOperators
open HistoricalThirdCoarse
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation
open Certificates.P2OriginalSixthElevenLogSemantics

/-- The producer's masks are exactly 9..15.  On these seven literal
natural numbers, `testBit` and the raw source's quotient/modulo bit agree;
the fifth raw bit is zero.  The finite decision does no numerical
integration or certificate replay. -/
private theorem producer_mask_bits (mask : ℕ) (hlo : 9 ≤ mask)
    (hhi : mask ≤ 15) :
    (∀ i : Fin 4, Nat.testBit mask i.val = bit mask i.val) ∧
      bit mask 4 = false := by
  have table : ∀ b : Fin 16, 9 ≤ b.val →
      (∀ i : Fin 4, Nat.testBit b.val i.val = bit b.val i.val) ∧
        bit b.val 4 = false := by decide
  exact table ⟨mask, by omega⟩ hlo

/-- A fourth producer's selected sum is its actual numeric raw31 mask,
after rank-four-to-six coordinate inclusion.  In particular no arbitrary
`hmask` identification is left to the fifth-parent caller. -/
theorem producer_selected_sum_eq_raw31 (r : ProducerRow) (hr : r.Geometry)
    (t : Physical) :
    (∑ i ∈ r.selected, t (i.castLE (by omega : 4 ≤ 6))) =
      subsetSum r.mask t := by
  have hb := producer_mask_bits r.mask hr.1 hr.2.1
  calc
    (∑ i ∈ r.selected, t (i.castLE (by omega : 4 ≤ 6))) =
        ∑ i : Fin 4,
          if Nat.testBit r.mask i.val then
            t (i.castLE (by omega : 4 ≤ 6)) else 0 := by
      simp only [ProducerRow.selected, Finset.sum_filter]
    _ = ∑ i : Fin 4,
          if bit r.mask i.val then
            t (i.castLE (by omega : 4 ≤ 6)) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hb.1 i]
    _ = subsetSum r.mask t := by
      symm
      unfold subsetSum
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, hb.2,
        Bool.false_eq_true, if_false, add_zero] <;> rfl

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
  (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

/-- The earlier inherited-fourth raw31 result now needs only actual
selected-third support and each licensed row's source geometry. -/
theorem actual_inherited_fourth_le_raw31
    (c : Cell) (pre : List ℕ) (hlen : pre.length = 6)
    (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (he : 0 ≤ e)
    (hs : supported (e : ℝ) chi m omega N (rosserAncestor 3 pre))
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry) :
    inherited4 e chi m omega N rows4 licensed4 (rosserAncestor 5 pre) ≤
      oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  apply P2InheritedFourthRaw31Embedding.inherited_fourth_le_oldCap
    e chi m omega N rows4 licensed4 c pre hlen hc he hs hgeometry
  intro r hr hlicensed
  exact producer_selected_sum_eq_raw31 r (hgeometry r hr hlicensed)
    (primeHistoryLogCoordinates N 6 pre)

/-- On each of the original eleven sixth cells the actual fifth
finite maximum is below the physical old comparison cap.  The seed
ceiling and every fifth row ceiling are proved, not supplied as premises. -/
theorem actual_fifth_exponent_le_raw31
    (c : Cell) (pre : List ℕ) (hlen : pre.length = 6)
    (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (he : 0 ≤ e)
    (hs : supported (e : ℝ) chi m omega N (rosserAncestor 3 pre))
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry) :
    exponent5 e chi m omega N rows4 licensed4 J5 rows5
        (rosserAncestor 5 pre) ≤
      oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hseed := actual_inherited_fourth_le_raw31 e chi m omega N
    rows4 licensed4 c pre hlen hc he hs hgeometry
  exact P2ActualFifthCandidateBelowSixthRaw31.exponent5_le_sixth_oldCap_of_inherited4_le
    e chi m omega N rows4 licensed4 J5 rows5 c pre hlen heR hc hseed

/-- Convert the same-history exponent ceiling to the literal physical
`level5 = N^exponent5`.  This is the level usable in the coefficient
support argument; it is not silently replaced by an auxiliary exponent. -/
theorem actual_fifth_physical_level_le_raw31
    (hN : 1 ≤ N)
    (c : Cell) (pre : List ℕ) (hlen : pre.length = 6)
    (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (he : 0 ≤ e)
    (hs : supported (e : ℝ) chi m omega N (rosserAncestor 3 pre))
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry) :
    level5 e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 5 pre) ≤
      N ^ oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  exact Real.rpow_le_rpow_of_exponent_le hN
    (actual_fifth_exponent_le_raw31 e chi m omega N rows4 licensed4 J5 rows5
      c pre hlen hc he hs hgeometry)

/-- Both inherited physical levels belong to the same source history.
The fifth continuation preserves its fourth ancestor and remains below
the exact oldCap of the selected sixth physical cell. -/
theorem actual_fourth_fifth_physical_support_chain
    (hN : 1 ≤ N)
    (c : Cell) (pre : List ℕ) (hlen : pre.length = 6)
    (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (he : 0 ≤ e)
    (hs : supported (e : ℝ) chi m omega N (rosserAncestor 3 pre))
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry) :
    producerLevel4 (e : ℝ) chi m omega N rows4 licensed4 (rosserAncestor 4 pre) ≤
        level5 e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 5 pre) ∧
      level5 e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 5 pre) ≤
        N ^ oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  constructor
  · have h := fourthLevel_le_fifthLevel e chi m omega N rows4 licensed4 J5 rows5
      hN (rosserAncestor 5 pre)
    simpa only [rosserAncestor_nested 4 5 (by omega)] using h
  · exact actual_fifth_physical_level_le_raw31 e chi m omega N rows4 licensed4
      J5 rows5 hN c pre hlen hc he hs hgeometry

end
end ImbalancedChen.P2ActualFifthRaw31SupportCeiling
