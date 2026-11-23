import ImbalancedChen.P1OriginalVariableFifthContinuation
import ImbalancedChen.P2OriginalSixthElevenLogSemantics

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.

The source fifth candidate is the literal pointwise min of the ascending and
descending selected planes, minus 2e. On an actual selected sixth PhysicalCell,
its nonempty selected Fin 5 set is one of the original masks 1..31. The
sixth source raw-envelope theorem then bounds this candidate by oldCap.
Eligibility retains the selected fifth cell, qVLo gateCheck and mesh membership.
No fifth or sixth retained carrier, parent seed bound, or nonempty cell is
asserted here.
-/

namespace ImbalancedChen.P2ActualFifthCandidateBelowSixthRaw31
noncomputable section
open Classical
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation
open Certificates.P2OriginalSixthElevenLogSemantics

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
  (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

/-- This is only the five-bit encoding fact. The full fifth row gate below
proves its selected set is nonempty before using this code. -/
private theorem nonempty_fin5_has_old_mask (I : Finset (Fin 5)) (hI : I.Nonempty) :
    ∃ mask ∈ Finset.Icc 1 31,
      ∀ i : Fin 5, bit mask i.val = decide (i ∈ I) := by
  have hcode : ∀ I : Finset (Fin 5), I.Nonempty →
      ∃ b : Fin 32, 0 < b.val ∧
        ∀ i : Fin 5, bit b.val i.val = decide (i ∈ I) := by decide
  obtain ⟨b, hb, hbits⟩ := hcode I hI
  refine ⟨b.val, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hbits⟩

private theorem eligible_selected_nonempty
    (r : FifthRow m) (u : Fin 5 → ℝ) (he : 0 ≤ (e : ℝ))
    (helig : eligible e chi m omega J5 r u) : r.selected.Nonempty := by
  have hhalf := (gateCheck_sound e m r u helig.2.1 helig.2.2).1
  by_contra hnot
  have hempty : r.selected = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro i hi
    exact hnot ⟨i, hi⟩
  have hcandidate : candidate (e : ℝ) r.selected u = 1 / 2 - 2 * (e : ℝ) := by
    norm_num [candidate, envelope, hempty]
  rw [hcandidate] at hhalf
  linarith

private theorem candidate_le_selected_tent
    (r : FifthRow m) (u : Fin 5 → ℝ) (he : 0 ≤ (e : ℝ)) :
    candidate (e : ℝ) r.selected u ≤
      tent (∑ i ∈ r.selected, u i) := by
  have henv : envelope r.selected u = tent (∑ i ∈ r.selected, u i) := by
    unfold envelope tent
    congr 1 <;> ring
  calc
    candidate (e : ℝ) r.selected u = envelope r.selected u - 2 * (e : ℝ) := rfl
    _ ≤ envelope r.selected u := by linarith
    _ = tent (∑ i ∈ r.selected, u i) := henv

/-- The actual sixth witness family is `PhysicalCell c t`, for any of its
eleven named cells. The eligible fifth row has its exact selected cell,
qVLo gate and mesh point; its candidate is bounded by a concrete old mask. -/
theorem eligible_fifth_candidate_has_raw31_mask
    (c : Cell) (pre : List ℕ) (hlen : pre.length = 6)
    (he : 0 ≤ (e : ℝ))
    (hcell : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (r : FifthRow m)
    (helig : eligible e chi m omega J5 r
      (primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre))) :
    let u := primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre)
    let t := primeHistoryLogCoordinates N 6 pre
    ∃ mask ∈ Finset.Icc 1 31,
      (∀ i : Fin 5, bit mask i.val = decide (i ∈ r.selected)) ∧
      (∑ i ∈ r.selected, u i) = subsetSum mask t ∧
      candidate (e : ℝ) r.selected u ≤ tent (subsetSum mask t) ∧
      tent (subsetSum mask t) ≤ oldCap c t := by
  dsimp only
  let u := primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre)
  let t := primeHistoryLogCoordinates N 6 pre
  have hI := eligible_selected_nonempty e chi m omega J5 r u he helig
  obtain ⟨mask, hmask, hbits⟩ := nonempty_fin5_has_old_mask r.selected hI
  have hcoord (i : Fin 5) : u i = t i.castSucc := by
    simpa [u, t] using
      (primeHistoryLogCoordinates_ancestor N hlen (by omega : 5 ≤ 6) i)
  have hsum : (∑ i ∈ r.selected, u i) = subsetSum mask t := by
    unfold subsetSum
    calc
      (∑ i ∈ r.selected, u i) = ∑ i ∈ r.selected, t i.castSucc := by
        apply Finset.sum_congr rfl
        intro i _
        exact hcoord i
      _ = ∑ i : Fin 5, if i ∈ r.selected then t i.castSucc else 0 := by simp
      _ = ∑ i : Fin 5, if bit mask i.val then t i.castSucc else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hbits i]
        by_cases hi : i ∈ r.selected <;> simp [hi]
  have htent : candidate (e : ℝ) r.selected u ≤ tent (subsetSum mask t) := by
    rw [← hsum]
    exact candidate_le_selected_tent e m r u he
  have hraw := hcell.raw_envelope
  exact ⟨mask, hmask, hbits, hsum, htent, hraw.2.1 mask hmask⟩

/-- All eligible actual fifth candidates are below the same original oldCap
on this sixth source cell, with no generic row-ceiling hypothesis. -/
theorem every_eligible_fifth_candidate_le_oldCap
    (c : Cell) (pre : List ℕ) (hlen : pre.length = 6)
    (he : 0 ≤ (e : ℝ))
    (hcell : PhysicalCell c (primeHistoryLogCoordinates N 6 pre)) :
    ∀ r ∈ rows5,
      eligible e chi m omega J5 r
        (primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre)) →
      candidate (e : ℝ) r.selected
        (primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre)) ≤
        oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  intro r _hr helig
  obtain ⟨mask, _hm, _hb, _hs, htent, hraw⟩ :=
    eligible_fifth_candidate_has_raw31_mask e chi m omega N J5
      c pre hlen he hcell r helig
  exact htent.trans hraw

/-- Consequently the sixth oldCap ceiling for actual exponent5 reduces to
the inherited fourth seed ceiling; every eligible fifth row is discharged by
the original raw31 envelope on the same PhysicalCell. -/
theorem exponent5_le_sixth_oldCap_of_inherited4_le
    (c : Cell) (pre : List ℕ) (hlen : pre.length = 6)
    (he : 0 ≤ (e : ℝ))
    (hcell : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (hseed : inherited4 e chi m omega N rows4 licensed4
      (rosserAncestor 5 pre) ≤ oldCap c (primeHistoryLogCoordinates N 6 pre)) :
    exponent5 e chi m omega N rows4 licensed4 J5 rows5
      (rosserAncestor 5 pre) ≤ oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  have ha : (rosserAncestor 5 pre).length = 5 := by
    rw [rosserAncestor_length, hlen]
    decide
  have hrows := every_eligible_fifth_candidate_le_oldCap e chi m omega N
    J5 rows5 c pre hlen he hcell
  have hmax := finiteMax_le rows5
    (fun r => eligible e chi m omega J5 r
      (primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre)))
    (fun r => candidate (e : ℝ) r.selected
      (primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre)))
    (inherited4 e chi m omega N rows4 licensed4 (rosserAncestor 5 pre))
    (oldCap c (primeHistoryLogCoordinates N 6 pre)) hseed hrows
  simpa only [exponent5, if_pos ha] using hmax

end
end ImbalancedChen.P2ActualFifthCandidateBelowSixthRaw31
