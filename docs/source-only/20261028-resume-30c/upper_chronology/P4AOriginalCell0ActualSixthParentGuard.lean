import ImbalancedChen.P4AOriginalCell0HalfOpenPrimeCarrier
import ImbalancedChen.Part3ActualRetainedAncestorTests
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual all-eleven sixth cap is not replaced by the raw envelope R.
On cell0 all eleven physical sixth actions are disjoint, so that cap equals
its actual fifth parent. The fifth/fourth/third frozen values are bounded
using their actual buffered candidates and actual supported third label.
The strict lower bound is recovered from the real rank-seven ancestor test.
-/
namespace ImbalancedChen.P4AOriginalCell0ActualSixthParentGuard
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope HistoricalThirdCoarse
open P4AOriginalCell0AffineChronology P4AOriginalCell0HalfOpenPrimeCarrier
open P2OriginalAscendingEighthCapDictionary P4AOriginalAscending14Literal42
open P4AOriginalActualElevenSixthCandidate P4AOriginalActualSeed7Slot15
open P4AOriginalAscendingCell0AfterSeed7
open P1OriginalVariableFifthContinuation P1OriginalVariableFourthContinuation

abbrev point8 (N : ℝ) (pre : List ℕ) := primeHistoryLogCoordinates N 8 pre
abbrev first6 (t : Fin 8 → ℝ) : Fin 6 → ℝ := fun i => t ⟨i.val, by omega⟩

/-- Literal row34 is strict: the old singleton-A cap is strictly below R. -/
theorem cell0_singleton_strict (t : Fin 8 → ℝ) (ht : literalRows t) :
    A (t 0) < R t := by
  have h := ht (34 : Fin 96)
  norm_num [sourceRow, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ] at h
  dsimp [A, R, d, C]
  linarith

/-- Every one of the eleven source cells licenses the old third mask6 at
A(t0). Cell0 instead has this mask equal to R>A(t0), so none applies. -/
theorem cell0_no_sixth_PhysicalCell (t : Fin 8 → ℝ) (ht : literalRows t)
    (c : Certificates.P2OriginalSixthElevenLogSemantics.Cell) :
    ¬ Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c (first6 t) := by
  intro hp
  have h6 := Certificates.P2OriginalSixthElevenLogSemantics.branchLicense_sound
    (hp.first3Branches 6 (by decide))
  have hd := (literalRows_cellGuard t ht).old_descending
  have heq : Certificates.P2OriginalSixthElevenLogSemantics.tent
      (Certificates.P2OriginalSixthElevenLogSemantics.subsetSum 6 (first6 t)) = R t := by
    have hdesc : 57 / 64 - 3 * (t 1 + t 2) / 2 ≤ (1 + (t 1 + t 2)) / 2 := by
      dsimp [A, C, d] at hd
      linarith
    norm_num [Certificates.P2OriginalSixthElevenLogSemantics.subsetSum,
      Certificates.P2OriginalSixthElevenLogSemantics.bit, first6,
      Fin.sum_univ_succ, Certificates.P2OriginalSixthElevenLogSemantics.tent]
    rw [min_eq_right hdesc]
    dsimp [R, d, C]
    ring
  rw [heq] at h6
  have hstrict := cell0_singleton_strict t ht
  change R t ≤ (1 + t 0) / 2 at h6
  dsimp [A] at hstrict
  linarith

private theorem physical6_ancestor (N : ℝ) (pre : List ℕ) (hlen : pre.length = 8) :
    physical6 N (rosserAncestor 6 pre) = first6 (point8 N pre) := by
  funext i
  exact primeHistoryLogCoordinates_ancestor N hlen (by decide : 6 ≤ 8) i

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
  (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
  (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

/-- Exact inheritance of the real fifth cap, not an equality with R. -/
theorem cell0_sixth_eq_actual_fifth (pre : List ℕ) (hlen : pre.length = 8)
    (ht : literalRows (point8 N pre)) :
    sixthSourceCap e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 6 pre) =
      actualParent5 e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 6 pre) := by
  unfold sixthSourceCap
  apply finiteMax_eq_seed_of_outside
  intro c _ hc
  have hp := hc.2.1
  rw [physical6_ancestor N pre hlen] at hp
  exact cell0_no_sixth_PhysicalCell _ ht c hp

private theorem empty_tent_le_R (t : Fin 8 → ℝ) (ht : literalRows t) : v 0 ≤ R t := by
  have hc := literalRows_cellGuard t ht
  have hpos : 0 < t 0 := hc.last_pos.trans (hc.order (by decide : (0 : Fin 8) < 7))
  have h0 := cell0_singleton_strict t ht
  rw [v_eq_min]
  dsimp [A, C] at *
  norm_num
  linarith

/-- Every subset cap through rank six is bounded on this very source cell,
including an empty selected mask. No row-wise cap bound is a premise. -/
theorem ancestor_subset_tent_le_R (pre : List ℕ) (hlen : pre.length = 8)
    (ht : literalRows (point8 N pre)) (k : ℕ) (hk : k ≤ 6)
    (I : Finset (Fin k)) :
    v (∑ i ∈ I, primeHistoryLogCoordinates N k (rosserAncestor k pre) i) ≤
      R (point8 N pre) := by
  let emb : Fin k ↪ Fin 6 := ⟨fun i => i.castLE hk, by intro i j h; exact Fin.ext (congrArg Fin.val h)⟩
  let J : Finset (Fin 6) := I.map emb
  have hsum : (∑ i ∈ I, primeHistoryLogCoordinates N k (rosserAncestor k pre) i) =
      P2OriginalAscendingEighthCapDictionary.subsetSum (point8 N pre) J := by
    simp only [J, P2OriginalAscendingEighthCapDictionary.subsetSum, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    exact primeHistoryLogCoordinates_ancestor N hlen (by omega : k ≤ 8) i
  rw [hsum]
  by_cases hj : J = ∅
  · simpa [hj, P2OriginalAscendingEighthCapDictionary.subsetSum] using empty_tent_le_R _ ht
  · exact old_tents_below_R (literalPattern 0) _
      (literalRows_cellGuard _ ht).old_planes J (by simp [oldMasks, hj])

/-- On the actual supported third ancestor Gamma is a lower enclosure of
the original third envelope R. The unsupported Theta fallback is excluded
by a genuine support witness, never silently substituted. -/
theorem supported_third_seed_le_R (he : 0 ≤ e) (pre : List ℕ) (hlen : pre.length = 8)
    (ht : literalRows (point8 N pre))
    (hs : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N (rosserAncestor 3 pre)) :
    P1CoarseFirstCubeFallbackMargin.effectiveExponent (e : ℝ) chi m omega N
      (rosserAncestor 3 pre) ≤ R (point8 N pre) := by
  obtain ⟨j, hj, hjt⟩ := hs.2
  have hc := literalRows_cellGuard _ ht
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hcoords (i : Fin 3) := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) i
  have hb := inBox_of_cell hjt
  have horder : Ordered
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 0)
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 1)
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2) := by
    simp only [hcoords]
    exact ⟨(hc.last_pos.trans (hc.order (by decide : (2 : Fin 8) < 7))).le,
      (hc.order (by decide : (1 : Fin 8) < 2)).le,
      (hc.order (by decide : (0 : Fin 8) < 1)).le, hc.largest.le⟩
  have hg := gamma_le_endpoint (e : ℝ) (box m j) heR hb
    horder.1 horder.2.1 horder.2.2.1
  have hend : endpoint
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 0)
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 1)
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2) = R (point8 N pre) := by
    simp only [hcoords, endpoint, if_pos hc.largest.le]
    exact hc.originalThird_eq
  rw [hend] at hg
  rw [P1CoarseFirstCubeFallbackMargin.effectiveExponent, if_pos hs,
    exponent_on_cell (e : ℝ) chi m _ j hj hjt]
  dsimp [levelExponent]
  linarith

/-- The actual fourth and fifth finite maxima keep their actual ancestor
seeds. Every new candidate is one of the source's bounded subset tents. -/
theorem actual_fifth_le_R (he : 0 ≤ e) (pre : List ℕ) (hlen : pre.length = 8)
    (ht : literalRows (point8 N pre))
    (hs : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N (rosserAncestor 3 pre)) :
    actualParent5 e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 6 pre) ≤
      R (point8 N pre) := by
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hseed := supported_third_seed_le_R e chi m omega N he pre hlen ht hs
  have h4len : (rosserAncestor 4 pre).length = 4 := by simp [hlen]
  have h5len : (rosserAncestor 5 pre).length = 5 := by simp [hlen]
  have h4 : exponent4 (e : ℝ) chi m omega N rows4 (producerEligible licensed4)
      (fun r => r.bufferedCandidate (e : ℝ)) (rosserAncestor 4 pre) ≤ R (point8 N pre) := by
    rw [exponent4, if_pos h4len]
    unfold profile4
    apply finiteMax_le
    · simpa [seedExponent, rosserAncestor_nested] using hseed
    · intro r _ _
      rw [r.bufferedCandidate_eq]
      have hr := ancestor_subset_tent_le_R N pre hlen ht 4 (by decide) r.selected
      linarith
  have hseed5 : inherited4 e chi m omega N rows4 licensed4 (rosserAncestor 5 pre) ≤
      R (point8 N pre) := by
    simpa only [inherited4, rosserAncestor_nested 4 5 (by decide)] using h4
  change exponent5 e chi m omega N rows4 licensed4 J5 rows5
    (rosserAncestor 5 (rosserAncestor 6 pre)) ≤ _
  rw [rosserAncestor_nested 5 6 (by decide), exponent5, if_pos h5len]
  apply finiteMax_le
  · exact hseed5
  · intro r _ _
    have hr := ancestor_subset_tent_le_R N pre hlen ht 5 (by decide) r.selected
    rw [candidate, envelope_eq_v]
    linarith

/-- All-eleven sixth values are the exact actual fifth predecessor here,
and hence bounded above by R, without replacing either by R. -/
theorem actual_sixth_le_R (he : 0 ≤ e) (pre : List ℕ) (hlen : pre.length = 8)
    (ht : literalRows (point8 N pre))
    (hs : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N (rosserAncestor 3 pre)) :
    sixthSourceCap e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 6 pre) ≤
      R (point8 N pre) := by
  rw [cell0_sixth_eq_actual_fifth e chi m omega N rows4 licensed4 J5 rows5 pre hlen ht]
  exact actual_fifth_le_R e chi m omega N rows4 licensed4 J5 rows5 he pre hlen ht hs

private theorem even_length_seven {α : Type*} (a : List α) (ha : a.length = 7) :
    evenListLength a = false := by
  have hpar : ∀ a : List α, evenListLength a = decide (Even a.length) := by
    intro a
    induction a with
    | nil => rfl
    | cons p ps ih => simp only [evenListLength, ih, List.length_cons, Nat.even_add_one, decide_not]
  rw [hpar, ha]
  decide

/-- An actual rank-eight retained state supplies the active rank-seven
ordinary test at the SAME frozen rank-six ancestor cap. -/
theorem actual_seventh_admissible (weight : ℕ → ℝ) (carrier : List ℕ)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 8
      (actual58Candidate e chi m omega N rows4 licensed4 J5 rows5)
      weight [] true 1 carrier) :
    ordinaryRosserPrefixAdmissible false
      (N ^ sixthSourceCap e chi m omega N rows4 licensed4 J5 rows5
        (rosserAncestor 6 s.selectedPrefix)) (rosserAncestor 7 s.selectedPrefix) := by
  have hlen := firstExitDepthFrontier_selected_length 8 _ weight [] carrier true 1 (by simp) s hs
  have h7 : (rosserAncestor 7 s.selectedPrefix).length = 7 := by simp [hlen]
  have hleaf := firstExitDepthFrontier_toLeaf_mem 8 _ weight [] carrier true 1 s hs
  have hpass := Part3.ActualRetainedAncestorTests.retained_leaf_ancestor_tests
    (actual58Candidate e chi m omega N rows4 licensed4 J5 rows5) weight carrier
    ⟨s.selectedPrefix, s.positive, s.mass⟩ hleaf 7 (by decide) (by omega)
  rw [even_length_seven _ h7,
    actual58_through_eight e chi m omega N rows4 licensed4 J5 rows5 false
      (rosserAncestor 7 s.selectedPrefix) (by omega)] at hpass
  have hdeep : ¬ (rosserAncestor 7 s.selectedPrefix).length ≤ 6 := by omega
  simpa only [sixthSourcePolicy, firstExitDepthSplicePolicy, if_neg hdeep,
    frozenParityRosserPolicy, ancestorFrozenPolicy, sixthSourceLevel,
    rosserAncestor_nested 6 7 (by decide), ordinaryParityRosserPolicy,
    Bool.false_eq_true, if_false, oddFirstExitPolicy, Bool.false_or, decide_eq_true_eq] using hpass

private theorem seventh_own_cube {Q : ℝ} (a : List ℕ) (hlen : a.length = 7)
    (hsort : a.Pairwise (· < ·)) (ha : ordinaryRosserPrefixAdmissible false Q a) :
    (a.prod : ℝ) * (a.headD 0 : ℝ)^2 < Q := by
  cases a with
  | nil => simp at hlen
  | cons p ps =>
    have hnd : (p :: ps).Nodup := hsort.nodup
    have hf : (p :: ps).toFinset.filter (fun q => p ≤ q) = (p :: ps).toFinset := by
      apply Finset.filter_eq_self.mpr
      intro q hq
      rcases List.mem_cons.mp (List.mem_toFinset.mp hq) with rfl | hq
      · exact le_rfl
      · exact ((List.pairwise_cons.mp hsort).1 q hq).le
    have hc : ((p :: ps).toFinset.filter (fun q => p ≤ q)).card = 7 := by
      rw [hf, List.toFinset_card_of_nodup hnd]
      exact hlen
    have hset : MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet Q
        (p :: ps).toFinset := ha.2
    have htest := hset p (by simp) (by rw [hc]; decide)
    rw [hf] at htest
    have hp : (p :: ps).toFinset.prod id = (p :: ps).prod := by
      simpa using List.prod_toFinset (fun p : ℕ => p) hnd
    simpa only [hp, List.headD_cons] using htest

/-- Exact logarithmic image of the ancestor-seven own-cube product. -/
private theorem rpow_H7 (hN : 1 < N) (pre : List ℕ) (hlen : pre.length = 8)
    (hpos : ∀ p ∈ pre, 0 < p) :
    N ^ oddCube (point8 N pre) 6 =
      ((rosserAncestor 7 pre).prod : ℝ) * ((rosserAncestor 7 pre).headD 0 : ℝ)^2 := by
  have h7 : (rosserAncestor 7 pre).length = 7 := by simp [hlen]
  have hp7 : ∀ p ∈ rosserAncestor 7 pre, 0 < p := fun p hp => hpos p (List.mem_of_mem_drop hp)
  have hc (i : Fin 7) := primeHistoryLogCoordinates_ancestor N hlen (by decide : 7 ≤ 8) i
  have hsum : oddCube (point8 N pre) 6 =
      (∑ i : Fin 7, primeHistoryLogCoordinates N 7 (rosserAncestor 7 pre) i) +
        2 * primeHistoryLogCoordinates N 7 (rosserAncestor 7 pre) 6 := by
    simp only [hc]
    norm_num [oddCube, prefixSum, Finset.sum_filter, Fin.sum_univ_succ, point8]
    ring
  have hpow := rpow_primeHistoryLogCoordinates N hN h7 hp7 (6 : Fin 7)
  rw [primeHistoryTuple_last h7] at hpow
  have hsq : N ^ (2 * primeHistoryLogCoordinates N 7 (rosserAncestor 7 pre) 6) =
      ((rosserAncestor 7 pre).headD 0 : ℝ)^2 := by
    rw [mul_comm, Real.rpow_mul (zero_lt_one.trans hN).le, hpow]
    norm_num
  rw [hsum, Real.rpow_add (zero_lt_one.trans hN),
    rpow_sum_primeHistoryLogCoordinates N hN h7 hp7, hsq]

/-- Actual recursion, actual prime carrier, actual seventh ancestor test:
this removes the lower half of CurrentParentGuard as an external premise. -/
theorem actual_H7_lt_sixth (Nnat cap : ℕ) (hident : N = (Nnat : ℝ)) (hN : 1 < N)
    (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 8
      (actual58Candidate e chi m omega N rows4 licensed4 J5 rows5)
      (fun p => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse Nnat cap w z)) :
    oddCube (point8 N s.selectedPrefix) 6 <
      sixthSourceCap e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 6 s.selectedPrefix) := by
  have hlen := firstExitDepthFrontier_selected_length 8 _ _ []
    (roughPrimeUniverse Nnat cap w z) true 1 (by simp) s hs
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 8 _ _ _ s hs
  have hsort : s.selectedPrefix.Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using
      (roughPrimeUniverse_pairwise_gt Nnat cap w z).sublist hsub
  have hp : ∀ p ∈ s.selectedPrefix, 0 < p := by
    intro p hp
    exact (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))).pos
  have hsort7 : (rosserAncestor 7 s.selectedPrefix).Pairwise (· < ·) :=
    hsort.sublist (List.drop_sublist _ _)
  have hadm := actual_seventh_admissible e chi m omega N rows4 licensed4 J5 rows5
    _ _ s hs
  have hcube := seventh_own_cube _ (by simp [hlen]) hsort7 hadm
  rw [← rpow_H7 N hN s.selectedPrefix hlen hp] at hcube
  exact (Real.rpow_lt_rpow_left_iff hN).mp hcube


/-- Add only the original finite third-label/rough-activation licences to
the prior cell0 inner bank. The tests still precede N; none asks for a
CurrentParentGuard, a sixth cap value, or a final source inequality. -/
def parentBoxes (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) : Finset (BoxIndex m) :=
  (innerBoxes e m).filter fun j =>
    historicalPrefixProject (by decide : 3 ≤ 8) j ∈ cells (e : ℝ) chi m ∧
      omega ≤ logPrimeMeshLo 0 (19 / 96) m j 2


private theorem qLo_native (m : ℕ) (j : BoxIndex m) (i : Fin 8) :
    qLo m j i = qLogPrimeMeshLo 0 (19 / 96) m j i := by
  dsimp [qLo, qPoint, qLogPrimeMeshLo, qLogPrimeMeshPoint]
  ring

private theorem qHi_native (m : ℕ) (j : BoxIndex m) (i : Fin 8) :
    qHi m j i = qLogPrimeMeshHi 0 (19 / 96) m j i := by
  dsimp [qHi, qPoint, qLogPrimeMeshHi, qLogPrimeMeshPoint]
  push_cast
  ring

/-- With the original mesh-width and rough-cutoff choices the added third
licences are automatic from the prior 96-row inner tests. Thus the parent
proof does not restrict the former carrier to an artificially easier set. -/
theorem innerBox_mem_parentBoxes (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (homega : omega ≤ 1 / 100) (j : BoxIndex m) (hj : j ∈ innerBoxes e m) :
    j ∈ parentBoxes e chi m omega := by
  have hi := (mem_innerBoxes e m j).mp hj
  have hcut := hi.2 (1 : Fin 96)
  have horder01 := hi.2 (3 : Fin 96)
  have horder12 := hi.2 (4 : Fin 96)
  norm_num [rowLowerQ, sourceRow, P4AOriginalAscendingCell0Literal96.rows,
    Fin.sum_univ_succ] at hcut horder01 horder12
  let jp := historicalPrefixProject (by decide : 3 ≤ 8) j
  have hlo (i : Fin 3) : qLogPrimeMeshLo 0 (19 / 96) m jp i =
      qLo m j ⟨i.val, by omega⟩ := by
    rw [qLo_native]
    rfl
  have hhi (i : Fin 3) : qLogPrimeMeshHi 0 (19 / 96) m jp i =
      qHi m j ⟨i.val, by omega⟩ := by
    rw [qHi_native]
    rfl
  let stepQ : ℚ := (19 / 96) / ((m : ℚ) + 1)
  have hstepQ : 0 ≤ stepQ := by dsimp [stepQ]; positivity
  have hdelta (i : Fin 8) : qHi m j i - qLo m j i = stepQ := by
    dsimp [qHi, qLo, qPoint, stepQ]
    push_cast
    ring
  have hwidth : (box m jp).width = stepQ := by
    simp only [RationalBox.width, box, hlo, hhi, hdelta, max_self, max_eq_right hstepQ]
  have hwidthR : ((box m jp).width : ℝ) ≤ chi := by
    rw [hwidth]
    have hcast : (stepQ : ℝ) = logPrimeMeshStep 0 (19 / 96) m := by
      norm_num [stepQ, logPrimeMeshStep]
    rw [hcast]
    exact hstep
  have hc : jp ∈ cells (e : ℝ) chi m := by
    apply (mem_cells (e : ℝ) chi m jp).mpr
    refine ⟨?_, ?_, ?_, ?_, ?_, hwidthR⟩
    · change (box m jp).lx ≤ (box m jp).ux ∧
        (box m jp).ly ≤ (box m jp).uy ∧ (box m jp).lz ≤ (box m jp).uz
      simp only [box, hlo, hhi]
      exact ⟨by linarith [hdelta 0], by linarith [hdelta 1], by linarith [hdelta 2]⟩
    · simpa only [box, hlo] using (show (0 : ℚ) ≤ qLo m j 2 by linarith)
    · simpa only [box, hlo, hhi] using (show qHi m j 2 ≤ qLo m j 1 by linarith)
    · simpa only [box, hlo, hhi] using (show qHi m j 1 ≤ qLo m j 0 by linarith)
    · have hs : ((qHi m j 0 : ℚ) : ℝ) ≤ (19 / 96 : ℝ) - 4 * (e : ℝ) := by
        exact_mod_cast hi.1
      simpa only [box, hhi, VariableEnvelope.extendedFirstStop] using hs
  apply Finset.mem_filter.mpr
  refine ⟨hj, hc, ?_⟩
  have hlowQ : (1 / 100 : ℚ) ≤ qLo m j 2 := by linarith
  have hlowR : (1 / 100 : ℝ) ≤ logPrimeMeshLo 0 (19 / 96) m j 2 := by
    rw [← congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m j) 2, ← qLo_native]
    exact_mod_cast hlowQ
  exact homega.trans hlowR

theorem parentBox_supported (hN : 1 < N) (pre : List ℕ) (hlen : pre.length = 8)
    (hpos : ∀ p ∈ pre, 0 < p) (j : BoxIndex m)
    (hj : j ∈ parentBoxes e chi m omega)
    (ht : point8 N pre ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N (rosserAncestor 3 pre) := by
  have hlic : historicalPrefixProject (by decide : 3 ≤ 8) j ∈ cells (e : ℝ) chi m ∧
      omega ≤ logPrimeMeshLo 0 (19 / 96) m j 2 := (Finset.mem_filter.mp hj).2
  have h3 : (rosserAncestor 3 pre).length = 3 := by simp [hlen]
  have hp3 : ∀ p ∈ rosserAncestor 3 pre, 0 < p := fun p hp => hpos p (List.mem_of_mem_drop hp)
  have hcoords := primeHistoryLogCoordinates_eq_historicalPrefixProject N
    (by decide : 3 ≤ 8) hlen
  have ht3 : primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) ∈
      logPrimeMeshCell 0 (19 / 96) m (historicalPrefixProject (by decide : 3 ≤ 8) j) := by
    rw [hcoords]
    exact mem_logPrimeMeshCell_historicalPrefixProject (by decide : 3 ≤ 8) ht
  have hrough : omega ≤ primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2 := by
    rw [primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) (2 : Fin 3)]
    exact hlic.2.trans (mem_logPrimeMeshCell.mp ht (2 : Fin 8)).1
  have hpow := rpow_primeHistoryLogCoordinates N hN h3 hp3 (2 : Fin 3)
  refine ⟨⟨h3, ?_⟩, ?_⟩
  · rw [← hpow]
    exact Real.rpow_le_rpow_of_exponent_le hN.le hrough
  · exact ⟨historicalPrefixProject (by decide : 3 ≤ 8) j, hlic.1, ht3⟩

/-- Actual retained frontier with the additional finite third licences.
No ideal or post-rounded replacement for an actual parent value occurs. -/
def parentSelectedFrontier (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (Nnat cap : ℕ) (w z : ℝ) (parent : Bool → List ℕ → Bool) :
    List (FirstExitDepthState ℕ) :=
  (selectedFrontier e m Nnat cap w z parent).filter fun s => decide
    (∃ j ∈ parentBoxes e chi m omega,
      primeHistoryTuple 8 s.selectedPrefix ∈ primeBox m Nnat j)

/-- Both halves of CurrentParentGuard are now consequences of the real
carrier and real frozen predecessor. The actual sixth cap need not equal R. -/
theorem actual_CurrentParentGuard (he : 0 ≤ e) (Nnat cap : ℕ) (hN : 1 < Nnat)
    (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ parentSelectedFrontier e chi m omega Nnat cap w z
      (actual58Candidate e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5)) :
    CurrentParentGuard (point8 (Nnat : ℝ) s.selectedPrefix)
      (sixth e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5
        (rosserAncestor 6 s.selectedPrefix)) := by
  have hmem : s ∈ selectedFrontier e m Nnat cap w z
      (actual58Candidate e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5) ∧
      ∃ j ∈ parentBoxes e chi m omega,
        primeHistoryTuple 8 s.selectedPrefix ∈ primeBox m Nnat j := by
    simpa only [parentSelectedFrontier, List.mem_filter, decide_eq_true_eq] using hs
  obtain ⟨hbase, j, hj, hp⟩ := hmem
  obtain ⟨hlen, _hpass, hrows, _hstop⟩ := selectedFrontier_actual_source e m Nnat cap hN w z
    (actual58Candidate e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5) s hbase
  have hfront : s ∈ firstExitDepthFrontier 8
      (actual58Candidate e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5)
      (fun p => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse Nnat cap w z) := by
    exact (List.mem_filter.mp hbase).1
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 8 _ _ _ s hfront
  have hpos : ∀ p ∈ s.selectedPrefix, 0 < p := by
    intro p hp
    exact (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))).pos
  have hNr : (1 : ℝ) < Nnat := by exact_mod_cast hN
  have hsupport := parentBox_supported e chi m omega (Nnat : ℝ) hNr s.selectedPrefix
    hlen hpos j hj (primeBox_log hN j _ hp)
  have hlower := actual_H7_lt_sixth e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5
    Nnat cap rfl hNr w z s hfront
  have hupper := actual_sixth_le_R e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5
    he s.selectedPrefix hlen hrows hsupport
  exact ⟨by simpa only [sixth, actualSixth] using hlower,
    by simpa only [sixth, actualSixth] using hupper⟩

/-- Actual slot16 on the qualified cell0 bank. No firstStop, source-row,
ancestor-admission, or CurrentParentGuard premise remains in this theorem. -/
theorem parentSelectedFrontier_slot16 (he : 0 ≤ e) (Nnat cap : ℕ) (hN : 1 < Nnat)
    (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ parentSelectedFrontier e chi m omega Nnat cap w z
      (actual58Candidate e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5)) :
    P4AOriginalPrior58Chronology.slot16 (Nnat : ℝ)
      (sixth e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5) s.selectedPrefix =
        M (point8 (Nnat : ℝ) s.selectedPrefix) := by
  have hbase : s ∈ selectedFrontier e m Nnat cap w z
      (actual58Candidate e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5) :=
    (List.mem_filter.mp hs).1
  exact selected_actual_slot16 e chi m omega Nnat cap w z rows4 licensed4 J5 rows5 hN s hbase
    (actual_CurrentParentGuard e chi m omega rows4 licensed4 J5 rows5 he Nnat cap hN w z s hs)


/-- The original half-open cell0 bank already supplies all parent licences
at the stated common mesh and rough cutoff. Actual frozen sixth values,
not raw or ideal replacements, satisfy CurrentParentGuard. -/
theorem original_bank_CurrentParentGuard (he : 0 ≤ e)
    (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi) (homega : omega ≤ 1 / 100)
    (Nnat cap : ℕ) (hN : 1 < Nnat) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selectedFrontier e m Nnat cap w z
      (actual58Candidate e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5)) :
    CurrentParentGuard (point8 (Nnat : ℝ) s.selectedPrefix)
      (sixth e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5
        (rosserAncestor 6 s.selectedPrefix)) := by
  have hbox : ∃ j ∈ innerBoxes e m,
      primeHistoryTuple 8 s.selectedPrefix ∈ primeBox m Nnat j := by
    exact of_decide_eq_true (List.mem_filter.mp hs).2
  obtain ⟨j, hj, hp⟩ := hbox
  have hsparent : s ∈ parentSelectedFrontier e chi m omega Nnat cap w z
      (actual58Candidate e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5) := by
    apply List.mem_filter.mpr
    exact ⟨hs, decide_eq_true ⟨j, innerBox_mem_parentBoxes e chi m omega hstep homega j hj, hp⟩⟩
  exact actual_CurrentParentGuard e chi m omega rows4 licensed4 J5 rows5
    he Nnat cap hN w z s hsparent

/-- Cell0 slot16 now follows from actual retained arithmetic membership,
with no source-row, firstStop or CurrentParentGuard assumption. -/
theorem original_bank_slot16 (he : 0 ≤ e)
    (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi) (homega : omega ≤ 1 / 100)
    (Nnat cap : ℕ) (hN : 1 < Nnat) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selectedFrontier e m Nnat cap w z
      (actual58Candidate e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5)) :
    P4AOriginalPrior58Chronology.slot16 (Nnat : ℝ)
      (sixth e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5) s.selectedPrefix =
        M (point8 (Nnat : ℝ) s.selectedPrefix) := by
  exact selected_actual_slot16 e chi m omega Nnat cap w z rows4 licensed4 J5 rows5 hN s hs
    (original_bank_CurrentParentGuard e chi m omega rows4 licensed4 J5 rows5
      he hstep homega Nnat cap hN w z s hs)

end
end ImbalancedChen.P4AOriginalCell0ActualSixthParentGuard
