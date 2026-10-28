import ImbalancedChen.P4AOriginalAscendingCell2Affine
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual next ascending cell2: finite rational whole-box tests, true prime
carrier and true inherited all-eleven sixth values feed chronological
slot16. This is not the complete fourteen-cell or full58/full87 policy.
-/
namespace ImbalancedChen.P4AOriginalAscendingCell2ActualChronology
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope HistoricalThirdCoarse
open P4AOriginalCell0HalfOpenPrimeCarrier P4AOriginalAscendingCell2Affine
open P2OriginalAscendingEighthCapDictionary P4AOriginalAscending14Literal42
open P4AOriginalActualElevenSixthCandidate P4AOriginalActualSeed7Slot15
open P4AOriginalAscendingCell0AfterSeed7
open P1OriginalVariableFifthContinuation P1OriginalVariableFourthContinuation

abbrev point8 (N : ℝ) (pre : List ℕ) := primeHistoryLogCoordinates N 8 pre
abbrev first6 (t : Fin 8 → ℝ) : Fin 6 → ℝ := fun i => t ⟨i.val, by omega⟩

/-- Literal row34 is strict: the old singleton-A cap is strictly below R. -/
theorem cell2_singleton_strict (t : Fin 8 → ℝ) (ht : literalRows t) :
    A (t 0) < R t := by
  have h := ht (34 : Fin 96)
  norm_num [sourceRow, rows2, P4AOriginalAscendingCell1Affine.rows1, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ] at h
  dsimp [A, R, d, C]
  linarith

/-- Every one of the eleven source cells licenses the old third mask6 at
A(t0). Cell2 instead has this mask equal to R>A(t0), so none applies. -/
theorem cell2_no_sixth_PhysicalCell (t : Fin 8 → ℝ) (ht : literalRows t)
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
  have hstrict := cell2_singleton_strict t ht
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
theorem cell2_sixth_eq_actual_fifth (pre : List ℕ) (hlen : pre.length = 8)
    (ht : literalRows (point8 N pre)) :
    sixthSourceCap e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 6 pre) =
      actualParent5 e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 6 pre) := by
  unfold sixthSourceCap
  apply finiteMax_eq_seed_of_outside
  intro c _ hc
  have hp := hc.2.1
  rw [physical6_ancestor N pre hlen] at hp
  exact cell2_no_sixth_PhysicalCell _ ht c hp

private theorem empty_tent_le_R (t : Fin 8 → ℝ) (ht : literalRows t) : v 0 ≤ R t := by
  have hc := literalRows_cellGuard t ht
  have hpos : 0 < t 0 := hc.last_pos.trans (hc.order (by decide : (0 : Fin 8) < 7))
  have h0 := cell2_singleton_strict t ht
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
  · exact old_tents_below_R (literalPattern 2) _
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
  rw [cell2_sixth_eq_actual_fifth e chi m omega N rows4 licensed4 J5 rows5 pre hlen ht]
  exact actual_fifth_le_R e chi m omega N rows4 licensed4 J5 rows5 he pre hlen ht hs


/-- The rational infimum of each original cell2 row over one closed box. -/
def rowLower2 (m : ℕ) (j : BoxIndex m) (k : Fin 96) : ℚ :=
  (rows2 k).2 0 + ∑ i : Fin 8,
    (rows2 k).2 i.succ * (if 0 ≤ (rows2 k).2 i.succ then qLo m j i else qHi m j i)

/-- All tests are finite geometric/actual third licences before N. -/
def bank2 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) : Finset (BoxIndex m) :=
  Finset.univ.filter fun j =>
    qHi m j 0 ≤ 19 / 96 - 4 * e ∧
    (∀ k : Fin 96, 0 < rowLower2 m j k) ∧
    historicalPrefixProject (by decide : 3 ≤ 8) j ∈ cells (e : ℝ) chi m ∧
    omega ≤ logPrimeMeshLo 0 (19 / 96) m j 2

private theorem qlo_cast (m : ℕ) (j : BoxIndex m) (i : Fin 8) :
    (qLo m j i : ℝ) = logPrimeMeshLo 0 (19 / 96) m j i := by
  norm_num [qLo, qPoint, logPrimeMeshLo, logPrimeMeshPoint, logPrimeMeshStep]
  push_cast
  ring

private theorem qhi_cast (m : ℕ) (j : BoxIndex m) (i : Fin 8) :
    (qHi m j i : ℝ) = logPrimeMeshHi 0 (19 / 96) m j i := by
  norm_num [qHi, qPoint, logPrimeMeshHi, logPrimeMeshPoint, logPrimeMeshStep]
  push_cast
  ring

/-- Real exact affine lower bound, using the original row slopes. -/
theorem rowLower2_le (m : ℕ) (j : BoxIndex m) (k : Fin 96) (t : Fin 8 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    (rowLower2 m j k : ℝ) ≤ evalRow (rows2 k).2 t := by
  unfold rowLower2 evalRow P4AOriginalSeed7Unequal15Literal.evalAffine
  simp only [Rat.cast_add, Rat.cast_sum, Rat.cast_mul]
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  have hi := mem_logPrimeMeshCell.mp ht i
  split_ifs with hsign
  · rw [qlo_cast]
    exact mul_le_mul_of_nonneg_left hi.1 (by exact_mod_cast hsign)
  · rw [qhi_cast]
    exact mul_le_mul_of_nonpos_left hi.2.le (by exact_mod_cast (le_of_not_ge hsign))

/-- This carrier uses original Ico power boxes and target-excluded prime
universe, retaining the incoming sign, mass and unprocessed primes. -/
def selected2 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (Nnat cap : ℕ)
    (w z : ℝ) (parent : Bool → List ℕ → Bool) : List (FirstExitDepthState ℕ) :=
  (firstExitDepthFrontier 8 parent (fun p => 1 / ((p : ℝ) - 1)) [] true 1
    (roughPrimeUniverse Nnat cap w z)).filter fun s => decide
      (∃ j ∈ bank2 e chi m omega,
        primeHistoryTuple 8 s.selectedPrefix ∈ primeBox m Nnat j)

/-- Both firstStop and actual third support follow from the same finite
box label; neither is a subsequent invented parent-cap hypothesis. -/
theorem bank2_rows_stop_support (hN : 1 < N) (pre : List ℕ) (hlen : pre.length = 8)
    (hpos : ∀ p ∈ pre, 0 < p) (j : BoxIndex m)
    (hj : j ∈ bank2 e chi m omega)
    (ht : point8 N pre ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    literalRows (point8 N pre) ∧
    firstStop (e : ℝ) m N (rosserAncestor 1 pre) ∧
    P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N (rosserAncestor 3 pre) := by
  have hb : qHi m j 0 ≤ 19 / 96 - 4 * e ∧
      (∀ k : Fin 96, 0 < rowLower2 m j k) ∧
      historicalPrefixProject (by decide : 3 ≤ 8) j ∈ cells (e : ℝ) chi m ∧
      omega ≤ logPrimeMeshLo 0 (19 / 96) m j 2 := (Finset.mem_filter.mp hj).2
  have hr : literalRows (point8 N pre) := by
    intro k
    have hq : (0 : ℝ) < (rowLower2 m j k : ℝ) := by exact_mod_cast hb.2.1 k
    exact hq.trans_le (rowLower2_le m j k _ ht)
  have hfirst : firstStop (e : ℝ) m N (rosserAncestor 1 pre) := by
    have hx := mem_logPrimeMeshCell.mp ht (0 : Fin 8)
    have hid := primeHistoryLogCoordinates_ancestor N hlen (by decide : 1 ≤ 8) (0 : Fin 1)
    have hstopR : logPrimeMeshHi 0 (19 / 96) m j 0 ≤ extendedFirstStop - 4 * (e : ℝ) := by
      rw [← qhi_cast]
      dsimp [extendedFirstStop]
      exact_mod_cast hb.1
    refine ⟨j 0, ?_, ?_, ?_⟩
    · simpa only [hid, logPrimeMeshLo] using hx.1
    · simpa only [hid, logPrimeMeshHi] using hx.2
    · simpa only [logPrimeMeshHi] using hstopR
  have h3 : (rosserAncestor 3 pre).length = 3 := by simp [hlen]
  have hp3 : ∀ p ∈ rosserAncestor 3 pre, 0 < p := fun p hp => hpos p (List.mem_of_mem_drop hp)
  have hcoords := primeHistoryLogCoordinates_eq_historicalPrefixProject N (by decide : 3 ≤ 8) hlen
  have ht3 : primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) ∈
      logPrimeMeshCell 0 (19 / 96) m (historicalPrefixProject (by decide : 3 ≤ 8) j) := by
    rw [hcoords]
    exact mem_logPrimeMeshCell_historicalPrefixProject (by decide : 3 ≤ 8) ht
  have hrough : omega ≤ primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2 := by
    rw [primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) (2 : Fin 3)]
    exact hb.2.2.2.trans (mem_logPrimeMeshCell.mp ht (2 : Fin 8)).1
  have hpow := rpow_primeHistoryLogCoordinates N hN h3 hp3 (2 : Fin 3)
  refine ⟨hr, hfirst, ⟨h3, ?_⟩, ?_⟩
  · rw [← hpow]
    exact Real.rpow_le_rpow_of_exponent_le hN.le hrough
  · exact ⟨historicalPrefixProject (by decide : 3 ≤ 8) j, hb.2.2.1, ht3⟩

/-- The next source cell is disjoint from the adopted seed7, by their
literal opposite mask26 planes and strict old descending winner. -/
theorem cell2_not_seed7 (pre : List ℕ) (hlen : pre.length = 8)
    (hr : literalRows (point8 N pre)) :
    ¬ sourceSeed7 e chi m omega N rows4 licensed4 J5 rows5 pre := by
  intro hs
  exact cell0_seed7_affine_disjoint _ (literalRows_core _ hr) hs.2.1

/-- Chronology on cell2: actual slot15 inherits the actual all-eleven
sixth cap, then slot16 raises to the actual original ascending M. -/
theorem cell2_slot16 (pre : List ℕ) (hlen : pre.length = 8)
    (hr : literalRows (point8 N pre))
    (hp : CurrentParentGuard (point8 N pre)
      (sixth e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 6 pre))) :
    P4AOriginalPrior58Chronology.slot16 N
      (sixth e chi m omega N rows4 licensed4 J5 rows5) pre = M (point8 N pre) := by
  let t := point8 N pre
  have hc := literalRows_cellGuard t hr
  have ha : ascending14Owns t :=
    ⟨2, (mem_selectedCellIndices 2).2 (by decide), hc⟩
  have hn := cell2_not_seed7 e chi m omega N rows4 licensed4 J5 rows5 pre hlen hr
  have h15 : P4AOriginalPrior58Chronology.slot15 N
      (sixth e chi m omega N rows4 licensed4 J5 rows5) pre =
        sixth e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 6 pre) := by
    rw [slot15_source_identity e chi m omega N rows4 licensed4 J5 rows5 pre]
    simp [hn]
  have h16 : literal16Exponent N (sixth e chi m omega N rows4 licensed4 J5 rows5) pre = M t := by
    simp [literal16Exponent, familyNextExponent, ha, hp, t, point8, inheritedExponent]
  have hle := hp.2.trans hc.improvement.le
  simp only [P4AOriginalPrior58Chronology.slot16, h15, h16, max_eq_right hle]

/-- The existing chronological42 dispatcher also preserves this genuine
cell2 action against its descending15 and ascending13 alternatives. -/
theorem cell2_chronological42 (pre : List ℕ)
    (hr : literalRows (point8 N pre))
    (hp : CurrentParentGuard (point8 N pre)
      (sixth e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 6 pre))) :
    chronological42Exponent N (sixth e chi m omega N rows4 licensed4 J5 rows5) pre =
      M (point8 N pre) := by
  have ha : ascending14Owns (point8 N pre) :=
    ⟨2, (mem_selectedCellIndices 2).2 (by decide), literalRows_cellGuard _ hr⟩
  rw [chronological42_on_ascending14 N _ pre ha]
  simp [literal16Exponent, familyNextExponent, ha, hp, point8, inheritedExponent]

/-- No source-row, firstStop, supported-third or parent guard is asked of
the arithmetic caller: all are derived from its actual finite bank/state. -/
theorem actual_selected2_slot16 (he : 0 ≤ e) (Nnat cap : ℕ) (hN : 1 < Nnat)
    (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected2 e chi m omega Nnat cap w z
      (actual58Candidate e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5)) :
    firstStop (e : ℝ) m (Nnat : ℝ) (rosserAncestor 1 s.selectedPrefix) ∧
    CurrentParentGuard (point8 (Nnat : ℝ) s.selectedPrefix)
      (sixth e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5 (rosserAncestor 6 s.selectedPrefix)) ∧
    P4AOriginalPrior58Chronology.slot16 (Nnat : ℝ)
      (sixth e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5) s.selectedPrefix =
        M (point8 (Nnat : ℝ) s.selectedPrefix) := by
  have hmem : s ∈ firstExitDepthFrontier 8
      (actual58Candidate e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5)
      (fun p => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse Nnat cap w z) ∧
      ∃ j ∈ bank2 e chi m omega,
        primeHistoryTuple 8 s.selectedPrefix ∈ primeBox m Nnat j := by
    simpa only [selected2, List.mem_filter, decide_eq_true_eq] using hs
  obtain ⟨hf, j, hj, hp⟩ := hmem
  have hlen := firstExitDepthFrontier_selected_length 8 _ _ []
    (roughPrimeUniverse Nnat cap w z) true 1 (by simp) s hf
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 8 _ _ _ s hf
  have hpos : ∀ p ∈ s.selectedPrefix, 0 < p := by
    intro p hp
    exact (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))).pos
  have hNr : (1 : ℝ) < Nnat := by exact_mod_cast hN
  obtain ⟨hrows, hstop, hsupport⟩ := bank2_rows_stop_support e chi m omega (Nnat : ℝ)
    hNr s.selectedPrefix hlen hpos j hj (primeBox_log hN j _ hp)
  have hlo := P4AOriginalCell0ActualSixthParentGuard.actual_H7_lt_sixth
    e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5 Nnat cap rfl hNr w z s hf
  have hhi := actual_sixth_le_R e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5
    he s.selectedPrefix hlen hrows hsupport
  have hguard : CurrentParentGuard (point8 (Nnat : ℝ) s.selectedPrefix)
      (sixth e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5 (rosserAncestor 6 s.selectedPrefix)) :=
    ⟨by simpa only [sixth, actualSixth] using hlo,
      by simpa only [sixth, actualSixth] using hhi⟩
  exact ⟨hstop, hguard, cell2_slot16 e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5
    s.selectedPrefix hlen hrows hguard⟩

/-- Distinct literal next cells cannot overlap: mask58 takes opposite
strict old planes. The shared actual inherited value is not duplicated. -/
theorem cell2_disjoint_cell0 (t : Fin 8 → ℝ) (h1 : literalRows t)
    (h0 : P4AOriginalCell0AffineChronology.literalRows t) : False := by
  have hleft := h0 (90 : Fin 96)
  have hright := h1 (90 : Fin 96)
  have hd := (literalRows_cellGuard t h1).old_descending
  norm_num [P4AOriginalCell0AffineChronology.sourceRow,
    P4AOriginalAscendingCell0Literal96.rows, rows2, P4AOriginalAscendingCell1Affine.rows1, evalRow,
    P4AOriginalSeed7Unequal15Literal.evalAffine, Fin.sum_univ_succ] at hleft hright
  dsimp [A, C, d] at hd
  linarith


/-- The genuinely new cell2 is distinct from cell1: only mask60 changes
its strict chosen plane, so the same physical prefix cannot own both. -/
theorem cell2_disjoint_cell1 (t : Fin 8 → ℝ) (h2 : literalRows t)
    (h1 : P4AOriginalAscendingCell1Affine.literalRows t) : False := by
  have hleft := h1 (92 : Fin 96)
  have hright := h2 (92 : Fin 96)
  have hd := (literalRows_cellGuard t h2).old_descending
  norm_num [P4AOriginalAscendingCell1Affine.sourceRow,
    P4AOriginalAscendingCell1Affine.rows1, P4AOriginalAscendingCell0Literal96.rows,
    rows2, evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ] at hleft hright
  dsimp [A, C, d] at hd
  linarith


/-- Actual membership in the independently constructed cell2 bank gives
its own source rows, for any literal parent policy. -/
theorem selected2_source_rows (Nnat cap : ℕ) (hN : 1 < Nnat) (w z : ℝ)
    (parent : Bool → List ℕ → Bool) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected2 e chi m omega Nnat cap w z parent) :
    literalRows (point8 (Nnat : ℝ) s.selectedPrefix) := by
  have hbox : ∃ j ∈ bank2 e chi m omega,
      primeHistoryTuple 8 s.selectedPrefix ∈ primeBox m Nnat j :=
    of_decide_eq_true (List.mem_filter.mp hs).2
  obtain ⟨j, hj, hp⟩ := hbox
  have hrows : ∀ k : Fin 96, 0 < rowLower2 m j k := (Finset.mem_filter.mp hj).2.2.1
  have ht := primeBox_log hN j _ hp
  intro k
  have hq : (0 : ℝ) < (rowLower2 m j k : ℝ) := by exact_mod_cast hrows k
  exact hq.trans_le (rowLower2_le m j k _ ht)

/-- The next physical source bank cannot count a state already owned by
cell1, even if both banks are put over the same actual retained tree. -/
theorem selected2_not_selected1 (Nnat cap : ℕ) (hN : 1 < Nnat) (w z : ℝ)
    (parent : Bool → List ℕ → Bool) (s : FirstExitDepthState ℕ)
    (hs2 : s ∈ selected2 e chi m omega Nnat cap w z parent) :
    s ∉ P4AOriginalAscendingCell1ActualChronology.selected1
      e chi m omega Nnat cap w z parent := by
  intro hs1
  have h2 := selected2_source_rows e chi m omega Nnat cap hN w z parent s hs2
  have hbox : ∃ j ∈ P4AOriginalAscendingCell1ActualChronology.bank1 e chi m omega,
      primeHistoryTuple 8 s.selectedPrefix ∈ primeBox m Nnat j :=
    of_decide_eq_true (List.mem_filter.mp hs1).2
  obtain ⟨j, hj, hp⟩ := hbox
  have ht := primeBox_log hN j _ hp
  have hrow : ∀ k : Fin 96,
      0 < P4AOriginalAscendingCell1ActualChronology.rowLower1 m j k :=
    (Finset.mem_filter.mp hj).2.2.1
  have h1 : P4AOriginalAscendingCell1Affine.literalRows
      (point8 (Nnat : ℝ) s.selectedPrefix) := by
    intro k
    have hq : (0 : ℝ) < (P4AOriginalAscendingCell1ActualChronology.rowLower1 m j k : ℝ) := by
      exact_mod_cast hrow k
    exact hq.trans_le (P4AOriginalAscendingCell1ActualChronology.rowLower1_le m j k _ ht)
  exact cell2_disjoint_cell1 _ h2 h1

/-- Cell0 is also excluded on the genuine N-dependent arithmetic carrier,
so the three sequentially formalized source domains do not duplicate gain. -/
theorem selected2_not_selected0 (Nnat cap : ℕ) (hN : 1 < Nnat) (w z : ℝ)
    (parent : Bool → List ℕ → Bool) (s : FirstExitDepthState ℕ)
    (hs2 : s ∈ selected2 e chi m omega Nnat cap w z parent) :
    s ∉ P4AOriginalCell0HalfOpenPrimeCarrier.selectedFrontier e m Nnat cap w z parent := by
  intro hs0
  have h2 := selected2_source_rows e chi m omega Nnat cap hN w z parent s hs2
  have h0 := (P4AOriginalCell0HalfOpenPrimeCarrier.selectedFrontier_actual_source
    e m Nnat cap hN w z parent s hs0).2.2.1
  exact cell2_disjoint_cell0 _ h2 h0

end
end ImbalancedChen.P4AOriginalAscendingCell2ActualChronology
