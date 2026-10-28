import ImbalancedChen.P4AOriginalLive171819CommonParent

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Finite original-source banks for the forty-three actual LIVE source IDs. Each bank
uses its own actual rows before N; actual retained prime states supply the
complete guard, firstStop, original rough/third licence and NEW common cap.
-/
namespace ImbalancedChen.P4AOriginalLive171819PrimeBank
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope HistoricalThirdCoarse
open P4AOriginalLive171819Atlas P4AOriginalLive171819CommonParent
open P4AOriginalCell0HalfOpenPrimeCarrier
variable (c : LiveCell)
variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)

/-- The rational infimum of each original actual atlas row over one closed box. -/
def rowLower (m : ℕ) (j : BoxIndex m) (k : Fin (rowCount c)) : ℚ :=
  (rows c k) 0 + ∑ i : Fin 8,
    (rows c k) i.succ * (if 0 ≤ (rows c k) i.succ then qLo m j i else qHi m j i)

/-- All tests are finite geometric/actual third licences before N. -/
def bank (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) : Finset (BoxIndex m) :=
  Finset.univ.filter fun j =>
    qHi m j 0 ≤ 19 / 96 - 4 * e ∧
    (∀ k : Fin (rowCount c), 0 < rowLower c m j k) ∧
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
theorem rowLower_le (m : ℕ) (j : BoxIndex m) (k : Fin (rowCount c)) (t : Fin 8 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    (rowLower c m j k : ℝ) ≤ eval (rows c k) t := by
  unfold rowLower eval P4AOriginalSeed7Unequal15Literal.evalAffine
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
def selected (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (Nnat cap : ℕ)
    (w z : ℝ) (parent : Bool → List ℕ → Bool) : List (FirstExitDepthState ℕ) :=
  (firstExitDepthFrontier 8 parent (fun p => 1 / ((p : ℝ) - 1)) [] true 1
    (roughPrimeUniverse Nnat cap w z)).filter fun s => decide
      (∃ j ∈ bank c e chi m omega,
        primeHistoryTuple 8 s.selectedPrefix ∈ primeBox m Nnat j)

/-- Both firstStop and actual third support follow from the same finite
box label; neither is a subsequent invented parent-cap hypothesis. -/
theorem bank_rows_stop_support (hN : 1 < N) (pre : List ℕ) (hlen : pre.length = 8)
    (hpos : ∀ p ∈ pre, 0 < p) (j : BoxIndex m)
    (hj : j ∈ bank c e chi m omega)
    (ht : point8 N pre ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    sourceRows c (point8 N pre) ∧
    firstStop (e : ℝ) m N (rosserAncestor 1 pre) ∧
    P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N (rosserAncestor 3 pre) := by
  have hb : qHi m j 0 ≤ 19 / 96 - 4 * e ∧
      (∀ k : Fin (rowCount c), 0 < rowLower c m j k) ∧
      historicalPrefixProject (by decide : 3 ≤ 8) j ∈ cells (e : ℝ) chi m ∧
      omega ≤ logPrimeMeshLo 0 (19 / 96) m j 2 := (Finset.mem_filter.mp hj).2
  have hr : sourceRows c (point8 N pre) := by
    intro k
    have hq : (0 : ℝ) < (rowLower c m j k : ℝ) := by exact_mod_cast hb.2.1 k
    exact hq.trans_le (rowLower_le c m j k _ ht)
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

/-- A real retained state of the common physical policy supplies its own
new sixth ancestor guard. No equality with the old actual58 tree is used. -/
theorem shared_frontier_live_guard
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected c d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))) :
    sourceRows c (point8 (N : ℝ) s.selectedPrefix) ∧
    HistoricalThirdCoarse.firstStop (d.e : ℝ) d.m (N : ℝ) (rosserAncestor 1 s.selectedPrefix) ∧
    (P2OriginalDescendingEighthLogSemantics.history7 (point8 (N : ℝ) s.selectedPrefix) <
      P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix)) ∧
    (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) ≤
      oldCap c (point8 (N : ℝ) s.selectedPrefix)) := by
  have hm : s ∈ firstExitDepthFrontier 8
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))
      (fun p => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z) ∧
      ∃ j ∈ bank c d.e d.chi d.m d.omega,
        primeHistoryTuple 8 s.selectedPrefix ∈ primeBox d.m N j := by
    simpa only [selected, List.mem_filter, decide_eq_true_eq] using hs
  obtain ⟨hf, j, hj, hp⟩ := hm
  have hf6 := hf
  rw [P5OriginalCommonRefinedAncestry.policy8_frontier_eight_eq_six] at hf6
  have hlen := firstExitDepthFrontier_selected_length 8 _ _ []
    (roughPrimeUniverse N cap w z) true 1 (by simp) s hf
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 8 _ _ _ s hf
  have hpos : ∀ p ∈ s.selectedPrefix, 0 < p := by
    intro p hp
    exact (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))).pos
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hrows, hstop, hsupport⟩ := bank_rows_stop_support c d.e d.chi d.m d.omega (N : ℝ)
    hNr s.selectedPrefix hlen hpos j hj (primeBox_log hN j _ hp)
  have hup := common_sixth_le_old c d (N : ℝ) he s.selectedPrefix hlen hrows hsupport
  have hlo := P4AActualEighthInheritedHistoryGuard.actual_log_history7_lt_current
    (P5OriginalCommonRefinedConstructor.policy5 d (N : ℝ))
    (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ))
    N cap hNr w z (fun p => 1 / ((p : ℝ) - 1)) s hf6
  exact ⟨hrows,hstop,hlo,hup⟩


end
end ImbalancedChen.P4AOriginalLive171819PrimeBank
