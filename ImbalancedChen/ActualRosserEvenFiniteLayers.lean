import ImbalancedChen.ActualRosserEvenBoxUnion
import ImbalancedChen.RosserEvenMeshIntegral

/-!
# Actual lower Rosser density below finite even-layer losses

The prime boxes from all selected ranks enter one negative boundary expansion.
Its constant term is counted once. A common mesh is then chosen from the
proved finite sum of mesh limits, before the target and enumeration cap.
The finite rank set can be empty. No single-layer inequalities are added.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Filter Topology

/-- A common fixed mesh at finitely many ranks contributes all its lower
sums to one actual raw density, with just one constant term. -/
theorem exists_actualSmallRosserMinusDensity_evenMeshes_upper_threshold
    (K : Finset ℕ) (s : ℝ) (hs : 1 < s)
    (hcut : ∀ k ∈ K, (s - 1) / 3 ^ (k + 1) < 1)
    (u : ℝ) (hu : 0 < u) (n : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
          actualSmallEulerProduct N cap ((N : ℝ) ^ u) ≤
            1 - (∑ k ∈ K, rosserEvenMeshLowerSum k s n) + eta := by
  have hspos : 0 < s := zero_lt_one.trans hs
  let J := fun k => rosserEvenMeshCells k s n
  let a := fun (k : ℕ) (j : Fin (2 * k + 2) → Fin (n + 1)) =>
    fun i => u * rosserEvenMeshLo k s n j i
  let b := fun (k : ℕ) (j : Fin (2 * k + 2) → Fin (n + 1)) =>
    fun i => u * rosserEvenMeshHi k s n j i
  have ha (k : ℕ) (hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (_hj : j ∈ J k)
      (i : Fin (2 * k + 2)) : 0 < a k j i := by
    have hpos : (0 : ℝ) < (s - 1) / 3 ^ (k + 1) := by positivity
    exact mul_pos hu (hpos.trans_le (rosserEvenMeshLoHi_bounds (hcut k hk) n j i).1)
  have hab (k : ℕ) (hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (_hj : j ∈ J k)
      (i : Fin (2 * k + 2)) : a k j i < b k j i :=
    mul_lt_mul_of_pos_left (rosserEvenMeshLoHi_bounds (hcut k hk) n j i).2.1 hu
  have hsep (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (hj : j ∈ J k)
      (i : Fin (2 * k + 1)) : b k j i.succ ≤ a k j i.castSucc :=
    mul_le_mul_of_nonneg_left ((mem_rosserEvenMeshCells.mp hj).1 i) hu.le
  have hbu (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (hj : j ∈ J k) : b k j 0 ≤ u := by
    simpa [b] using mul_le_mul_of_nonneg_left (mem_rosserEvenMeshCells.mp hj).2.1 hu.le
  have hprod (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (hj : j ∈ J k) :
      (∑ i : Fin (2 * k + 1), b k j i.castSucc) ≤ s * u := by
    have h := mul_le_mul_of_nonneg_left (mem_rosserEvenMeshCells.mp hj).2.2.1.le hu.le
    simpa [b, Finset.mul_sum, mul_comm] using h
  have hprefix (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (hj : j ∈ J k)
      (i : Fin (2 * k + 1)) (hi : Odd i.val) :
      (∑ t : Fin (2 * k + 1) with t.val < i.val, b k j t.castSucc) +
        3 * b k j i.castSucc ≤ s * u := by
    have h := mul_le_mul_of_nonneg_left
      ((mem_rosserEvenMeshCells.mp hj).2.2.2.1 i hi).le hu.le
    dsimp [b]
    rw [← Finset.mul_sum]
    dsimp [rosserEvenLogPrefix] at h
    nlinarith
  have hshell (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (hj : j ∈ J k) :
      s * u ≤ (∑ i : Fin (2 * k + 1), a k j i.castSucc) +
        3 * a k j (Fin.last (2 * k + 1)) := by
    have h := mul_le_mul_of_nonneg_left (mem_rosserEvenMeshCells.mp hj).2.2.2.2.le hu.le
    dsimp [a]
    rw [← Finset.mul_sum]
    nlinarith
  have hdisj (k : ℕ) (hk : k ∈ K)
      (j : Fin (2 * k + 2) → Fin (n + 1)) (_hj : j ∈ J k)
      (r : Fin (2 * k + 2) → Fin (n + 1)) (_hr : r ∈ J k) (hjr : j ≠ r) :
      ∃ i, b k j i ≤ a k r i ∨ b k r i ≤ a k j i := by
    obtain ⟨i, hi | hi⟩ := rosserEvenMesh_separated (hcut k hk).le hjr
    · exact ⟨i, Or.inl (mul_le_mul_of_nonneg_left hi hu.le)⟩
    · exact ⟨i, Or.inr (mul_le_mul_of_nonneg_left hi hu.le)⟩
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserMinusDensity_evenBoxUnion_upper_threshold K J a b u (s * u)
      hu (mul_pos hspos hu) (by nlinarith) ha hab hsep hbu hprod hprefix hshell hdisj eta heta
  have heq (k : ℕ) (j : Fin (2 * k + 2) → Fin (n + 1)) :
      (u / b k j (Fin.last (2 * k + 1))) * (∏ i, Real.log (b k j i / a k j i)) =
        (1 / rosserEvenMeshHi k s n j (Fin.last (2 * k + 1))) *
          (∏ i, Real.log (rosserEvenMeshHi k s n j i / rosserEvenMeshLo k s n j i)) := by
    have hratio (i : Fin (2 * k + 2)) : b k j i / a k j i =
        rosserEvenMeshHi k s n j i / rosserEvenMeshLo k s n j i := by
      dsimp [a, b]
      exact mul_div_mul_left _ _ hu.ne'
    simp_rw [hratio]
    congr 1
    dsimp [b]
    rw [div_mul_eq_div_div, div_self hu.ne']
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  simpa only [heq, J, rosserEvenMeshLowerSum] using hbound N hN hEven cap hcap

/-- Every finite collection of even region integrals contributes to the same
raw coefficient density. The common mesh and threshold precede both the
later target and every complete enumeration cap. -/
theorem exists_actualSmallRosserMinusDensity_evenFiniteLayers_upper_threshold_of_cutoff
    (K : Finset ℕ) (s : ℝ) (hs : 1 < s)
    (hcut : ∀ k ∈ K, (s - 1) / 3 ^ (k + 1) < 1)
    (u : ℝ) (hu : 0 < u) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
          actualSmallEulerProduct N cap ((N : ℝ) ^ u) ≤
            1 - (∑ k ∈ K, rosserEvenLayerIntegral k s) + eta := by
  have hlim : Tendsto (fun n => ∑ k ∈ K, rosserEvenMeshLowerSum k s n) atTop
      (nhds (∑ k ∈ K, rosserEvenLayerIntegral k s)) :=
    tendsto_finsetSum K (fun k hk =>
      tendsto_rosserEvenMeshLowerSum hs (hcut k hk))
  have hnear := hlim.eventually
    (lt_mem_nhds (show (∑ k ∈ K, rosserEvenLayerIntegral k s) - eta / 2 <
        ∑ k ∈ K, rosserEvenLayerIntegral k s by linarith))
  obtain ⟨n, hn⟩ := hnear.exists
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserMinusDensity_evenMeshes_upper_threshold K s hs hcut u hu n
      (eta / 2) (by linarith)
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  have h := hbound N hN hEven cap hcap
  linarith

/-- If the positive support box has collapsed, the actual region is empty.
This removes the mesh nondegeneracy restriction from finite-layer bounds. -/
theorem rosserEvenLayerIntegral_eq_zero_of_cutoff_ge_one
    (k : ℕ) (s : ℝ) (hs : 1 < s) (hcut : 1 ≤ (s - 1) / 3 ^ (k + 1)) :
    rosserEvenLayerIntegral k s = 0 := by
  have hempty : rosserEvenLogRegion k s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hb := rosserEvenLogRegion_bounds hs hx 0
    linarith
  simp only [rosserEvenLayerIntegral, hempty, MeasureTheory.setIntegral_empty]

/-- Any finite collection of genuine even layers can be selected, including
empty regions and rank zero. All ranks share one mesh and one threshold. -/
theorem exists_actualSmallRosserMinusDensity_evenFiniteLayers_upper_threshold
    (K : Finset ℕ) (s : ℝ) (hs : 1 < s)
    (u : ℝ) (hu : 0 < u) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
          actualSmallEulerProduct N cap ((N : ℝ) ^ u) ≤
            1 - (∑ k ∈ K, rosserEvenLayerIntegral k s) + eta := by
  let K' := K.filter (fun k => (s - 1) / 3 ^ (k + 1) < 1)
  have hcut (k : ℕ) (hk : k ∈ K') : (s - 1) / 3 ^ (k + 1) < 1 :=
    (Finset.mem_filter.mp hk).2
  have hsum : (∑ k ∈ K', rosserEvenLayerIntegral k s) =
      ∑ k ∈ K, rosserEvenLayerIntegral k s := by
    dsimp [K']
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _hk
    split_ifs with hk
    · rfl
    · exact (rosserEvenLayerIntegral_eq_zero_of_cutoff_ge_one k s hs
        (le_of_not_gt hk)).symm
  simpa only [hsum] using
    exists_actualSmallRosserMinusDensity_evenFiniteLayers_upper_threshold_of_cutoff
      K' s hs hcut u hu eta heta

end

end ImbalancedChen
