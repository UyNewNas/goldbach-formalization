import ImbalancedChen.ActualRosserOddBoxUnion
import ImbalancedChen.RosserOddMeshIntegral

/-!
# Actual upper Rosser density above finite sums of continuous odd layers

The prime boxes from all selected ranks enter one positive boundary expansion.
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
theorem exists_actualSmallRosserPlusDensity_oddMeshes_lower_threshold
    (K : Finset ℕ) (s : ℝ) (hs : 1 ≤ s)
    (hcut : ∀ k ∈ K, s / 3 ^ (k + 1) < 1)
    (u : ℝ) (hu : 0 < u) (n : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        1 + (∑ k ∈ K, rosserOddMeshLowerSum k s n) - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  have hspos : 0 < s := zero_lt_one.trans_le hs
  let J := fun k => rosserOddMeshCells k s n
  let a := fun (k : ℕ) (j : Fin (2 * k + 1) → Fin (n + 1)) =>
    fun i => u * rosserOddMeshLo k s n j i
  let b := fun (k : ℕ) (j : Fin (2 * k + 1) → Fin (n + 1)) =>
    fun i => u * rosserOddMeshHi k s n j i
  have ha (k : ℕ) (hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (_hj : j ∈ J k)
      (i : Fin (2 * k + 1)) : 0 < a k j i := by
    have hpos : (0 : ℝ) < s / 3 ^ (k + 1) := by positivity
    exact mul_pos hu (hpos.trans_le (rosserOddMeshLoHi_bounds (hcut k hk) n j i).1)
  have hab (k : ℕ) (hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (_hj : j ∈ J k)
      (i : Fin (2 * k + 1)) : a k j i < b k j i :=
    mul_lt_mul_of_pos_left (rosserOddMeshLoHi_bounds (hcut k hk) n j i).2.1 hu
  have hsep (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (hj : j ∈ J k)
      (i : Fin (2 * k)) : b k j i.succ ≤ a k j i.castSucc :=
    mul_le_mul_of_nonneg_left ((mem_rosserOddMeshCells.mp hj).1 i) hu.le
  have hbu (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (hj : j ∈ J k) : b k j 0 ≤ u := by
    simpa [b] using mul_le_mul_of_nonneg_left (mem_rosserOddMeshCells.mp hj).2.1 hu.le
  have hprod (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (hj : j ∈ J k) :
      (∑ i : Fin (2 * k), b k j i.castSucc) ≤ s * u := by
    have h := mul_le_mul_of_nonneg_left (mem_rosserOddMeshCells.mp hj).2.2.1.le hu.le
    simpa [b, Finset.mul_sum, mul_comm] using h
  have hprefix (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (hj : j ∈ J k)
      (i : Fin (2 * k)) (hi : Even i.val) :
      (∑ t : Fin (2 * k) with t.val < i.val, b k j t.castSucc) +
        3 * b k j i.castSucc ≤ s * u := by
    have h := mul_le_mul_of_nonneg_left
      ((mem_rosserOddMeshCells.mp hj).2.2.2.1 i hi).le hu.le
    dsimp [b]
    rw [← Finset.mul_sum]
    dsimp [rosserOddLogPrefix] at h
    nlinarith
  have hshell (k : ℕ) (_hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (hj : j ∈ J k) :
      s * u ≤ (∑ i : Fin (2 * k), a k j i.castSucc) +
        3 * a k j (Fin.last (2 * k)) := by
    have h := mul_le_mul_of_nonneg_left (mem_rosserOddMeshCells.mp hj).2.2.2.2.le hu.le
    dsimp [a]
    rw [← Finset.mul_sum]
    nlinarith
  have hdisj (k : ℕ) (hk : k ∈ K)
      (j : Fin (2 * k + 1) → Fin (n + 1)) (_hj : j ∈ J k)
      (r : Fin (2 * k + 1) → Fin (n + 1)) (_hr : r ∈ J k) (hjr : j ≠ r) :
      ∃ i, b k j i ≤ a k r i ∨ b k r i ≤ a k j i := by
    obtain ⟨i, hi | hi⟩ := rosserOddMesh_separated (hcut k hk).le hjr
    · exact ⟨i, Or.inl (mul_le_mul_of_nonneg_left hi hu.le)⟩
    · exact ⟨i, Or.inr (mul_le_mul_of_nonneg_left hi hu.le)⟩
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_oddBoxUnion_lower_threshold K J a b u (s * u)
      hu (mul_pos hspos hu) (by nlinarith) ha hab hsep hbu hprod hprefix hshell hdisj eta heta
  have heq (k : ℕ) (j : Fin (2 * k + 1) → Fin (n + 1)) :
      (u / b k j (Fin.last (2 * k))) * (∏ i, Real.log (b k j i / a k j i)) =
        (1 / rosserOddMeshHi k s n j (Fin.last (2 * k))) *
          (∏ i, Real.log (rosserOddMeshHi k s n j i / rosserOddMeshLo k s n j i)) := by
    have hratio (i : Fin (2 * k + 1)) : b k j i / a k j i =
        rosserOddMeshHi k s n j i / rosserOddMeshLo k s n j i := by
      dsimp [a, b]
      exact mul_div_mul_left _ _ hu.ne'
    simp_rw [hratio]
    congr 1
    dsimp [b]
    rw [div_mul_eq_div_div, div_self hu.ne']
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  simpa only [heq, J, rosserOddMeshLowerSum] using hbound N hN hEven cap hcap

/-- Every finite collection of odd region integrals contributes to the same
raw coefficient density. The common mesh and threshold precede both the
later target and every complete enumeration cap. -/
theorem exists_actualSmallRosserPlusDensity_oddFiniteLayers_lower_threshold
    (K : Finset ℕ) (s : ℝ) (hs : 1 ≤ s)
    (hcut : ∀ k ∈ K, s / 3 ^ (k + 1) < 1)
    (u : ℝ) (hu : 0 < u) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        1 + (∑ k ∈ K, rosserOddLayerIntegral k s) - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  have hlim : Tendsto (fun n => ∑ k ∈ K, rosserOddMeshLowerSum k s n) atTop
      (nhds (∑ k ∈ K, rosserOddLayerIntegral k s)) :=
    tendsto_finsetSum K (fun k hk =>
      tendsto_rosserOddMeshLowerSum (zero_lt_one.trans_le hs) (hcut k hk))
  have hnear := hlim.eventually
    (lt_mem_nhds (show (∑ k ∈ K, rosserOddLayerIntegral k s) - eta / 2 <
        ∑ k ∈ K, rosserOddLayerIntegral k s by linarith))
  obtain ⟨n, hn⟩ := hnear.exists
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_oddMeshes_lower_threshold K s hs hcut u hu n
      (eta / 2) (by linarith)
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  have h := hbound N hN hEven cap hcap
  linarith

/-- At residual three every finite collection of positive pair depths has
a common lower threshold, for any fixed positive outer exponent. -/
theorem exists_actualSmallRosserPlusDensity_oddFiniteLayers_at_three_lower_threshold
    (K : Finset ℕ) (hK : ∀ k ∈ K, 1 ≤ k)
    (u : ℝ) (hu : 0 < u) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        1 + (∑ k ∈ K, rosserOddLayerIntegral k 3) - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (3 * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  have hcut (k : ℕ) (hk : k ∈ K) : (3 : ℝ) / 3 ^ (k + 1) < 1 := by
    have hpow : (3 : ℝ) ^ 2 ≤ 3 ^ (k + 1) :=
      pow_le_pow_right₀ (by norm_num) (by have := hK k hk; omega)
    apply (div_lt_one (by positivity)).mpr
    norm_num at hpow
    linarith
  exact exists_actualSmallRosserPlusDensity_oddFiniteLayers_lower_threshold K 3 (by norm_num)
    hcut u hu eta heta

/-- Original `R=N` specialization: an arbitrary finite set of positive odd
boundary layers, with a single constant term one. -/
theorem exists_actualSmallRosserPlusDensity_oneThird_oddFiniteLayers_lower_threshold
    (K : Finset ℕ) (hK : ∀ k ∈ K, 1 ≤ k) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ (1 / 3 : ℝ) ≤ (cap : ℝ) →
        1 + (∑ k ∈ K, rosserOddLayerIntegral k 3) - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ (1 / 3 : ℝ)) (N : ℝ) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  simpa only [show (3 * (1 / 3 : ℝ)) = 1 by norm_num, Real.rpow_one] using
    exists_actualSmallRosserPlusDensity_oddFiniteLayers_at_three_lower_threshold K hK
      (1 / 3) (by norm_num) eta heta

end

end ImbalancedChen
