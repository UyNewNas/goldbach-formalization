import ImbalancedChen.ActualRosserOddBoxFamily
import ImbalancedChen.RosserOddMeshIntegral

/-!
# Actual upper Rosser density above every fixed continuous odd layer

For a fixed odd rank and positive outer exponent, a normalized strict mesh
is scaled to genuine prime-exponent boxes. Its finite-family lower bound
uses the same raw coefficient at `ceil (N ^ (s*u))`. The proved mesh limit
then selects one mesh before the target threshold. Neither the analytic
limit nor the target-prime exclusion is assumed as an input.

These are individual fixed-layer contributions. Combining different layers
requires their boundary tails to be disjoint by cardinality before summing;
the constant term one must not be summed separately for each layer.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Filter Topology

/-- Every fixed inner mesh in a fixed odd layer contributes its full lower
sum to the actual raw density, uniformly in complete enumeration caps. -/
theorem exists_actualSmallRosserPlusDensity_oddMesh_lower_threshold
    (k : ℕ) (s : ℝ) (hs : 1 ≤ s) (hcut : s / 3 ^ (k + 1) < 1)
    (u : ℝ) (hu : 0 < u) (n : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        1 + rosserOddMeshLowerSum k s n - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  have hspos : 0 < s := zero_lt_one.trans_le hs
  let a := fun j : Fin (2 * k + 1) → Fin (n + 1) =>
    fun i => u * rosserOddMeshLo k s n j i
  let b := fun j : Fin (2 * k + 1) → Fin (n + 1) =>
    fun i => u * rosserOddMeshHi k s n j i
  have ha (j : Fin (2 * k + 1) → Fin (n + 1))
      (_hj : j ∈ rosserOddMeshCells k s n) (i : Fin (2 * k + 1)) : 0 < a j i := by
    have hpos : (0 : ℝ) < s / 3 ^ (k + 1) := by positivity
    exact mul_pos hu (hpos.trans_le (rosserOddMeshLoHi_bounds hcut n j i).1)
  have hab (j : Fin (2 * k + 1) → Fin (n + 1))
      (_hj : j ∈ rosserOddMeshCells k s n) (i : Fin (2 * k + 1)) : a j i < b j i :=
    mul_lt_mul_of_pos_left (rosserOddMeshLoHi_bounds hcut n j i).2.1 hu
  have hsep (j : Fin (2 * k + 1) → Fin (n + 1))
      (hj : j ∈ rosserOddMeshCells k s n) (i : Fin (2 * k)) :
      b j i.succ ≤ a j i.castSucc :=
    mul_le_mul_of_nonneg_left ((mem_rosserOddMeshCells.mp hj).1 i) hu.le
  have hbu (j : Fin (2 * k + 1) → Fin (n + 1))
      (hj : j ∈ rosserOddMeshCells k s n) : b j 0 ≤ u := by
    simpa [b] using mul_le_mul_of_nonneg_left (mem_rosserOddMeshCells.mp hj).2.1 hu.le
  have hprod (j : Fin (2 * k + 1) → Fin (n + 1))
      (hj : j ∈ rosserOddMeshCells k s n) :
      (∑ i : Fin (2 * k), b j i.castSucc) ≤ s * u := by
    have h := mul_le_mul_of_nonneg_left (mem_rosserOddMeshCells.mp hj).2.2.1.le hu.le
    simpa [b, Finset.mul_sum, mul_comm] using h
  have hprefix (j : Fin (2 * k + 1) → Fin (n + 1))
      (hj : j ∈ rosserOddMeshCells k s n) (i : Fin (2 * k)) (hi : Even i.val) :
      (∑ t : Fin (2 * k) with t.val < i.val, b j t.castSucc) +
        3 * b j i.castSucc ≤ s * u := by
    have h := mul_le_mul_of_nonneg_left
      ((mem_rosserOddMeshCells.mp hj).2.2.2.1 i hi).le hu.le
    dsimp [b]
    rw [← Finset.mul_sum]
    dsimp [rosserOddLogPrefix] at h
    nlinarith
  have hshell (j : Fin (2 * k + 1) → Fin (n + 1))
      (hj : j ∈ rosserOddMeshCells k s n) :
      s * u ≤ (∑ i : Fin (2 * k), a j i.castSucc) +
        3 * a j (Fin.last (2 * k)) := by
    have h := mul_le_mul_of_nonneg_left (mem_rosserOddMeshCells.mp hj).2.2.2.2.le hu.le
    dsimp [a]
    rw [← Finset.mul_sum]
    nlinarith
  have hdisj (j : Fin (2 * k + 1) → Fin (n + 1))
      (_hj : j ∈ rosserOddMeshCells k s n)
      (r : Fin (2 * k + 1) → Fin (n + 1))
      (_hr : r ∈ rosserOddMeshCells k s n) (hjr : j ≠ r) :
      ∃ i, b j i ≤ a r i ∨ b r i ≤ a j i := by
    obtain ⟨i, hi | hi⟩ := rosserOddMesh_separated hcut.le hjr
    · exact ⟨i, Or.inl (mul_le_mul_of_nonneg_left hi hu.le)⟩
    · exact ⟨i, Or.inr (mul_le_mul_of_nonneg_left hi hu.le)⟩
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_oddBoxFamily_lower_threshold k
      (rosserOddMeshCells k s n) a b u (s * u) hu (mul_pos hspos hu)
      (by nlinarith) ha hab hsep hbu hprod hprefix hshell hdisj eta heta
  have heq (j : Fin (2 * k + 1) → Fin (n + 1)) :
      (u / b j (Fin.last (2 * k))) * (∏ i, Real.log (b j i / a j i)) =
        (1 / rosserOddMeshHi k s n j (Fin.last (2 * k))) *
          (∏ i, Real.log (rosserOddMeshHi k s n j i / rosserOddMeshLo k s n j i)) := by
    have hratio (i : Fin (2 * k + 1)) : b j i / a j i =
        rosserOddMeshHi k s n j i / rosserOddMeshLo k s n j i := by
      dsimp [a, b]
      exact mul_div_mul_left _ _ hu.ne'
    simp_rw [hratio]
    congr 1
    dsimp [b]
    rw [div_mul_eq_div_div, div_self hu.ne']
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  simpa only [heq, rosserOddMeshLowerSum] using hbound N hN hEven cap hcap

/-- Every fixed odd layer's actual Lebesgue integral is a proved lower
contribution. The mesh is chosen first, then one threshold valid for all
later even targets and covering caps. No layer-uniform threshold is claimed. -/
theorem exists_actualSmallRosserPlusDensity_oddLayer_lower_threshold
    (k : ℕ) (s : ℝ) (hs : 1 ≤ s) (hcut : s / 3 ^ (k + 1) < 1)
    (u : ℝ) (hu : 0 < u) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        1 + rosserOddLayerIntegral k s - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  have hnear := (tendsto_rosserOddMeshLowerSum (zero_lt_one.trans_le hs) hcut).eventually
    (lt_mem_nhds (show rosserOddLayerIntegral k s - eta / 2 < rosserOddLayerIntegral k s by
      linarith))
  obtain ⟨n, hn⟩ := hnear.exists
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_oddMesh_lower_threshold k s hs hcut u hu n
      (eta / 2) (by linarith)
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  have h := hbound N hN hEven cap hcap
  linarith

/-- Every positive pair depth at residual coordinate three has a genuine
fixed-layer lower bound for an arbitrary fixed positive outer exponent. -/
theorem exists_actualSmallRosserPlusDensity_oddLayer_at_three_lower_threshold
    (k : ℕ) (hk : 1 ≤ k) (u : ℝ) (hu : 0 < u) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        1 + rosserOddLayerIntegral k 3 - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (3 * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  have hpow : (3 : ℝ) ^ 2 ≤ 3 ^ (k + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hcut : (3 : ℝ) / 3 ^ (k + 1) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    norm_num at hpow
    linarith
  exact exists_actualSmallRosserPlusDensity_oddLayer_lower_threshold k 3 (by norm_num)
    hcut u hu eta heta

/-- Original `R=N` specialization at the strict cube cutoff, for every
fixed positive pair depth. -/
theorem exists_actualSmallRosserPlusDensity_oneThird_oddLayer_lower_threshold
    (k : ℕ) (hk : 1 ≤ k) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ (1 / 3 : ℝ) ≤ (cap : ℝ) →
        1 + rosserOddLayerIntegral k 3 - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ (1 / 3 : ℝ)) (N : ℝ) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  simpa only [show (3 * (1 / 3 : ℝ)) = 1 by norm_num, Real.rpow_one] using
    exists_actualSmallRosserPlusDensity_oddLayer_at_three_lower_threshold k hk
      (1 / 3) (by norm_num) eta heta

end

end ImbalancedChen
