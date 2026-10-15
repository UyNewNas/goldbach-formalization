import ImbalancedChen.ActualExtendedThirdPhysicalCell
import Mathlib.Data.Finset.Max

/-!
# Deterministic least winning branch for the actual robust full cap

Index zero is the baseline. Failed pair entries equal that baseline, so the
least winning index cannot select them. The unsupported singleton p2 entry
is likewise excluded from the actual full ordered domain, using its true
whole-cell domination by the baseline. Each actual cell infimum is compared
with point values by the compact continuous-image supplier, not assumed to
license an action merely because Gamma has a numerical surplus.

This is the deterministic index and endpoint license. Choosing an intermediate
factorization parameter, the rescued-W action, perturbing the residue exponent,
and the same-policy arithmetic mean remain subsequent obligations.
-/

namespace ImbalancedChen

noncomputable section

open Set
open VariableEnvelope
open scoped Classical

def actualExtendedThirdRobustCandidate (e : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) (k : Fin 8) : ℝ :=
  let b := fun i => actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch i)
  ![b 0, b 1, b 2, b 3, b 4, b 5,
    if e ≤ actualExtendedThirdCellInf m j actualExtendedThirdGateXZ then
      actualExtendedThirdCellInf m j actualExtendedThirdPairXZ else b 0,
    if e ≤ actualExtendedThirdCellInf m j actualExtendedThirdGateYZ then
      actualExtendedThirdCellInf m j actualExtendedThirdPairYZ else b 0] k

theorem actualExtendedThirdRobustCandidate_le_fullGamma (e : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) (k : Fin 8) :
    actualExtendedThirdRobustCandidate e m j k ≤ actualExtendedThirdFullGamma e m j := by
  fin_cases k <;> simp [actualExtendedThirdRobustCandidate, actualExtendedThirdFullGamma, le_max_iff]

private theorem fullGamma_le_maximal_candidate {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {k : Fin 8}
    (hk : ∀ l : Fin 8, actualExtendedThirdRobustCandidate e m j l ≤
      actualExtendedThirdRobustCandidate e m j k) :
    actualExtendedThirdFullGamma e m j ≤ actualExtendedThirdRobustCandidate e m j k := by
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  have h3 := hk 3
  have h4 := hk 4
  have h5 := hk 5
  have h6 := hk 6
  have h7 := hk 7
  change actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 0) ≤ _ at h0
  change actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 1) ≤ _ at h1
  change actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 2) ≤ _ at h2
  change actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 3) ≤ _ at h3
  change actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 4) ≤ _ at h4
  change actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 5) ≤ _ at h5
  unfold actualExtendedThirdFullGamma
  exact max_le h0 (max_le h1 (max_le h2 (max_le h3
    (max_le h4 (max_le h5 (max_le h6 h7))))))

def actualExtendedThirdWinningIndices (e : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) : Finset (Fin 8) :=
  Finset.univ.filter (fun k => ∀ l : Fin 8, actualExtendedThirdRobustCandidate e m j l ≤
    actualExtendedThirdRobustCandidate e m j k)

theorem mem_actualExtendedThirdWinningIndices {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {k : Fin 8} :
    k ∈ actualExtendedThirdWinningIndices e m j ↔
      ∀ l : Fin 8, actualExtendedThirdRobustCandidate e m j l ≤
        actualExtendedThirdRobustCandidate e m j k := by
  simp only [actualExtendedThirdWinningIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem actualExtendedThirdWinningIndices_nonempty (e : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) : (actualExtendedThirdWinningIndices e m j).Nonempty := by
  obtain ⟨k, _hk, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 8))
    (actualExtendedThirdRobustCandidate e m j) (by simp)
  exact ⟨k, mem_actualExtendedThirdWinningIndices.mpr (fun l => hmax l (Finset.mem_univ _))⟩

def actualExtendedThirdLeastWinningIndex (e : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) : Fin 8 :=
  (actualExtendedThirdWinningIndices e m j).min' (actualExtendedThirdWinningIndices_nonempty e m j)

theorem actualExtendedThirdLeastWinningIndex_mem (e : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) :
    actualExtendedThirdLeastWinningIndex e m j ∈ actualExtendedThirdWinningIndices e m j :=
  Finset.min'_mem _ _

theorem actualExtendedThirdLeastWinningIndex_le {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {k : Fin 8}
    (hk : k ∈ actualExtendedThirdWinningIndices e m j) :
    actualExtendedThirdLeastWinningIndex e m j ≤ k :=
  Finset.min'_le _ _ hk

theorem actualExtendedThirdFullGamma_eq_leastWinningValue (e : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) :
    actualExtendedThirdFullGamma e m j =
      actualExtendedThirdRobustCandidate e m j (actualExtendedThirdLeastWinningIndex e m j) := by
  exact le_antisymm (fullGamma_le_maximal_candidate
    (mem_actualExtendedThirdWinningIndices.mp (actualExtendedThirdLeastWinningIndex_mem e m j)))
    (actualExtendedThirdRobustCandidate_le_fullGamma _ _ _ _)

private theorem leastIndex_eq_zero_of_baseline_dominates_winner {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (hb : actualExtendedThirdRobustCandidate e m j (actualExtendedThirdLeastWinningIndex e m j) ≤
      actualExtendedThirdRobustCandidate e m j 0) :
    actualExtendedThirdLeastWinningIndex e m j = 0 := by
  have hmax := mem_actualExtendedThirdWinningIndices.mp (actualExtendedThirdLeastWinningIndex_mem e m j)
  have hzero : (0 : Fin 8) ∈ actualExtendedThirdWinningIndices e m j :=
    mem_actualExtendedThirdWinningIndices.mpr (fun l => (hmax l).trans hb)
  exact le_antisymm (actualExtendedThirdLeastWinningIndex_le hzero) (Fin.zero_le _)

theorem actualExtendedThirdLeastWinningIndex_pairXZ_gate {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (hk : actualExtendedThirdLeastWinningIndex e m j = 6) :
    e ≤ actualExtendedThirdCellInf m j actualExtendedThirdGateXZ := by
  by_contra hgate
  have hb : actualExtendedThirdRobustCandidate e m j (actualExtendedThirdLeastWinningIndex e m j) ≤
      actualExtendedThirdRobustCandidate e m j 0 := by
    rw [hk]
    simp [actualExtendedThirdRobustCandidate, hgate]
  have hz := leastIndex_eq_zero_of_baseline_dominates_winner hb
  omega

theorem actualExtendedThirdLeastWinningIndex_pairYZ_gate {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (hk : actualExtendedThirdLeastWinningIndex e m j = 7) :
    e ≤ actualExtendedThirdCellInf m j actualExtendedThirdGateYZ := by
  by_contra hgate
  have hb : actualExtendedThirdRobustCandidate e m j (actualExtendedThirdLeastWinningIndex e m j) ≤
      actualExtendedThirdRobustCandidate e m j 0 := by
    rw [hk]
    simp [actualExtendedThirdRobustCandidate, hgate]
  have hz := leastIndex_eq_zero_of_baseline_dominates_winner hb
  omega

/-- Actual compact-image boundedness supplies each pointwise gate from the
selected branch's genuine infimum test, including ordering-wall points. -/
theorem actualExtendedThirdLeastWinningIndex_pairXZ_wholeCell {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (hk : actualExtendedThirdLeastWinningIndex e m j = 6)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    e ≤ v (t 0 + t 2) - (t 0 + 2 * t 1 + t 2) :=
  actualExtendedThirdRobustGateXZ_sound (actualExtendedThirdLeastWinningIndex_pairXZ_gate hk) ht

theorem actualExtendedThirdLeastWinningIndex_pairYZ_wholeCell {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (hk : actualExtendedThirdLeastWinningIndex e m j = 7)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    e ≤ v (t 1 + t 2) - (2 * t 0 + t 1 + t 2) :=
  actualExtendedThirdRobustGateYZ_sound (actualExtendedThirdLeastWinningIndex_pairYZ_gate hk) ht

theorem actualExtendedThirdLeastWinningIndex_pairXZ_endpoint_margin {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    (hk : actualExtendedThirdLeastWinningIndex e m j = 6)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    actualExtendedThirdPhysicalLevel e m j + 2 * e ≤ v (t 0 + t 2) := by
  have hg : actualExtendedThirdPhysicalGamma e m j =
      actualExtendedThirdCellInf m j actualExtendedThirdPairXZ := by
    rw [actualExtendedThirdPhysicalGamma, if_pos hfull,
      actualExtendedThirdFullGamma_eq_leastWinningValue, hk]
    simp [actualExtendedThirdRobustCandidate, actualExtendedThirdLeastWinningIndex_pairXZ_gate hk]
  have hl : actualExtendedThirdPhysicalLevel e m j ≤ actualExtendedThirdPhysicalGamma e m j - 2 * e :=
    min_le_right _ _
  have hp := actualExtendedThirdCellInf_le continuous_actualExtendedThirdPairXZ ht
  rw [hg] at hl
  change _ ≤ v (t 0 + t 2) at hp
  linarith

theorem actualExtendedThirdLeastWinningIndex_pairYZ_endpoint_margin {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    (hk : actualExtendedThirdLeastWinningIndex e m j = 7)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    actualExtendedThirdPhysicalLevel e m j + 2 * e ≤ v (t 1 + t 2) := by
  have hg : actualExtendedThirdPhysicalGamma e m j =
      actualExtendedThirdCellInf m j actualExtendedThirdPairYZ := by
    rw [actualExtendedThirdPhysicalGamma, if_pos hfull,
      actualExtendedThirdFullGamma_eq_leastWinningValue, hk]
    simp [actualExtendedThirdRobustCandidate, actualExtendedThirdLeastWinningIndex_pairYZ_gate hk]
  have hl : actualExtendedThirdPhysicalLevel e m j ≤ actualExtendedThirdPhysicalGamma e m j - 2 * e :=
    min_le_right _ _
  have hp := actualExtendedThirdCellInf_le continuous_actualExtendedThirdPairYZ ht
  rw [hg] at hl
  change _ ≤ v (t 1 + t 2) at hp
  linarith

/-- The singleton y branch cannot be the least winner on an actual full
closed ordered portion. Its missing selected-square license is not assumed. -/
theorem actualExtendedThirdLeastWinningIndex_ne_singletonY {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (hne : (actualExtendedThirdPhysicalCell m j).Nonempty)
    (hmu : actualExtendedThirdDyadicHi m j 0 ≤ mu) :
    actualExtendedThirdLeastWinningIndex e m j ≠ 1 := by
  have hdom : actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 1) ≤
      actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 0) := by
    apply le_csInf (hne.image _)
    rintro _ ⟨t, ht, rfl⟩
    have hinf := actualExtendedThirdCellInf_le (continuous_actualExtendedThirdRobustBaseBranch 1) ht
    have hx := (ht.1 0 (mem_univ _)).2.trans hmu
    have hy := ht.2.2.2.trans hx
    have hv : v (t 1) ≤ v (t 0) := by
      rw [v_eq_A hy, v_eq_A hx]
      dsimp [A]
      linarith [ht.2.2.2]
    exact hinf.trans hv
  intro hk
  have hb : actualExtendedThirdRobustCandidate e m j (actualExtendedThirdLeastWinningIndex e m j) ≤
      actualExtendedThirdRobustCandidate e m j 0 := by
    rw [hk]
    exact hdom
  have hz := leastIndex_eq_zero_of_baseline_dominates_winner hb
  omega

end

end ImbalancedChen
