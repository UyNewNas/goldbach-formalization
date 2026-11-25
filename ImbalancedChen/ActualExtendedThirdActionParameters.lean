import ImbalancedChen.ActualExtendedThirdLeastWinningIndex

/-!
# Actual full-cell parameters and rescued-W actions

The genuine W1 rescue infimum gives Gamma >= B(mu) on a nonempty full
closed ordered cell. Thus Gamma-e lies in the source parameter range and
above the actual buffered level. The deterministic winning index then
supplies actual branch values through the compact continuous-image infima.

The W split uses the literal gate v(x), retaining equality in the baseline
case. Both alternatives have positive quantitative slack. The pair choices
likewise use their actual whole-cell robust gates. These are actual analytic
parameter choices, not an abstract License supplied by the caller.

Freezing a point-selected parameter on a refining fine atom, perturbing alpha,
and the p/q factorization and arithmetic mean are not asserted here.
-/

namespace ImbalancedChen

noncomputable section

open Set
open VariableEnvelope
open scoped Classical

theorem actualExtendedThirdFullGamma_ge_Bmu {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (hne : (actualExtendedThirdPhysicalCell m j).Nonempty)
    (hmu : actualExtendedThirdDyadicHi m j 0 ≤ mu) :
    B mu ≤ actualExtendedThirdFullGamma e m j := by
  apply le_trans ?_ (actualExtendedThirdRobustCandidate_le_fullGamma e m j 4)
  change B mu ≤ actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 4)
  apply le_csInf (hne.image _)
  rintro _ ⟨t, ht, rfl⟩
  have hx := (ht.1 0 (mem_univ _)).2.trans hmu
  have hy := ht.2.2.2.trans hx
  have hz := ht.2.2.1.trans hy
  change B mu ≤ max (v (t 0)) (wInner (t 0) (t 1) (t 2))
  rw [wInner_eq_B (t 0) hy ht.2.1]
  apply le_max_of_le_right
  dsimp [B]
  linarith

theorem actualExtendedThirdFullGamma_le_cap {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (hne : (actualExtendedThirdPhysicalCell m j).Nonempty)
    (hmu : actualExtendedThirdDyadicHi m j 0 ≤ mu) :
    actualExtendedThirdFullGamma e m j ≤ cap := by
  obtain ⟨t, ht⟩ := hne
  have ho : Ordered (t 0) (t 1) (t 2) :=
    ⟨ht.2.1, ht.2.2.1, ht.2.2.2, (ht.1 0 (mem_univ _)).2.trans hmu⟩
  exact (actualExtendedThirdFullGamma_le_original ht ho).trans (original_le_cap ho)

def actualExtendedThirdBaseParameter (e : ℝ) (m : ℕ) (j : ActualExtendedThirdDyadicLabel m) : ℝ :=
  actualExtendedThirdFullGamma e m j - e

theorem actualExtendedThirdBaseParameter_range {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hne : (actualExtendedThirdPhysicalCell m j).Nonempty)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e) :
    1 / 2 ≤ actualExtendedThirdBaseParameter e m j ∧ actualExtendedThirdBaseParameter e m j < 5 / 8 := by
  have hmu : actualExtendedThirdDyadicHi m j 0 ≤ mu := by linarith
  have hlo := actualExtendedThirdFullGamma_ge_Bmu (e := e) hne hmu
  have hhi := actualExtendedThirdFullGamma_le_cap (e := e) hne hmu
  dsimp [actualExtendedThirdBaseParameter, B, cap, mu] at *
  constructor <;> linarith

theorem actualExtendedThirdBaseParameter_above_level {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e) :
    actualExtendedThirdPhysicalLevel e m j + e ≤ actualExtendedThirdBaseParameter e m j := by
  have hl : actualExtendedThirdPhysicalLevel e m j ≤ actualExtendedThirdPhysicalGamma e m j - 2 * e :=
    min_le_right _ _
  rw [actualExtendedThirdPhysicalGamma, if_pos hfull] at hl
  unfold actualExtendedThirdBaseParameter
  linarith

/-- The selected base branch is licensed by its actual compact-image infimum.
The exact branch equality is proved by the finite eight-entry definition. -/
theorem actualExtendedThirdSelectedBase_pointwise {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (k : Fin 6)
    (hk : actualExtendedThirdLeastWinningIndex e m j = Fin.castLE (by decide : 6 ≤ 8) k)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    actualExtendedThirdBaseParameter e m j + e ≤ actualExtendedThirdRobustBaseBranch k t := by
  have hindex : actualExtendedThirdRobustCandidate e m j (Fin.castLE (by decide : 6 ≤ 8) k) =
      actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch k) := by
    fin_cases k <;> rfl
  unfold actualExtendedThirdBaseParameter
  have hp := actualExtendedThirdCellInf_le (continuous_actualExtendedThirdRobustBaseBranch k) ht
  rw [← hindex, ← hk, ← actualExtendedThirdFullGamma_eq_leastWinningValue] at hp
  linarith

private theorem wInner_le_cap {a b c : ℝ} (hc : 0 ≤ c) : wInner a b c ≤ cap := by
  have hw : wInner a b c ≤ B c := (min_le_right _ _).trans (min_le_left _ _)
  have hb : B c ≤ cap := by dsimp [B]; linarith
  exact hw.trans hb

def actualExtendedThirdRescueParameter (e : ℝ) (m : ℕ) (j : ActualExtendedThirdDyadicLabel m)
    (t : Fin 3 → ℝ) : ℝ :=
  max (actualExtendedThirdBaseParameter e m j) (v (t 0) + e / 8)

private theorem rescue_split {e lam θ a W : ℝ} (he : 0 < e)
    (hθlo : 1 / 2 ≤ θ) (hθhi : θ < 5 / 8) (hlevel : lam + e ≤ θ)
    (hp : θ + e ≤ max a W) (hW : W ≤ cap) :
    (W - a ≤ e / 4 ∧ 1 / 2 ≤ θ ∧ θ < 5 / 8 ∧ lam + e ≤ θ ∧ θ + 3 * e / 4 ≤ a) ∨
      (e / 4 < W - a ∧ 1 / 2 ≤ max θ (a + e / 8) ∧ max θ (a + e / 8) < 5 / 8 ∧
        lam + e ≤ max θ (a + e / 8) ∧ a + e / 8 ≤ max θ (a + e / 8) ∧
          max θ (a + e / 8) + e / 8 ≤ W) := by
  by_cases hclose : W - a ≤ e / 4
  · have hm : max a W ≤ a + e / 4 := max_le (by linarith) (by linarith)
    exact Or.inl ⟨hclose, hθlo, hθhi, hlevel, by linarith⟩
  · have hgap : e / 4 < W - a := lt_of_not_ge hclose
    have haW : a ≤ W := by linarith
    rw [max_eq_right haW] at hp
    have hupper : max θ (a + e / 8) ≤ W - e / 8 := max_le (by linarith) (by linarith)
    have hrange : max θ (a + e / 8) < 5 / 8 := by
      dsimp [cap] at hW
      linarith
    exact Or.inr ⟨hgap, hθlo.trans (le_max_left _ _), hrange,
      hlevel.trans (le_max_left _ _), le_max_right _ _, by linarith⟩

/-- This deterministic split applies to either genuine rescued-W entry.
At the equality threshold the baseline action is selected. Every value and
gate premise is paid from the selected actual cell and its true branch. -/
theorem actualExtendedThirdSelectedRescue_action {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (swapped : Bool)
    (hk : actualExtendedThirdLeastWinningIndex e m j = if swapped then 5 else 4) :
    let W := if swapped then wInner (t 0) (t 2) (t 1) else wInner (t 0) (t 1) (t 2)
    (W - v (t 0) ≤ e / 4 ∧ 1 / 2 ≤ actualExtendedThirdBaseParameter e m j ∧
      actualExtendedThirdBaseParameter e m j < 5 / 8 ∧
      actualExtendedThirdPhysicalLevel e m j + e ≤ actualExtendedThirdBaseParameter e m j ∧
        actualExtendedThirdBaseParameter e m j + 3 * e / 4 ≤ v (t 0)) ∨
    (e / 4 < W - v (t 0) ∧ 1 / 2 ≤ actualExtendedThirdRescueParameter e m j t ∧
      actualExtendedThirdRescueParameter e m j t < 5 / 8 ∧
      actualExtendedThirdPhysicalLevel e m j + e ≤ actualExtendedThirdRescueParameter e m j t ∧
      v (t 0) + e / 8 ≤ actualExtendedThirdRescueParameter e m j t ∧
        actualExtendedThirdRescueParameter e m j t + e / 8 ≤ W) := by
  have hr := actualExtendedThirdBaseParameter_range he0 he ⟨t, ht⟩ hfull
  have hl := actualExtendedThirdBaseParameter_above_level hfull
  have hp : actualExtendedThirdBaseParameter e m j + e ≤
      max (v (t 0)) (if swapped then wInner (t 0) (t 2) (t 1) else wInner (t 0) (t 1) (t 2)) := by
    cases swapped
    · exact actualExtendedThirdSelectedBase_pointwise 4 hk ht
    · exact actualExtendedThirdSelectedBase_pointwise 5 hk ht
  have hW : (if swapped then wInner (t 0) (t 2) (t 1) else wInner (t 0) (t 1) (t 2)) ≤ cap := by
    cases swapped
    · exact wInner_le_cap (a := t 0) ht.2.1
    · exact wInner_le_cap (a := t 0) (ht.2.1.trans ht.2.2.1)
  exact rescue_split he0 hr.1 hr.2 hl hp hW

def actualExtendedThirdPairParameter (e : ℝ) (m : ℕ) (j : ActualExtendedThirdDyadicLabel m)
    (t : Fin 3 → ℝ) (yz : Bool) : ℝ :=
  max (actualExtendedThirdBaseParameter e m j)
    ((if yz then 2 * t 0 + t 1 + t 2 else t 0 + 2 * t 1 + t 2) + e / 2)

private theorem pair_parameter {e lam θ a g : ℝ} (he : 0 < e)
    (hθlo : 1 / 2 ≤ θ) (hlevel : lam + e ≤ θ) (ha : θ + e ≤ a)
    (hg : e ≤ a - g) (hcap : a ≤ cap) :
    1 / 2 ≤ max θ (g + e / 2) ∧ max θ (g + e / 2) < 5 / 8 ∧
      lam + e ≤ max θ (g + e / 2) ∧ g + e / 2 ≤ max θ (g + e / 2) ∧
        max θ (g + e / 2) + e / 2 ≤ a := by
  have hu : max θ (g + e / 2) ≤ a - e / 2 := max_le (by linarith) (by linarith)
  have hhi : max θ (g + e / 2) < 5 / 8 := by dsimp [cap] at hcap; linarith
  exact ⟨hθlo.trans (le_max_left _ _), hhi, hlevel.trans (le_max_left _ _),
    le_max_right _ _, by linarith⟩

theorem actualExtendedThirdSelectedPair_action {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (yz : Bool) (hk : actualExtendedThirdLeastWinningIndex e m j = if yz then 7 else 6) :
    1 / 2 ≤ actualExtendedThirdPairParameter e m j t yz ∧
      actualExtendedThirdPairParameter e m j t yz < 5 / 8 ∧
      actualExtendedThirdPhysicalLevel e m j + e ≤ actualExtendedThirdPairParameter e m j t yz ∧
      (if yz then 2 * t 0 + t 1 + t 2 else t 0 + 2 * t 1 + t 2) + e / 2 ≤
        actualExtendedThirdPairParameter e m j t yz ∧
      actualExtendedThirdPairParameter e m j t yz + e / 2 ≤
        v (if yz then t 1 + t 2 else t 0 + t 2) := by
  have hr := actualExtendedThirdBaseParameter_range he0 he ⟨t, ht⟩ hfull
  have hl := actualExtendedThirdBaseParameter_above_level hfull
  have hp : actualExtendedThirdBaseParameter e m j + e ≤
      v (if yz then t 1 + t 2 else t 0 + t 2) := by
    unfold actualExtendedThirdBaseParameter
    cases yz
    · rw [actualExtendedThirdFullGamma_eq_leastWinningValue, hk]
      change _ - e + e ≤ v (t 0 + t 2)
      have hb := actualExtendedThirdCellInf_le continuous_actualExtendedThirdPairXZ ht
      have hg := actualExtendedThirdLeastWinningIndex_pairXZ_gate hk
      simp only [actualExtendedThirdRobustCandidate, if_pos hg]
      change actualExtendedThirdCellInf m j actualExtendedThirdPairXZ - e + e ≤ v (t 0 + t 2)
      change _ ≤ v (t 0 + t 2) at hb
      linarith
    · rw [actualExtendedThirdFullGamma_eq_leastWinningValue, hk]
      change _ - e + e ≤ v (t 1 + t 2)
      have hb := actualExtendedThirdCellInf_le continuous_actualExtendedThirdPairYZ ht
      have hg := actualExtendedThirdLeastWinningIndex_pairYZ_gate hk
      simp only [actualExtendedThirdRobustCandidate, if_pos hg]
      change actualExtendedThirdCellInf m j actualExtendedThirdPairYZ - e + e ≤ v (t 1 + t 2)
      change _ ≤ v (t 1 + t 2) at hb
      linarith
  have hg : e ≤ v (if yz then t 1 + t 2 else t 0 + t 2) -
      (if yz then 2 * t 0 + t 1 + t 2 else t 0 + 2 * t 1 + t 2) := by
    cases yz
    · exact actualExtendedThirdLeastWinningIndex_pairXZ_wholeCell hk ht
    · exact actualExtendedThirdLeastWinningIndex_pairYZ_wholeCell hk ht
  exact pair_parameter he0 hr.1 hl hp hg (v_le_cap _)

end

end ImbalancedChen
