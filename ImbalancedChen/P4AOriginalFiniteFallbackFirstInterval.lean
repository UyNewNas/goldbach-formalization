import ImbalancedChen.P4AOriginalFiniteFallbackSmallThird
import ImbalancedChen.P4AOrderedThirdCompactComparison

namespace ImbalancedChen.P4AOriginalFiniteFallbackFirstInterval
noncomputable section
open Set HistoricalThirdCoarse VariableEnvelope
open P4AOriginalOrderedThirdTable
open P4AOriginalFiniteFallbackSmallThird (floorLevel)
open scoped Classical

/-- On the high side of the kink the infimum only sees the *first* bin.
Increasing the first coordinate to its closed upper end preserves the
ordered portion even when the three primes occupy the very same bin. -/
theorem high_infimum {m : ℕ} {j : Cell m} {t : Point} (ht : t∈portion m j)
    (hl : mu≤logPrimeMeshLo 0 (19/96) m j 0) :
    infimum m j (actualExtendedThirdRobustBaseBranch 0)=v (logPrimeMeshHi 0 (19/96) m j 0) := by
  let u := logPrimeMeshHi 0 (19/96) m j 0
  let t' : Point := ![u,t 1,t 2]
  have hu : t 0≤u := (ht.1 0 (mem_univ _)).2
  have ht' : t'∈portion m j := by
    refine ⟨?_,?_⟩
    · intro i _
      fin_cases i
      · exact ⟨((ht.1 0 (mem_univ _)).1.trans hu),le_rfl⟩
      · exact ht.1 1 (mem_univ _)
      · exact ht.1 2 (mem_univ _)
    · exact ⟨ht.2.1,ht.2.2.1,ht.2.2.2.trans hu⟩
  apply le_antisymm (inf_le (continuous_actualExtendedThirdRobustBaseBranch 0) ht')
  apply le_csInf ((show (portion m j).Nonempty from ⟨t,ht⟩).image _)
  rintro _ ⟨s,hs,rfl⟩
  change v u≤v (s 0)
  have hx := hs.1 0 (mem_univ _)
  rw [v_eq_C (hl.trans (hx.1.trans hx.2)),v_eq_C (hl.trans hx.1)]
  dsimp [C]; linarith [hx.2]

theorem high_cap {e : ℝ} (he : 0≤e) {m : ℕ} {j : Cell m} {t : Point}
    (ht : t∈portion m j) (hhi : mu<t 0) (hl : mu≤logPrimeMeshLo 0 (19/96) m j 0) :
    capValue e m j=v (logPrimeMeshHi 0 (19/96) m j 0)-2*e := by
  have hn : ¬logPrimeMeshHi 0 (19/96) m j 0≤mu-4*e := by linarith [(ht.1 0 (mem_univ _)).2]
  have hc : v (logPrimeMeshHi 0 (19/96) m j 0)≤thirdPrefixTheta :=
    (v_le_cap _).trans (by norm_num [VariableEnvelope.cap,thirdPrefixTheta])
  simp only [capValue,thirdPrefixBufferedCap,envelope,if_neg hn,high_infimum ht hl,
    min_eq_right (sub_le_sub_right hc (2*e))]

theorem high_error {m : ℕ} {j : Cell m} {t : Point} (ht : t∈portion m j)
    (hl : mu≤logPrimeMeshLo 0 (19/96) m j 0) {e : ℝ} (he : 0≤e) (hx : mu<t 0) :
    0≤v (t 0)-capValue e m j ∧ v (t 0)-capValue e m j≤2*e+3/2*logPrimeMeshStep 0 (19/96) m := by
  have h := ht.1 0 (mem_univ _)
  rw [high_cap he ht hx hl,v_eq_C hx.le,v_eq_C (hx.le.trans h.2)]
  have hu := logPrimeMeshHi_eq_lo_add_step 0 (19/96) m j 0
  dsimp [C]; constructor <;> linarith

theorem lower_floor {e : ℝ} (he : e≤1/2048) (m : ℕ) (w N : ℝ) (p : List ℕ) :
    floorLevel≤rawExponent e m w N p := by
  have root : floorLevel≤initial e := by
    dsimp [floorLevel,initial,extendedDistributionCap]; linarith
  unfold rawExponent atPoint
  split_ifs with ha hh
  · let j := hh.choose
    have hret := (Finset.mem_filter.mp hh.choose_spec.1).2
    have hb : (1/2:ℝ)≤infimum m j (actualExtendedThirdRobustBaseBranch 0) := by
      apply le_csInf (hret.1.image _)
      rintro _ ⟨s,hs,rfl⟩
      apply half_le_v_of_extended_range (hs.2.1.trans (hs.2.2.1.trans hs.2.2.2))
      exact (hs.1 0 (mem_univ _)).2.trans (logPrimeMeshLoHi_bounds (by norm_num : (0:ℝ)<19/96) m j 0).2.2
    have hg : 1/2≤envelope e m j := by
      unfold envelope
      split_ifs <;> first | exact hb.trans (le_max_left _ _) | exact hb
    exact le_min root (by dsimp [floorLevel]; linarith)
  all_goals exact root

end
end ImbalancedChen.P4AOriginalFiniteFallbackFirstInterval
