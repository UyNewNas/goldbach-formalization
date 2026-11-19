import ImbalancedChen.P4AFallbackUniformMargins

/-! SOURCE_ONLY / UNCOMPILED.
One actual finite canonical bank covers BOTH original compact trims,
with closed-box cap errors arbitrarily small. The selected owner is Ico;
the licensing/margin/approximation statements include BOTH corners.
Every choice precedes historical and physical rough cutoffs and N.
-/
namespace ImbalancedChen.P4AFallbackJointFiniteCover
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter VariableEnvelope
open P4AFallbackCanonicalBanks P4AFallbackCompactEndpointCover
open P4AFallbackOriginalCompactTrims P4AFallbackUniformMargins
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient (secondMask thirdMask)
open P4AOriginalFiniteFallbackBank (read read_some_iff)

theorem closed_coordinate_bounds {k : ℕ} (m : ℕ) (j : Label k m) (t : Point k)
    (ht : t∈closedBox m j) (i : Fin k) :
    (lo m j i : ℝ)≤t i ∧ t i≤(hi m j i : ℝ) ∧
      (hi m j i : ℝ)-(lo m j i : ℝ)=logPrimeMeshStep 0 (19/96) m := by
  refine ⟨ht.1 i,ht.2 i,?_⟩
  unfold lo hi
  rw [congrFun (cast_qLogPrimeMeshHi 0 (19/96) m j) i,
    congrFun (cast_qLogPrimeMeshLo 0 (19/96) m j) i]
  norm_num only [Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat]
  rw [logPrimeMeshHi_eq_lo_add_step]
  ring

theorem second_closed_error (m : ℕ) (j : Label 2 m) (t : Point 2) (ht : t∈closedBox m j) :
    0<v (t 1)-(level2 m j : ℝ) ∧
      v (t 1)-(level2 m j : ℝ)≤3*logPrimeMeshStep 0 (19/96) m+width m := by
  obtain ⟨hl,hu,hw⟩ := closed_coordinate_bounds m j t ht 1
  have he := rationalInterval_v_error hl hu
  rw [hw] at he
  have hup := qVLo_le_v hl hu
  have hb : (0 : ℝ)<buffer m := by exact_mod_cast buffer_pos m
  have hstep : 0≤logPrimeMeshStep 0 (19/96) m := (logPrimeMeshStep_pos (by norm_num) m).le
  unfold level2
  push_cast
  have hbcast : (buffer m : ℝ)=width m := by
    simp only [buffer_cast,P4AOriginalFull87HistoryCore.width]
  change v (t 1)-(qVLo (lo m j 1) (hi m j 1) : ℝ)≤_ at he
  change (qVLo (lo m j 1) (hi m j 1) : ℝ)≤v (t 1) at hup
  change 0<v (t 1)-((qVLo (lo m j 1) (hi m j 1) : ℝ)-(buffer m : ℝ)) ∧
    v (t 1)-((qVLo (lo m j 1) (hi m j 1) : ℝ)-(buffer m : ℝ))≤_
  constructor <;> linarith

theorem third_closed_error (m : ℕ) (j : Label 3 m) (t : Point 3) (ht : t∈closedBox m j) :
    0<v (t 1+t 2)-(level3 m j : ℝ) ∧
      v (t 1+t 2)-(level3 m j : ℝ)≤3*logPrimeMeshStep 0 (19/96) m+width m := by
  obtain ⟨hl1,hu1,hw1⟩ := closed_coordinate_bounds m j t ht 1
  obtain ⟨hl2,hu2,hw2⟩ := closed_coordinate_bounds m j t ht 2
  have hl : ((lo m j 1+lo m j 2 : ℚ) : ℝ)≤t 1+t 2 := by push_cast;linarith
  have hu : t 1+t 2≤((hi m j 1+hi m j 2 : ℚ) : ℝ) := by push_cast;linarith
  have he := rationalInterval_v_error hl hu
  push_cast at he
  have hup := qVLo_le_v hl hu
  have hb : (0 : ℝ)<buffer m := by exact_mod_cast buffer_pos m
  have hbcast : (buffer m : ℝ)=width m := by
    simp only [buffer_cast,P4AOriginalFull87HistoryCore.width]
  unfold level3
  push_cast
  change 0<v (t 1+t 2)-((qVLo (lo m j 1+lo m j 2) (hi m j 1+hi m j 2) : ℝ)-(buffer m : ℝ)) ∧
    v (t 1+t 2)-((qVLo (lo m j 1+lo m j 2) (hi m j 1+hi m j 2) : ℝ)-(buffer m : ℝ))≤_
  constructor <;> linarith

theorem exists_endpoint_accuracy (eta : ℝ) (heta : 0<eta) :
    ∃ m0 : ℕ,∀ m : ℕ,m0≤m → 3*logPrimeMeshStep 0 (19/96) m+width m<eta := by
  have h : Tendsto (fun m : ℕ => 3*logPrimeMeshStep 0 (19/96) m+width m) atTop (𝓝 0) := by
    simpa using ((tendsto_logPrimeMeshStep 0 (19/96)).const_mul (3 : ℝ)).add width_tendsto
  exact eventually_atTop.mp (h.eventually (gt_mem_nhds heta))

/-- Public simultaneous finite-family supplier. No history, rough
cutoff, target, cap licence or preselected finite owner is an input.
-/
theorem exists_joint_original_cover (delta : ℝ) (hd : 0<delta) (r : ℕ)
    (eta : ℝ) (heta : 0<eta) (mMin : ℕ) :
    ∃ m0 : ℕ,mMin≤m0 ∧ ∀ m : ℕ,m0≤m →
      (∀ t∈secondCore delta,∃! j : Label 2 m,
        t∈logPrimeMeshCell 0 (19/96) m j ∧ (bank m).second j=some (level2 m j)) ∧
      (∀ t∈thirdCore r,∃! j : Label 3 m,
        t∈logPrimeMeshCell 0 (19/96) m j ∧ (bank m).third j=some (level3 m j)) ∧
      (∀ j : Label 2 m,∀ t∈closedBox m j,0<v (t 1)-(level2 m j : ℝ) ∧ v (t 1)-(level2 m j : ℝ)<eta) ∧
      (∀ j : Label 3 m,∀ t∈closedBox m j,0<v (t 1+t 2)-(level3 m j : ℝ) ∧ v (t 1+t 2)-(level3 m j : ℝ)<eta) ∧
      0<(uniformMargin m : ℝ) := by
  obtain ⟨m2,_,h2⟩ := exists_second_core_owners delta hd
  obtain ⟨m3,_,h3⟩ := exists_third_core_owners r
  obtain ⟨ma,ha⟩ := exists_endpoint_accuracy eta heta
  refine ⟨max mMin (max m2 (max m3 ma)),le_max_left _ _,?_⟩
  intro m hm
  have hm2 : m2≤m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm3 : m3≤m := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  have hma : ma≤m := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  refine ⟨h2 m hm2,h3 m hm3,?_,?_,?_⟩
  · intro j t ht
    have he := second_closed_error m j t ht
    exact ⟨he.1,he.2.trans_lt (ha m hma)⟩
  · intro j t ht
    have he := third_closed_error m j t ht
    exact ⟨he.1,he.2.trans_lt (ha m hma)⟩
  · exact_mod_cast uniformMargin_pos m

/-- This is the exact support requested by the existing third gain
transport; its original continuous weighted trim limit is unchanged. -/
theorem joint_covers_original_third_test (delta : ℝ) (hd : 0<delta) (r : ℕ)
    (eta : ℝ) (heta : 0<eta) (mMin : ℕ) :
    ∃ m0 : ℕ,mMin≤m0 ∧ ∀ m : ℕ,m0≤m → ∀ t : Point 3,
      P4AOriginalThirdFallbackPrimeTests.combined r t≠0 →
      ∃ c : ℚ,read m (bank m).third t=some c ∧ 0<v (t 1+t 2)-(c : ℝ) ∧ v (t 1+t 2)-(c : ℝ)<eta := by
  obtain ⟨m0,hm0,hM⟩ := exists_joint_original_cover delta hd r eta heta mMin
  refine ⟨m0,hm0,?_⟩
  intro m hm t ht
  obtain ⟨j,hj,_⟩ := (hM m hm).2.1 t (third_combined_support r t ht)
  have he := (hM m hm).2.2.2.1 j t (meshCell_subset_closedBox m j hj.1)
  exact ⟨level3 m j,(read_some_iff).mpr ⟨j,hj.1,hj.2⟩,he⟩

end
end ImbalancedChen.P4AFallbackJointFiniteCover
