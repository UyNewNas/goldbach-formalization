import ImbalancedChen.ActualExtendedThirdFirstCubeMargin
import ImbalancedChen.P4AFull87UnsupportedThirdAdmission

/-! The six original branch infima and two original whole-cell gates on the
closed ordered part of the actual (475q)-mesh rectangle. The label of a
history stays half-open. The table and its finite cardinal do not see w. -/
namespace ImbalancedChen.P4AOriginalOrderedThirdTable
noncomputable section
open Set HistoricalThirdCoarse VariableEnvelope
open scoped Classical

abbrev Point := Fin 3 → ℝ

def portion (m : ℕ) (j : Cell m) : Set Point :=
  univ.pi (fun i => Icc (logPrimeMeshLo 0 (19/96) m j i)
    (logPrimeMeshHi 0 (19/96) m j i)) ∩ actualExtendedThirdClosedOrder

def infimum (m : ℕ) (j : Cell m) (f : Point → ℝ) : ℝ :=
  sInf (f '' portion m j)

theorem compact_portion (m : ℕ) (j : Cell m) : IsCompact (portion m j) :=
  (isCompact_univ_pi (fun _ => isCompact_Icc)).inter_right isClosed_actualExtendedThirdClosedOrder

theorem inf_le {m : ℕ} {j : Cell m} {f : Point → ℝ} (hf : Continuous f)
    {t : Point} (ht : t ∈ portion m j) : infimum m j f ≤ f t :=
  csInf_le ((compact_portion m j).image hf).bddBelow (mem_image_of_mem f ht)

def full (e : ℝ) (m : ℕ) (j : Cell m) : ℝ :=
  let b := fun k => infimum m j (actualExtendedThirdRobustBaseBranch k)
  max (b 0) (max (b 1) (max (b 2) (max (b 3) (max (b 4) (max (b 5)
    (max (if e ≤ infimum m j actualExtendedThirdGateXZ then
      infimum m j actualExtendedThirdPairXZ else b 0)
      (if e ≤ infimum m j actualExtendedThirdGateYZ then
        infimum m j actualExtendedThirdPairYZ else b 0)))))))

def envelope (e : ℝ) (m : ℕ) (j : Cell m) : ℝ :=
  if logPrimeMeshHi 0 (19/96) m j 0 ≤ mu-4*e then full e m j
  else infimum m j (actualExtendedThirdRobustBaseBranch 0)

def capValue (e : ℝ) (m : ℕ) (j : Cell m) : ℝ :=
  thirdPrefixBufferedCap e (envelope e m j)

def retained (e : ℝ) (m : ℕ) : Finset (Cell m) :=
  Finset.univ.filter (fun j => (portion m j).Nonempty ∧
    logPrimeMeshHi 0 (19/96) m j 0 ≤ extendedFirstStop-4*e)

def catalogue (e : ℝ) (m : ℕ) : Finset ℝ :=
  insert (initial e) ((retained e m).image (capValue e m))

theorem catalogue_card_le (e : ℝ) (m : ℕ) :
    (catalogue e m).card ≤ (m+1)^3+1 := by
  have hc := Finset.card_le_card (Finset.filter_subset _ _
    : retained e m ⊆ (Finset.univ : Finset (Cell m)))
  have hf : (Finset.univ : Finset (Cell m)).card=(m+1)^3 := by simp [Cell]
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
    (Finset.card_image_le.trans (hc.trans hf.le)) 1)

theorem owned_portion {m : ℕ} {j : Cell m} {t : Point}
    (ht : t ∈ logPrimeMeshCell 0 (19/96) m j) (ho : t ∈ actualExtendedThirdClosedOrder) :
    t ∈ portion m j :=
  ⟨fun i _ => ⟨(mem_logPrimeMeshCell.mp ht i).1,(mem_logPrimeMeshCell.mp ht i).2.le⟩,ho⟩

theorem cap_on_ordered {e : ℝ} (he : 0≤e) {m : ℕ} {j : Cell m} {t : Point}
    (ht : t ∈ portion m j) : capValue e m j ≤ VariableEnvelope.cap-2*e := by
  suffices hg : envelope e m j ≤ VariableEnvelope.cap by
    exact (min_le_right _ _).trans (sub_le_sub_right hg _)
  unfold envelope
  split_ifs with h
  · have h0 := (ht.1 0 (mem_univ _)).2
    have ho : Ordered (t 0) (t 1) (t 2) := ⟨ht.2.1,ht.2.2.1,ht.2.2.2,by linarith⟩
    have hb (k : Fin 6) := (inf_le (continuous_actualExtendedThirdRobustBaseBranch k) ht).trans
      ((actualExtendedThirdRobustBaseBranch_le_six ho k).trans (six_le_cap _ _ ht.2.1))
    have hx := (inf_le continuous_actualExtendedThirdPairXZ ht).trans (v_le_cap _)
    have hy := (inf_le continuous_actualExtendedThirdPairYZ ht).trans (v_le_cap _)
    dsimp only [full]
    split_ifs <;> simp only [max_le_iff] <;>
      exact ⟨hb 0,hb 1,hb 2,hb 3,hb 4,hb 5,by first | exact hx | exact hb 0,
        by first | exact hy | exact hb 0⟩
  · exact (inf_le (continuous_actualExtendedThirdRobustBaseBranch 0) ht).trans (v_le_cap _)

theorem first_cube {e : ℝ} (he : 0<e) (he' : e≤1/384) {m : ℕ}
    (hstep : logPrimeMeshStep 0 (19/96) m ≤ e/2) {j : Cell m} {t : Point}
    (ht : t ∈ portion m j)
    (hstop : logPrimeMeshHi 0 (19/96) m j 0 ≤ extendedFirstStop-4*e) :
    3*t 0 < capValue e m j := by
  have hh := (ht.1 0 (mem_univ _)).2.trans hstop
  have hb : 3*t 0+3*e ≤ infimum m j (actualExtendedThirdRobustBaseBranch 0) := by
    apply le_csInf ((show (portion m j).Nonempty from ⟨t,ht⟩).image _)
    rintro _ ⟨s,hs,rfl⟩
    change 3*t 0+3*e ≤ v (s 0)
    have hs' := actualExtendedThird_v_firstCube_margin he.le he' ((hs.1 0 (mem_univ _)).2.trans hstop)
    have hl := (hs.1 0 (mem_univ _)).1
    have hu := (ht.1 0 (mem_univ _)).2
    rw [logPrimeMeshHi_eq_lo_add_step] at hu
    linarith
  have hg : infimum m j (actualExtendedThirdRobustBaseBranch 0) ≤ envelope e m j := by
    unfold envelope
    split_ifs <;> first | exact le_max_left _ _ | exact le_rfl
  change 3*t 0 < min (thirdPrefixTheta-2*e) (envelope e m j-2*e)
  exact lt_min (by dsimp [extendedFirstStop,thirdPrefixTheta] at *; linarith) (by linarith)

def atPoint (e : ℝ) (m : ℕ) (t : Point) : ℝ :=
  if h : ∃ j ∈ retained e m, t ∈ logPrimeMeshCell 0 (19/96) m j then
    capValue e m h.choose else initial e

theorem atPoint_on_cell {e : ℝ} {m : ℕ} {j : Cell m} {t : Point}
    (hj : j ∈ retained e m) (ht : t ∈ logPrimeMeshCell 0 (19/96) m j) :
    atPoint e m t=capValue e m j := by
  have H : ∃ i ∈ retained e m, t ∈ logPrimeMeshCell 0 (19/96) m i := ⟨j,hj,ht⟩
  rw [atPoint,dif_pos H,logPrimeMeshCell_unique (by norm_num) H.choose_spec.2 ht]

def rawExponent (e : ℝ) (m : ℕ) (omega N : ℝ) (history : List ℕ) : ℝ :=
  if active omega N history then atPoint e m (primeHistoryLogCoordinates N 3 history)
  else initial e

def policy (e : ℝ) (m : ℕ) (omega N : ℝ) : Bool → List ℕ → Bool :=
  thirdCappedUpperPolicy (initialPolicy e m N) (fun h => N ^ rawExponent e m omega N h)

theorem raw_mem (e : ℝ) (m : ℕ) (omega N : ℝ) (history : List ℕ) :
    rawExponent e m omega N history ∈ catalogue e m := by
  unfold rawExponent atPoint
  split_ifs with ha h
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨h.choose,h.choose_spec.1,rfl⟩)
  all_goals exact Finset.mem_insert_self _ _

/-- At the actual physical cutoff, every ordered occupied cell of a
retained first label receives its own precomputed value. No historical
third cutoff, separated coarse labels, or certificate catalogue is used. -/
theorem raw_on_physical_triple {e omega N : ℝ} {m : ℕ} {p1 p2 p3 : ℕ}
    (hw : N^omega ≤ (p3:ℝ)) {j : Cell m}
    (ht : primeHistoryLogCoordinates N 3 [p3,p2,p1] ∈ logPrimeMeshCell 0 (19/96) m j)
    (ho : primeHistoryLogCoordinates N 3 [p3,p2,p1] ∈ actualExtendedThirdClosedOrder)
    (hs : logPrimeMeshHi 0 (19/96) m j 0 ≤ extendedFirstStop-4*e) :
    rawExponent e m omega N [p3,p2,p1]=capValue e m j := by
  rw [rawExponent,if_pos ((active_triple omega N p1 p2 p3).mpr hw)]
  exact atPoint_on_cell (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨_,owned_portion ht ho⟩,hs⟩) ht

theorem old_missed_first_interval {d : P5OriginalCommonRefinedConstructor.OriginalData}
    {N : ℝ} {pre : List ℕ}
    (h0 : primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 0 <
      logPrimeMeshPoint 0 (19/96) d.m 1) :
    P4AFull87UnsupportedThirdAdmission.missed d N pre := by
  rintro ⟨_,j,hj,ht⟩
  have hlo := (mem_logPrimeMeshCell.mp ht (0:Fin 3)).1
  have hj0 : (j 0).val=0 := by
    by_contra hn
    have hmono := logPrimeMeshPoint_mono (by norm_num : (0:ℝ)≤19/96) d.m
      (by omega : 1≤(j 0).val)
    exact (not_lt_of_ge (hmono.trans hlo)) h0
  have horder := ((mem_cells _ _ _ _).mp hj).2.2.2.1
  change qLogPrimeMeshPoint 0 (19/96) d.m ((j 1).val+1) ≤
    qLogPrimeMeshPoint 0 (19/96) d.m (j 0).val at horder
  rw [hj0] at horder
  have hp : 0<qLogPrimeMeshPoint 0 (19/96) d.m ((j 1).val+1) := by
    unfold qLogPrimeMeshPoint
    positivity
  exact (not_le_of_gt hp) (by simpa [qLogPrimeMeshPoint] using horder)

end
end ImbalancedChen.P4AOriginalOrderedThirdTable
