import ImbalancedChen.ActualExtendedThirdIdealCap

/-!
# Actual robust extended-third caps on closed ordered dyadic cells

The source is manuscript pin ba6ec11d800eccc54406490631895e174de85766:
`imbalanced-chen-transfer.tex:5300--5320` and
`extended-prefix-upper.tex:84--103`. Every infimum below is over the CLOSED
ORDERED PORTION of the dyadic box. This includes cells meeting an ordering
wall; an empty ordered portion is omitted explicitly.

The six base entries retain both rescue maxima from the full eight-branch
formula. The two nonleading pairs enter only after their actual whole-cell
gate-gap infimum is at least e. The transition strip uses only inf v(x), and
both retention walls are literal. All quantities are exact real infima;
none is the fixed-D numerical certificate's `extendedClippedLower`.

This file concerns the cell cap and its pointwise certificates. Common fine
ownership, the least-winning-branch action tie rule, coverage, convergence
Gamma -> A, and the same-policy arithmetic density are subsequent work.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology MeasureTheory
open VariableEnvelope
open scoped Classical

abbrev ActualExtendedThirdDyadicLabel (m : ℕ) := Fin 3 → Fin (2 ^ m)

def actualExtendedThirdDyadicLo (m : ℕ) (j : ActualExtendedThirdDyadicLabel m) (i : Fin 3) : ℝ :=
  thirdPrefixRho * (j i).val / (2 : ℝ) ^ m

def actualExtendedThirdDyadicHi (m : ℕ) (j : ActualExtendedThirdDyadicLabel m) (i : Fin 3) : ℝ :=
  thirdPrefixRho * ((j i).val + 1 : ℕ) / (2 : ℝ) ^ m

def actualExtendedThirdClosedOrder : Set (Fin 3 → ℝ) :=
  {t | 0 ≤ t 2 ∧ t 2 ≤ t 1 ∧ t 1 ≤ t 0}

def actualExtendedThirdPhysicalCell (m : ℕ) (j : ActualExtendedThirdDyadicLabel m) :
    Set (Fin 3 → ℝ) :=
  Set.univ.pi (fun i => Icc (actualExtendedThirdDyadicLo m j i)
    (actualExtendedThirdDyadicHi m j i)) ∩ actualExtendedThirdClosedOrder

theorem isClosed_actualExtendedThirdClosedOrder : IsClosed actualExtendedThirdClosedOrder := by
  have hx : Continuous (fun t : Fin 3 → ℝ => t 0) := continuous_apply 0
  have hy : Continuous (fun t : Fin 3 → ℝ => t 1) := continuous_apply 1
  have hz : Continuous (fun t : Fin 3 → ℝ => t 2) := continuous_apply 2
  exact (isClosed_le continuous_const hz).inter ((isClosed_le hz hy).inter (isClosed_le hy hx))

theorem isCompact_actualExtendedThirdPhysicalCell (m : ℕ) (j : ActualExtendedThirdDyadicLabel m) :
    IsCompact (actualExtendedThirdPhysicalCell m j) :=
  (isCompact_univ_pi (fun _ => isCompact_Icc)).inter_right isClosed_actualExtendedThirdClosedOrder

/-- Nonempty ordered portions are retained, including genuine wall cells. -/
def actualExtendedThirdRetainedCells (e : ℝ) (m : ℕ) : Finset (ActualExtendedThirdDyadicLabel m) :=
  Finset.univ.filter (fun j => (actualExtendedThirdPhysicalCell m j).Nonempty ∧
    actualExtendedThirdDyadicHi m j 0 ≤ thirdPrefixRho - 4 * e)

theorem mem_actualExtendedThirdRetainedCells {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} : j ∈ actualExtendedThirdRetainedCells e m ↔
      (actualExtendedThirdPhysicalCell m j).Nonempty ∧
        actualExtendedThirdDyadicHi m j 0 ≤ thirdPrefixRho - 4 * e := by
  simp only [actualExtendedThirdRetainedCells, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Exactly the six base entries listed in the source, before the two robust
pair tests. Rescue maxima are not permission to use an ungated W action. -/
def actualExtendedThirdRobustBaseBranch (k : Fin 6) (t : Fin 3 → ℝ) : ℝ :=
  ![v (t 0), v (t 1), v (t 0 + t 1), v (t 0 + t 1 + t 2),
    max (v (t 0)) (wInner (t 0) (t 1) (t 2)),
    max (v (t 0)) (wInner (t 0) (t 2) (t 1))] k

theorem continuous_actualExtendedThirdRobustBaseBranch (k : Fin 6) :
    Continuous (actualExtendedThirdRobustBaseBranch k) := by
  fin_cases k <;> unfold actualExtendedThirdRobustBaseBranch v wInner A B C cap <;> fun_prop

def actualExtendedThirdCellInf (m : ℕ) (j : ActualExtendedThirdDyadicLabel m)
    (f : (Fin 3 → ℝ) → ℝ) : ℝ := sInf (f '' actualExtendedThirdPhysicalCell m j)

theorem actualExtendedThirdCellInf_le {m : ℕ} {j : ActualExtendedThirdDyadicLabel m}
    {f : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdPhysicalCell m j) : actualExtendedThirdCellInf m j f ≤ f t := by
  apply csInf_le ((isCompact_actualExtendedThirdPhysicalCell m j).image hf).bddBelow
  exact mem_image_of_mem f ht

def actualExtendedThirdPairXZ (t : Fin 3 → ℝ) : ℝ := v (t 0 + t 2)
def actualExtendedThirdPairYZ (t : Fin 3 → ℝ) : ℝ := v (t 1 + t 2)
def actualExtendedThirdGateXZ (t : Fin 3 → ℝ) : ℝ :=
  actualExtendedThirdPairXZ t - (t 0 + 2 * t 1 + t 2)
def actualExtendedThirdGateYZ (t : Fin 3 → ℝ) : ℝ :=
  actualExtendedThirdPairYZ t - (2 * t 0 + t 1 + t 2)

theorem continuous_actualExtendedThirdPairXZ : Continuous actualExtendedThirdPairXZ :=
  continuous_v.comp ((continuous_apply 0).add (continuous_apply 2))

theorem continuous_actualExtendedThirdPairYZ : Continuous actualExtendedThirdPairYZ :=
  continuous_v.comp ((continuous_apply 1).add (continuous_apply 2))

theorem continuous_actualExtendedThirdGateXZ : Continuous actualExtendedThirdGateXZ := by
  unfold actualExtendedThirdGateXZ
  exact continuous_actualExtendedThirdPairXZ.sub
    (((continuous_apply 0).add ((continuous_apply 1).const_mul 2)).add (continuous_apply 2))

theorem continuous_actualExtendedThirdGateYZ : Continuous actualExtendedThirdGateYZ := by
  unfold actualExtendedThirdGateYZ
  exact continuous_actualExtendedThirdPairYZ.sub
    ((((continuous_apply 0).const_mul 2).add (continuous_apply 1)).add (continuous_apply 2))

theorem actualExtendedThirdRobustGateXZ_sound {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (he : e ≤ actualExtendedThirdCellInf m j actualExtendedThirdGateXZ)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    e ≤ v (t 0 + t 2) - (t 0 + 2 * t 1 + t 2) :=
  he.trans (actualExtendedThirdCellInf_le continuous_actualExtendedThirdGateXZ ht)

theorem actualExtendedThirdRobustGateYZ_sound {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (he : e ≤ actualExtendedThirdCellInf m j actualExtendedThirdGateYZ)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    e ≤ v (t 1 + t 2) - (2 * t 0 + t 1 + t 2) :=
  he.trans (actualExtendedThirdCellInf_le continuous_actualExtendedThirdGateYZ ht)

def actualExtendedThirdFullGamma (e : ℝ) (m : ℕ) (j : ActualExtendedThirdDyadicLabel m) : ℝ :=
  let b := fun k => actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch k)
  max (b 0) (max (b 1) (max (b 2) (max (b 3) (max (b 4) (max (b 5)
    (max (if e ≤ actualExtendedThirdCellInf m j actualExtendedThirdGateXZ then
      actualExtendedThirdCellInf m j actualExtendedThirdPairXZ else b 0)
      (if e ≤ actualExtendedThirdCellInf m j actualExtendedThirdGateYZ then
        actualExtendedThirdCellInf m j actualExtendedThirdPairYZ else b 0)))))))

/-- The upper endpoint, not a sampled point, decides the transition strip. -/
def actualExtendedThirdPhysicalGamma (e : ℝ) (m : ℕ) (j : ActualExtendedThirdDyadicLabel m) : ℝ :=
  if actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e then actualExtendedThirdFullGamma e m j
  else actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 0)

def actualExtendedThirdPhysicalLevel (e : ℝ) (m : ℕ) (j : ActualExtendedThirdDyadicLabel m) : ℝ :=
  thirdPrefixBufferedCap e (actualExtendedThirdPhysicalGamma e m j)

theorem actualExtendedThirdRobustBaseBranch_le_six {t : Fin 3 → ℝ}
    (ht : Ordered (t 0) (t 1) (t 2)) (k : Fin 6) :
    actualExtendedThirdRobustBaseBranch k t ≤ six (t 0) (t 1) (t 2) := by
  have hv := v_le_six (t 0) (t 1) (t 2)
  have hb := B_le_six (t 0) (t 1) (t 2)
  have hy : t 1 ≤ mu := ht.2.2.1.trans ht.2.2.2
  have hz : t 2 ≤ mu := ht.2.1.trans hy
  have hy0 : 0 ≤ t 1 := ht.1.trans ht.2.1
  have hvy : v (t 1) ≤ v (t 0) := by
    rw [v_eq_A hy, v_eq_A ht.2.2.2]
    dsimp [A]
    linarith [ht.2.2.1]
  have hby : B (t 1) ≤ B (t 2) := by
    dsimp [B]
    linarith [ht.2.1]
  fin_cases k
  · exact hv
  · exact hvy.trans hv
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  · change max (v (t 0)) (wInner (t 0) (t 1) (t 2)) ≤ _
    rw [wInner_eq_B (t 0) hy ht.1]
    exact max_le hv hb
  · change max (v (t 0)) (wInner (t 0) (t 2) (t 1)) ≤ _
    rw [wInner_eq_B (t 0) hz hy0]
    exact max_le hv (hby.trans hb)

theorem actualExtendedThirdFullGamma_le_original {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdPhysicalCell m j) (ho : Ordered (t 0) (t 1) (t 2)) :
    actualExtendedThirdFullGamma e m j ≤ original (t 0) (t 1) (t 2) := by
  have hb (k : Fin 6) : actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch k) ≤
      original (t 0) (t 1) (t 2) := by
    rw [original_eq_six ho]
    exact (actualExtendedThirdCellInf_le (continuous_actualExtendedThirdRobustBaseBranch k) ht).trans
      (actualExtendedThirdRobustBaseBranch_le_six ho k)
  have hpXZ : actualExtendedThirdCellInf m j actualExtendedThirdPairXZ ≤
      original (t 0) (t 1) (t 2) := by
    rw [original_eq_six ho]
    apply (actualExtendedThirdCellInf_le continuous_actualExtendedThirdPairXZ ht).trans
    simp only [actualExtendedThirdPairXZ, six]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _))))
  have hpYZ : actualExtendedThirdCellInf m j actualExtendedThirdPairYZ ≤
      original (t 0) (t 1) (t 2) := by
    rw [original_eq_six ho]
    apply (actualExtendedThirdCellInf_le continuous_actualExtendedThirdPairYZ ht).trans
    simp only [actualExtendedThirdPairYZ, six]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _))))
  unfold actualExtendedThirdFullGamma
  dsimp only
  refine max_le (hb 0) (max_le (hb 1) (max_le (hb 2) (max_le (hb 3)
    (max_le (hb 4) (max_le (hb 5) (max_le ?_ ?_))))))
  · split_ifs
    · exact hpXZ
    · exact hb 0
  · split_ifs
    · exact hpYZ
    · exact hb 0

/-- Every actual retained physical cell supplies a lower certificate for the
literal pointwise ideal envelope. No certificate-box identity is assumed. -/
theorem actualExtendedThirdPhysicalGamma_le_envelope {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he : 0 ≤ e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    actualExtendedThirdPhysicalGamma e m j ≤ actualExtendedThirdEnvelope (t 0) (t 1) (t 2) := by
  have hhi : t 0 ≤ actualExtendedThirdDyadicHi m j 0 := (ht.1 0 (mem_univ _)).2
  unfold actualExtendedThirdPhysicalGamma
  split_ifs with hfull
  · have hx : t 0 ≤ mu := by linarith
    have ho : Ordered (t 0) (t 1) (t 2) := ⟨ht.2.1, ht.2.2.1, ht.2.2.2, hx⟩
    rw [actualExtendedThirdEnvelope, if_pos hx]
    exact actualExtendedThirdFullGamma_le_original ht ho
  · have hv : actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 0) ≤ v (t 0) :=
      actualExtendedThirdCellInf_le (continuous_actualExtendedThirdRobustBaseBranch 0) ht
    exact hv.trans (v_le_actualExtendedThirdEnvelope (t 0) (t 1) (t 2))

theorem actualExtendedThirdPhysicalLevel_le_ideal {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he : 0 ≤ e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    actualExtendedThirdPhysicalLevel e m j ≤ actualExtendedThirdIdealCap (t 0) (t 1) (t 2) := by
  have hg := actualExtendedThirdPhysicalGamma_le_envelope he ht
  rw [actualExtendedThirdIdealCap_eq]
  change actualExtendedThirdPhysicalLevel e m j ≤
    min thirdPrefixTheta (actualExtendedThirdEnvelope (t 0) (t 1) (t 2))
  have hl := min_le_left (thirdPrefixTheta - 2 * e) (actualExtendedThirdPhysicalGamma e m j - 2 * e)
  have hr := min_le_right (thirdPrefixTheta - 2 * e) (actualExtendedThirdPhysicalGamma e m j - 2 * e)
  unfold actualExtendedThirdPhysicalLevel thirdPrefixBufferedCap
  exact le_min (by linarith) (by linarith)

/-- The baseline is retained whichever transition branch was chosen. -/
theorem actualExtendedThirdPhysicalGamma_ge_baseline (e : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) :
    actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 0) ≤
      actualExtendedThirdPhysicalGamma e m j := by
  unfold actualExtendedThirdPhysicalGamma
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem half_le_actualExtendedThirdPhysicalGamma {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he : 0 ≤ e)
    (hj : j ∈ actualExtendedThirdRetainedCells e m) :
    (1 / 2 : ℝ) ≤ actualExtendedThirdPhysicalGamma e m j := by
  obtain ⟨hne, hstop⟩ := mem_actualExtendedThirdRetainedCells.mp hj
  apply le_trans ?_ (actualExtendedThirdPhysicalGamma_ge_baseline e m j)
  apply le_csInf (hne.image _)
  rintro _ ⟨t, ht, rfl⟩
  have hx0 : 0 ≤ t 0 := ht.2.1.trans (ht.2.2.1.trans ht.2.2.2)
  have hx : t 0 ≤ extendedFirstStop := by
    have hhi := (ht.1 0 (mem_univ _)).2
    change t 0 ≤ thirdPrefixRho
    linarith
  exact half_le_v_of_extended_range hx0 hx

/-- Uniform positive residual for the actual physical cell cap, including
all retained ordering-wall cells. This estimate is independent of z and m. -/
theorem actualExtendedThirdPhysicalLevel_tail_geometry {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he0 : 0 ≤ e) (he : e ≤ 1 / 384)
    (hj : j ∈ actualExtendedThirdRetainedCells e m)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    thirdPrefixTailMargin ≤ actualExtendedThirdPhysicalLevel e m j - t 0 - t 1 ∧
      actualExtendedThirdPhysicalLevel e m j ≤ thirdPrefixTheta - 2 * e := by
  have hstop := (mem_actualExtendedThirdRetainedCells.mp hj).2
  have hx : t 0 ≤ thirdPrefixRho := by
    have hhi := (ht.1 0 (mem_univ _)).2
    linarith
  have hy : t 1 ≤ thirdPrefixRho := ht.2.2.2.trans hx
  exact ⟨thirdPrefixBufferedCap_residual_margin he
    (half_le_actualExtendedThirdPhysicalGamma he0 hj) hx hy, thirdPrefixBufferedCap_le_root _ _⟩

end

end ImbalancedChen
