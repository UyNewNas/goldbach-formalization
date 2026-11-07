/-!
SOURCE ONLY / UNCOMPILED.

Exact truncation of the original complete third integral. The compact part
uses z >= h and the strict discarded part uses z < h. Their union is the
literal manuscript region, not a surrogate box. Full integrability is obtained
from the actual full gated kernel; the strict/closed tail comparison pays the
coordinate face by its proved zero volume. The error is the actual nonnegative
tail, with the explicit D(10) modulus supplied by P2CompleteThirdTailIntegral.

The sibling draft is intended for ImbalancedChen/P2CompleteThirdTailIntegral.lean
when a later authorized promotion/validation occurs. Neither draft nor the
imported source candidates has been compiled by this task.
-/
import ImbalancedChen.P2CompleteThirdTailIntegral
import ImbalancedChen.Part4ActualThirdOriginalClosedSplitAggregation

set_option Elab.async false

namespace ImbalancedChen.P2ThirdTailCertificateTruncation

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal
open P2CompleteThirdTailIntegral

abbrev Point := Fin 3 → ℝ

/-- The original complete manuscript region with all its ordering and cube gates. -/
def fullRegion : Set Point :=
  actualExtendedThirdManuscriptTailRegion 0 thirdPrefixRho

def originalKernel (t : Point) : ℝ :=
  actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2)

/-- The cutoff face belongs to the compact part. -/
def compactRegion (h : ℝ) : Set Point :=
  fullRegion ∩ {t : Point | h ≤ t 2}

/-- The omitted tail has a genuinely strict z cutoff. -/
def strictTailRegion (h : ℝ) : Set Point :=
  fullRegion ∩ {t : Point | t 2 < h}

def compactIntegral (h : ℝ) : ℝ := ∫ t in compactRegion h, originalKernel t

def strictTailIntegral (h : ℝ) : ℝ := ∫ t in strictTailRegion h, originalKernel t

theorem measurableSet_fullRegion : MeasurableSet fullRegion :=
  measurableSet_actualExtendedThirdManuscriptTailRegion 0 thirdPrefixRho

theorem measurableSet_compactRegion (h : ℝ) : MeasurableSet (compactRegion h) :=
  measurableSet_fullRegion.inter
    (isClosed_le continuous_const (continuous_apply 2)).measurableSet

theorem measurableSet_strictTailRegion (h : ℝ) : MeasurableSet (strictTailRegion h) :=
  measurableSet_fullRegion.inter
    (isOpen_lt (continuous_apply 2) continuous_const).measurableSet

/-- Genuine full integrability comes from the actual positive tail and compact
bounds already used to prove integrability of the full gated functional. -/
theorem integrableOn_originalKernel : IntegrableOn originalKernel fullRegion := by
  let A := actualExtendedThirdClosedOrderRegion thirdPrefixRho
  let g : Point → ℝ := fun t => actualExtendedThirdGatedKernel 0 (t 0) (t 1) (t 2)
  have hA : MeasurableSet A :=
    measurableSet_actualExtendedThirdClosedOrderRegion thirdPrefixRho
  have hg : IntegrableOn g A :=
    integrableOn_actualExtendedThirdGatedKernel_full (by norm_num) (by norm_num)
  have hgi : Integrable (A.indicator g) := (integrable_indicator_iff hA).2 hg
  have heq : A.indicator g =ᵐ[volume] fullRegion.indicator originalKernel :=
    Eventually.of_forall fun t =>
      (actualExtendedThirdManuscript_indicator 0 thirdPrefixRho t).symm
  exact (integrable_indicator_iff measurableSet_fullRegion).1 (hgi.congr heq)

theorem integrableOn_compactKernel (h : ℝ) :
    IntegrableOn originalKernel (compactRegion h) :=
  integrableOn_originalKernel.mono_set inter_subset_left

theorem integrableOn_strictTailKernel (h : ℝ) :
    IntegrableOn originalKernel (strictTailRegion h) :=
  integrableOn_originalKernel.mono_set inter_subset_left

/-- This partition is pointwise exact, so no null-face assertion is needed for
its additivity. The shared z=h face belongs only to the compact region. -/
theorem compact_union_strictTail (h : ℝ) :
    compactRegion h ∪ strictTailRegion h = fullRegion := by
  ext t
  constructor
  · intro ht
    rcases ht with ht | ht
    · exact ht.1
    · exact ht.1
  · intro ht
    rcases le_or_gt h (t 2) with hge | hlt
    · exact Or.inl ⟨ht, hge⟩
    · exact Or.inr ⟨ht, hlt⟩

theorem compact_disjoint_strictTail (h : ℝ) :
    Disjoint (compactRegion h) (strictTailRegion h) := by
  apply Set.disjoint_left.mpr
  intro t hc ht
  exact not_lt_of_ge hc.2 ht.2

/-- Exact compact plus strict-tail decomposition of the original full integral.
There are no assumed numerical, integrability, or endpoint hypotheses. -/
theorem fullIntegral_eq_compact_add_strictTail (h : ℝ) :
    actualExtendedThirdIdealFunctional = compactIntegral h + strictTailIntegral h := by
  change (∫ t in fullRegion, originalKernel t) = _
  rw [← compact_union_strictTail h]
  exact setIntegral_union (compact_disjoint_strictTail h)
    (measurableSet_strictTailRegion h)
    (integrableOn_compactKernel h) (integrableOn_strictTailKernel h)

/-- Closing the strict cutoff changes only the proper affine face z=h.
The full-region upper radius is preserved, rather than assumed redundant. -/
theorem strictTailRegion_ae_eq_closedTail {h : ℝ} (hsmall : h ≤ thirdPrefixRho) :
    strictTailRegion h =ᵐ[volume] actualExtendedThirdManuscriptTailRegion 0 h := by
  have hwall : volume {t : Point | t 2 = h} = 0 :=
    OriginalThirdCompactPartitionSourceOnly.coordinate_face_volume_zero 2 h
  have hne : ∀ᵐ t : Point ∂volume, t 2 ≠ h := by
    rw [ae_iff]
    simpa only [not_not] using hwall
  filter_upwards [hne] with t htne
  apply propext
  constructor
  · rintro ⟨⟨⟨hz, _hzrho, hzy, hyx, hx⟩, hcube⟩, hzh⟩
    exact ⟨⟨hz, hzh.le, hzy, hyx, hx⟩, hcube⟩
  · rintro ⟨⟨hz, hzh, hzy, hyx, hx⟩, hcube⟩
    have hlt : t 2 < h := (lt_or_eq_of_le hzh).resolve_right htne
    exact ⟨⟨⟨hz, hzh.trans hsmall, hzy, hyx, hx⟩, hcube⟩, hlt⟩

theorem strictTailIntegral_eq_closedTail {h : ℝ} (hsmall : h ≤ thirdPrefixRho) :
    strictTailIntegral h =
      ∫ t in actualExtendedThirdManuscriptTailRegion 0 h,
        actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2) := by
  exact setIntegral_congr_set (strictTailRegion_ae_eq_closedTail hsmall)

/-- The strict real tail equals the proved finite nonnegative mass. This rules
out using the exceptional toReal value of an infinite mass as an error bound. -/
theorem strictTailIntegral_eq_mass {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1 / 100) :
    strictTailIntegral h = (P2CompleteThirdTailIntegral.strictTailMass h).toReal := by
  have hrho : h ≤ thirdPrefixRho := hsmall.trans (by norm_num [thirdPrefixRho])
  have hs : h ≤ thirdPrefixTailMargin / 4 :=
    hsmall.trans (by norm_num [thirdPrefixTailMargin])
  rw [strictTailIntegral_eq_closedTail hrho,
    integral_actualExtendedThirdManuscriptKernel_eq_core (by norm_num) hs,
    P2CompleteThirdTailIntegral.strictTailMass_eq_actual]

theorem strictTailIntegral_nonneg {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1 / 100) : 0 ≤ strictTailIntegral h := by
  rw [strictTailIntegral_eq_mass hh hsmall]
  exact ENNReal.toReal_nonneg

theorem strictTailIntegral_le_cutoffEnvelope {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1 / 100) :
    strictTailIntegral h ≤ cutoffEnvelope h := by
  rw [strictTailIntegral_eq_closedTail
    (hsmall.trans (by norm_num [thirdPrefixRho]))]
  exact manuscriptIntegral_le_cutoffEnvelope hh hsmall

/-- An explicit quantitative truncation error for the SAME full integral. -/
theorem fullIntegral_sub_compact_bounds {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1 / 100) :
    0 ≤ actualExtendedThirdIdealFunctional - compactIntegral h ∧
      actualExtendedThirdIdealFunctional - compactIntegral h ≤ cutoffEnvelope h := by
  have hsplit := fullIntegral_eq_compact_add_strictTail h
  have hn := strictTailIntegral_nonneg hh hsmall
  have hb := strictTailIntegral_le_cutoffEnvelope hh hsmall
  constructor <;> linarith only [hsplit, hn, hb]

theorem abs_compactIntegral_sub_full_le {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1 / 100) :
    |compactIntegral h - actualExtendedThirdIdealFunctional| ≤ cutoffEnvelope h := by
  have hb := fullIntegral_sub_compact_bounds hh hsmall
  rw [abs_sub_comm, abs_of_nonneg hb.1]
  exact hb.2

/-- A rational compact certificate and a rational certificate for the explicit
analytic modulus combine into a certificate for the complete third integral. -/
theorem fullIntegral_le_rational_certificates {h : ℝ} (q r : ℚ)
    (hh : 0 < h) (hsmall : h ≤ 1 / 100)
    (hcompact : compactIntegral h ≤ (q : ℝ))
    (htail : cutoffEnvelope h ≤ (r : ℝ)) :
    actualExtendedThirdIdealFunctional ≤ ((q + r : ℚ) : ℝ) := by
  have hb := (fullIntegral_sub_compact_bounds hh hsmall).2
  push_cast
  linarith only [hb, hcompact, htail]

/-- Tail convergence is established through its finite nonnegative mass and
then converted to Real; no truncated-integral limit is supplied by the caller. -/
theorem strictTailIntegral_tendsto_zero :
    Tendsto strictTailIntegral (𝓝[>] 0) (𝓝 0) := by
  have hmass : Tendsto (fun h =>
      (P2CompleteThirdTailIntegral.strictTailMass h).toReal) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp
        P2CompleteThirdTailIntegral.strictTailMass_tendsto_zero
  apply hmass.congr'
  have hsmall : Iio ((1 : ℝ) / 100) ∈ 𝓝[>] (0 : ℝ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hs
  exact (strictTailIntegral_eq_mass hh hs.le).symm

/-- The actual z>=h compact truncations converge to the original complete
third functional, with the explicit error proved above at every small cutoff. -/
theorem compactIntegral_tendsto_full :
    Tendsto compactIntegral (𝓝[>] 0) (𝓝 actualExtendedThirdIdealFunctional) := by
  have hlim := (tendsto_const_nhds
    (x := actualExtendedThirdIdealFunctional)).sub strictTailIntegral_tendsto_zero
  simp only [sub_zero] at hlim
  apply hlim.congr'
  exact Eventually.of_forall fun h => by
    have hsplit := fullIntegral_eq_compact_add_strictTail h
    linarith only [hsplit]

/-- The generic compact cutoff specializes to the exact original certificate
obligation, including the original z=1/100 boundary convention. -/
theorem compactIntegral_at_original_cutoff :
    compactIntegral (1 / 100) =
      OriginalThirdFiniteReserveSourceOnly.originalCompactThirdCorrection := by
  exact OriginalThirdCompactEndpointSourceOnly.
    originalCompactThirdCorrection_eq_literal_closed_compact.symm

private theorem sum_leaf_bounds
    {cells : List (Set Point)} {upper : List ℚ}
    (h : List.Forall₂
      (fun c q => (∫ t in c, originalKernel t) ≤ (q : ℝ)) cells upper) :
    (cells.map (fun c => ∫ t in c, originalKernel t)).sum ≤
      (upper.map (fun q : ℚ => (q : ℝ))).sum := by
  induction h with
  | nil => simp
  | cons hhead _htail ih =>
      simpa only [List.map_cons, List.sum_cons] using add_le_add hhead ih

/-- Concrete finite certificate consumer at the original cutoff. Its inputs
are individual rational leaf bounds for the actual closed split tree. The
whole compact integral, full integral and tail endpoint are not hypotheses. -/
theorem fullIntegral_le_closedTree_certificate
    (tree : OriginalThirdCompactPartitionSourceOnly.ClosedCutTree)
    (upper : List ℚ)
    (hleaf : List.Forall₂
      (fun c q => (∫ t in c, originalKernel t) ≤ (q : ℝ))
      (OriginalThirdCompactPartitionSourceOnly.closedLeaves tree
        OriginalThirdCompactPartitionSourceOnly.compactRegion) upper) :
    actualExtendedThirdIdealFunctional ≤
      (upper.map (fun q : ℚ => (q : ℝ))).sum +
        OriginalThirdTailActualIdealSourceOnly.Tnew := by
  have hcompact := sum_leaf_bounds hleaf
  have hbase := OriginalThirdFiniteReserveSourceOnly.idealFunctional_le_compact_add_Tnew
  rw [OriginalThirdCompactPartitionSourceOnly.
    originalCompactThirdCorrection_eq_sum_closedLeaves tree] at hbase
  change actualExtendedThirdIdealFunctional ≤
    (upper.map (fun q : ℚ => (q : ℝ))).sum +
      (319683857488126290909150567 / 2^111 : ℝ)
  change
    ((OriginalThirdCompactPartitionSourceOnly.closedLeaves tree
      OriginalThirdCompactPartitionSourceOnly.compactRegion).map
      (fun c => ∫ t in c, originalKernel t)).sum ≤ _ at hcompact
  have hkernel : originalKernel = OriginalThirdCompactPartitionSourceOnly.compactKernel := rfl
  rw [← hkernel] at hbase
  linarith only [hbase, hcompact]

end
end ImbalancedChen.P2ThirdTailCertificateTruncation
