import ImbalancedChen.P2OriginalSixthInnerInterior
import ImbalancedChen.P4AOriginalElevenOwnCaps
import ImbalancedChen.AffinePrimeGates
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Continuous ramps live INSIDE the exact original simplex unions and their
original source-margin trims. Distance to the complement is continuous;
the separately proved null simplex frontiers make it positive almost
everywhere on the original union. No prime atom on a face is discarded.
-/
namespace ImbalancedChen.P2OriginalSixthInnerPrimeRamp
noncomputable section
open Set Filter MeasureTheory
open scoped Classical BigOperators Topology
open P2OriginalSixthMomentRow (Point)
open P2OriginalSixthLogArchive (sourceCell)
open P2OriginalSixthPullingUnion (eval originalInnerUnion)
open P2OriginalSixthPhysicalGateRows (Gate row)
open P2OriginalSixthCompactTrim (trim eval_continuous)
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)
open P4AOriginalElevenOwnCaps (comparisonTies)
open P2OriginalSixthCrossCellOwnership (comparisonKind)

def insideDistance (U : Set Point) (t : Point) : ℝ :=
  if U=univ then 1 else Metric.infDist t Uᶜ

theorem continuous_insideDistance (U : Set Point) : Continuous (insideDistance U) := by
  by_cases h : U=univ
  · simp only [insideDistance,if_pos h]; exact continuous_const
  · simp only [insideDistance,if_neg h]; exact Metric.continuous_infDist_pt _

theorem insideDistance_zero {U : Set Point} {t : Point} (ht : t∉U) : insideDistance U t=0 := by
  have hU : U≠univ := by intro he; simpa only [he,mem_univ,not_true_eq_false] using ht
  rw [insideDistance,if_neg hU]
  exact Metric.infDist_zero_of_mem ht

theorem insideDistance_pos {U : Set Point} {t : Point} (ht : t∈interior U) : 0<insideDistance U t := by
  by_cases hU : U=univ
  · simp only [insideDistance,if_pos hU]; norm_num
  · have hne : (Uᶜ).Nonempty := by
      by_contra hn
      apply hU
      apply eq_univ_of_forall
      intro x
      by_contra hx
      exact hn ⟨x,hx⟩
    rw [insideDistance,if_neg hU]
    apply (Metric.infDist_pos_iff_notMem_closure hne).mp
    rwa [closure_compl,mem_compl_iff,not_not]

def distanceRamp (r : ℕ) (i : Fin 11) (t : Point) : ℝ :=
  affinePrimeClamp (insideDistance (originalInnerUnion i) t/width r-1)
def strictRamp (r : ℕ) (i : Fin 11) (t : Point) : ℝ :=
  ∏ g : Gate, if g.strict then affinePrimeClamp (eval (row (sourceCell i) g) t/width r-1) else 1
def tieRamp (r : ℕ) (t : Point) : ℝ :=
  ∏ i : Fin 11, ∏ j : Fin 11,
    if comparisonKind (sourceCell i)=comparisonKind (sourceCell j) then 1 else
      affinePrimeClamp (|eval (P2OriginalSixthPhysicalGateRows.old (sourceCell i)-
        P2OriginalSixthPhysicalGateRows.old (sourceCell j)) t|/width r-1)
def ramp (r : ℕ) (i : Fin 11) (t : Point) : ℝ :=
  distanceRamp r i t*strictRamp r i t*tieRamp r t

theorem continuous_ramp (r : ℕ) (i : Fin 11) : Continuous (ramp r i) := by
  have hd : Continuous (distanceRamp r i) := continuous_affinePrimeClamp.comp
    (((continuous_insideDistance _).div_const _).sub continuous_const)
  have hs : Continuous (strictRamp r i) := by
    apply continuous_finsetProd
    intro g _
    cases hg : g.strict <;> simp only [hg,if_true,if_false]
    · exact continuous_const
    · exact continuous_affinePrimeClamp.comp (((eval_continuous _).div_const _).sub continuous_const)
  have ht : Continuous (tieRamp r) := by
    apply continuous_finsetProd
    intro j _
    apply continuous_finsetProd
    intro k _
    by_cases h : comparisonKind (sourceCell j)=comparisonKind (sourceCell k)
    · simp only [if_pos h]; exact continuous_const
    · simp only [if_neg h]
      exact continuous_affinePrimeClamp.comp ((((eval_continuous _).abs).div_const _).sub continuous_const)
  exact (hd.mul hs).mul ht

private theorem finite_product_bounds {ι : Type*} [Fintype ι] (f : ι→ℝ)
    (h : ∀ i,0≤f i ∧ f i≤1) : 0≤∏ i,f i ∧ (∏ i,f i)≤1 :=
  ⟨Finset.prod_nonneg (fun i _ => (h i).1),
    Finset.prod_le_one (fun i _ => (h i).1) (fun i _ => (h i).2)⟩

theorem ramp_bounds (r : ℕ) (i : Fin 11) (t : Point) : 0≤ramp r i t ∧ ramp r i t≤1 := by
  have hd := affinePrimeClamp_bounds (insideDistance (originalInnerUnion i) t/width r-1)
  have hs : 0≤strictRamp r i t ∧ strictRamp r i t≤1 := by
    apply finite_product_bounds
    intro g
    cases hg : g.strict <;> simp only [hg,if_true,if_false]
    · exact ⟨zero_le_one,le_rfl⟩
    · exact affinePrimeClamp_bounds _
  have ht : 0≤tieRamp r t ∧ tieRamp r t≤1 := by
    apply finite_product_bounds
    intro j
    apply finite_product_bounds
    intro k
    split_ifs
    · exact ⟨zero_le_one,le_rfl⟩
    · exact affinePrimeClamp_bounds _
  have hp0 := mul_nonneg hd.1 hs.1
  have hp1 : distanceRamp r i t*strictRamp r i t≤1 :=
    (mul_le_mul_of_nonneg_right hd.2 hs.1).trans (by simpa only [one_mul] using hs.2)
  exact ⟨mul_nonneg hp0 ht.1,
    (mul_le_mul_of_nonneg_right hp1 ht.1).trans (by simpa only [one_mul] using ht.2)⟩

theorem ramp_off_trim (r : ℕ) (i : Fin 11) {t : Point} (ht : t∉trim i (width r)) : ramp r i t=0 := by
  by_cases hu : t∈originalInnerUnion i
  · have hbad : ∃ g : Gate, g.strict=true ∧ eval (row (sourceCell i) g) t<width r := by
      by_contra! h
      apply ht
      refine ⟨hu,?_⟩
      intro g
      cases hg : g.strict
      · simp only [hg,if_false]
        obtain ⟨s,hs⟩ := mem_iUnion.mp hu
        exact P2OriginalSixthInnerPhysicalCell.eval_nonneg_on_original_support i s g hs
      · simp only [hg,if_true]
        exact h g hg
    obtain ⟨g,hg,hbad⟩ := hbad
    have hz : strictRamp r i t=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ g)
      rw [if_pos hg]
      apply affinePrimeClamp_eq_zero
      have hh := (div_lt_one (width_pos r)).mpr hbad
      linarith
    simp only [ramp,hz,mul_zero,zero_mul]
  · have hz : distanceRamp r i t=0 := by
      rw [distanceRamp,insideDistance_zero hu,zero_div]
      apply affinePrimeClamp_eq_zero
      norm_num
    simp only [ramp,hz,zero_mul]

theorem ramp_on_comparison_ties (r : ℕ) (i : Fin 11) {t : Point} (ht : t∈comparisonTies) : ramp r i t=0 := by
  obtain ⟨j,hj⟩ := mem_iUnion.mp ht
  obtain ⟨k,hk⟩ := mem_iUnion.mp hj
  by_cases hkind : comparisonKind (sourceCell j)=comparisonKind (sourceCell k)
  · simpa only [if_pos hkind,mem_empty_iff_false] using hk
  · simp only [if_neg hkind,mem_setOf_eq] at hk
    have hz : tieRamp r t=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      rw [if_neg hkind,hk,abs_zero,zero_div]
      apply affinePrimeClamp_eq_zero
      norm_num
    simp only [ramp,hz,mul_zero]

private theorem clamp_eventually_one {z : ℝ} (hz : 0<z) :
    ∀ᶠ r : ℕ in atTop, affinePrimeClamp (z/width r-1)=1 := by
  filter_upwards [width_tendsto.eventually (gt_mem_nhds (half_pos hz))] with r hr
  apply affinePrimeClamp_eq_one
  have hh : 2≤z/width r := (le_div_iff₀ (width_pos r)).mpr (by linarith)
  linarith

theorem ramp_eventually_one (i : Fin 11) {t : Point}
    (hu : t∈interior (originalInnerUnion i))
    (hc : Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell (sourceCell i) t)
    (ht : t∉comparisonTies) : ∀ᶠ r : ℕ in atTop, ramp r i t=1 := by
  have hd := clamp_eventually_one (insideDistance_pos hu)
  have hs : ∀ᶠ r : ℕ in atTop, strictRamp r i t=1 := by
    have hh : ∀ᶠ r : ℕ in atTop, ∀ g : Gate,
        (if g.strict then affinePrimeClamp (eval (row (sourceCell i) g) t/width r-1) else 1)=1 := by
      apply eventually_all.mpr
      intro g
      cases hg : g.strict
      · exact Eventually.of_forall (fun r => by simp only [hg,if_false])
      · have hh := (P2OriginalSixthPhysicalGateRows.physicalCell_iff_rows _ _).mp hc g
        simp only [hg,if_true] at hh ⊢
        exact clamp_eventually_one hh
    filter_upwards [hh] with r hr
    exact Finset.prod_eq_one (fun g _ => hr g)
  have htie : ∀ᶠ r : ℕ in atTop, tieRamp r t=1 := by
    have hh : ∀ᶠ r : ℕ in atTop, ∀ j k : Fin 11,
        (if comparisonKind (sourceCell j)=comparisonKind (sourceCell k) then 1 else
          affinePrimeClamp (|eval (P2OriginalSixthPhysicalGateRows.old (sourceCell j)-
            P2OriginalSixthPhysicalGateRows.old (sourceCell k)) t|/width r-1))=1 := by
      apply eventually_all.mpr
      intro j
      apply eventually_all.mpr
      intro k
      by_cases hkind : comparisonKind (sourceCell j)=comparisonKind (sourceCell k)
      · exact Eventually.of_forall (fun r => by rw [if_pos hkind])
      · simp only [if_neg hkind]
        have he : eval (P2OriginalSixthPhysicalGateRows.old (sourceCell j)-
            P2OriginalSixthPhysicalGateRows.old (sourceCell k)) t≠0 := by
          intro he
          apply ht
          exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨k,by simp only [if_neg hkind,mem_setOf_eq]; exact he⟩⟩
        exact clamp_eventually_one (abs_pos.mpr he)
    filter_upwards [hh] with r hr
    exact Finset.prod_eq_one (fun j _ => Finset.prod_eq_one (fun k _ => hr j k))
  filter_upwards [hd,hs,htie] with r hrD hrS hrT
  simp only [ramp,distanceRamp,hrD,hrS,hrT,one_mul]

end
end ImbalancedChen.P2OriginalSixthInnerPrimeRamp
