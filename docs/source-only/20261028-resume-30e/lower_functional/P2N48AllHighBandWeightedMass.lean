import ImbalancedChen.P2N48TiedMomentPrimitives
import ImbalancedChen.P2N48OriginalStrictLogMassAndOmegaPorts

/-! SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
Actual n48 row weighted mass, all four tie patterns. Closed-to-half-open
transport uses a.e. equality supported on the original null faces/diagonals,
not equality of volumes. All product factors and the distinguished z weight
are integrated against genuine Lebesgue measure. No hFubini/hZ input.
-/
namespace ImbalancedChen.P2N48AllHighBandWeightedMass
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
open ImbalancedChen.OriginalThirdTriangleMomentsSourceOnly
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48TiedParentMassReduction P2N48AllHighBandTiePatterns
open P2N48TermOneNullBoundaryTransport P2N48TermOneAllPatternClosedVolumes
open P2N48GenericTwoThreeTieVolumes P2N48TiedMomentPrimitives
open P2N48OriginalStrictLogMassAndOmegaPorts
open P2N48ActualGeometricKeyDecoder
open P5Z.U11Integral P5Z.U11Canonical

/-- Integral transport needs a.e. set equality, not merely equal volume. -/
theorem fullParent_ae_closedOrderedParent (r : SourceRow) (ht : r.term.val=1) :
    fullParent r =ᵐ[volume] closedOrderedParent r := by
  have hn : ∀ᵐ v : LogFour, v∉nullBoundary r := by
    rw [ae_iff]
    simpa only [not_not] using nullBoundary_null r
  filter_upwards [hn] with v hv
  apply propext
  exact ⟨fun h => fullParent_subset_closedOrderedParent r ht h,
    fun h => closed_without_boundary_subset_fullParent r ht ⟨h,hv⟩⟩

/-- Only the source coordinate equivalence is used. -/
theorem splitFour_symm_vector (t : ℝ) (q : Tail3) :
    splitFour.symm (t,q)=![t,q.1,q.2.1,q.2.2] := by
  apply splitFour.injective
  simp [splitFour_apply]

def rowLog (r : SourceRow) (j : Fin 4) : ℝ := Real.log (rowUpper r j/rowLower r j)

/-- The high t interval separates exactly from the true ordered low block. -/
theorem actual_mass_eq_tLog_inner (r : SourceRow) (ht : r.term.val=1) :
    parentUnweightedMass (fullParent r)=
      rowLog r 0*(∫ q in innerClosed r, tripleKernel q) := by
  let F : LogFour→ℝ := (closedOrderedParent r).indicator
    (fun v => harmonicDensity v/v 2)
  have hfactor (t : ℝ) (q : Tail3) : F (splitFour.symm (t,q))=
      (Icc (rowLower r 0) (rowUpper r 0)).indicator (fun t => 1/t) t *
        (innerClosed r).indicator tripleKernel q := by
    have hm : splitFour.symm (t,q)∈closedOrderedParent r ↔
        t∈Icc (rowLower r 0) (rowUpper r 0) ∧ q∈innerClosed r := by
      rw [←splitClosed_preimage r ht]
      simp [splitClosed]
    by_cases htI : t∈Icc (rowLower r 0) (rowUpper r 0) <;>
      by_cases hq : q∈innerClosed r <;>
      simp [F, hm, htI, hq, splitFour_symm_vector, harmonicDensity,
        tripleKernel, pow_two, one_div, div_eq_mul_inv, mul_inv_rev] <;> ring
  calc
    parentUnweightedMass (fullParent r)=
        ∫ v in closedOrderedParent r, harmonicDensity v/v 2 :=
      setIntegral_congr_set (fullParent_ae_closedOrderedParent r ht)
    _=∫ v, F v := (integral_indicator (measurableSet_closedOrderedParent r)).symm
    _=∫ p : ℝ×Tail3, F (splitFour.symm p) :=
      (splitFour_preserving.symm.integral_comp' F).symm
    _=∫ p : ℝ×Tail3,
        (Icc (rowLower r 0) (rowUpper r 0)).indicator (fun t => 1/t) p.1 *
          (innerClosed r).indicator tripleKernel p.2 := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => hfactor p.1 p.2)
    _=(∫ t in Icc (rowLower r 0) (rowUpper r 0),1/t)*
        ∫ q in innerClosed r,tripleKernel q := by
      rw [integral_prod_mul, integral_indicator measurableSet_Icc,
        integral_indicator (measurableSet_innerClosed r)]
    _=_ := by rw [reciprocal_Icc (rowLower_pos r 0) (rowLower_le_upper r 0)]; rfl

private theorem product_set_integral {X Y : Type*}
    [MeasureSpace X] [MeasureSpace Y]
    [SigmaFinite (volume : Measure X)] [SigmaFinite (volume : Measure Y)]
    (S : Set X) (T : Set Y) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (f : X→ℝ) (g : Y→ℝ) :
    (∫ p : X×Y in S×ˢT,f p.1*g p.2)=(∫ x in S,f x)*(∫ y in T,g y) := by
  calc
    _=∫ p : X×Y,S.indicator f p.1*T.indicator g p.2 := by
      rw [←integral_indicator (hS.prod hT)]
      apply integral_congr_ae
      filter_upwards [] with p
      by_cases hx : p.1∈S <;> by_cases hy : p.2∈T <;>
        simp [hx,hy]
    _=_ := by rw [integral_prod_mul,integral_indicator hS,integral_indicator hT]

/-- zw is one equal-bin block, but u occupies a separate original bin. -/
theorem actual_zw_inner_moment (r : SourceRow)
    (h12 : r.iz<r.iy) (h23 : r.iz=r.iw) :
    (∫ q in innerClosed r,tripleKernel q)=
      rowLog r 1*moment01 (rowLower r 2) (rowUpper r 2) := by
  rw [innerClosed_zw r h12 h23]
  have heq : (fun q : Tail3 => tripleKernel q)=
      (fun q => (1/q.1)*zwKernel q.2) := by
    funext q
    unfold tripleKernel zwKernel
    ring
  rw [heq,product_set_integral _ _ measurableSet_Icc (measurableSet_xyTriangle _ _),
    reciprocal_Icc (rowLower_pos r 1) (rowLower_le_upper r 1),
    zwTriangle_moment (rowLower_pos r 2) (rowLower_le_upper r 2)]
  rfl

/-- uz is one equal-bin block, with z as its second distinguished slot. -/
theorem actual_uz_inner_moment (r : SourceRow)
    (h12 : r.iy=r.iz) (h23 : r.iw<r.iz) :
    (∫ q in innerClosed r,tripleKernel q)=
      moment10 (rowLower r 1) (rowUpper r 1)*rowLog r 3 := by
  let E : XY×ℝ ≃ᵐ Tail3 := MeasurableEquiv.prodAssoc
  have hE : MeasurePreserving E volume volume := volume_preserving_prodAssoc
  let F : Tail3→ℝ := (innerClosed r).indicator tripleKernel
  have hfactor (p : XY×ℝ) : F (E p)=
      (xyTriangle (rowLower r 1) (rowUpper r 1) ×ˢ
        Icc (rowLower r 3) (rowUpper r 3)).indicator
          (fun p : XY×ℝ => uzKernel p.1*(1/p.2)) p := by
    have hm : E p∈innerClosed r ↔
        p.1∈xyTriangle (rowLower r 1) (rowUpper r 1) ∧
          p.2∈Icc (rowLower r 3) (rowUpper r 3) := by
      rw [innerClosed_uz r h12 h23]
      simp [E]
    by_cases hp : p.1∈xyTriangle (rowLower r 1) (rowUpper r 1) <;>
      by_cases hw : p.2∈Icc (rowLower r 3) (rowUpper r 3) <;>
      simp [F,hm,hp,hw,E,tripleKernel,uzKernel] <;> ring
  calc
    _=∫ q,F q := (integral_indicator (measurableSet_innerClosed r)).symm
    _=∫ p : XY×ℝ,F (E p) := (hE.integral_comp' F).symm
    _=∫ p : XY×ℝ in xyTriangle (rowLower r 1) (rowUpper r 1) ×ˢ
        Icc (rowLower r 3) (rowUpper r 3),uzKernel p.1*(1/p.2) := by
      rw [←integral_indicator ((measurableSet_xyTriangle _ _).prod measurableSet_Icc)]
      exact integral_congr_ae (Eventually.of_forall hfactor)
    _=_ := by
      rw [product_set_integral _ _ (measurableSet_xyTriangle _ _) measurableSet_Icc,
        uzTriangle_moment (rowLower_pos r 1) (rowLower_le_upper r 1),
        reciprocal_Icc (rowLower_pos r 3) (rowLower_le_upper r 3)]
      rfl

theorem actual_uzw_inner_moment (r : SourceRow)
    (h12 : r.iy=r.iz) (h23 : r.iz=r.iw) :
    (∫ q in innerClosed r,tripleKernel q)=
      moment11 (rowLower r 1) (rowUpper r 1) := by
  rw [innerClosed_uzw r h12 h23]
  exact tripleTriangle_moment (rowLower_pos r 1) (rowLower_le_upper r 1)

/-- All four ORIGINAL high-band weighted formulas; no volume shortcut. -/
def rowZFormula (r : SourceRow) : ℝ :=
  if r.iy=r.iz then
    if r.iz=r.iw then rowLog r 0*moment11 (rowLower r 1) (rowUpper r 1)
    else rowLog r 0*moment10 (rowLower r 1) (rowUpper r 1)*rowLog r 3
  else if r.iz=r.iw then
    rowLog r 0*rowLog r 1*moment01 (rowLower r 2) (rowUpper r 2)
  else strictZ r

theorem highBand_true_mass_formula (r : SourceRow) (ht : r.term.val=1)
    (hchron : r.iw≤r.iz ∧ r.iz≤r.iy) :
    parentUnweightedMass (fullParent r)=rowZFormula r := by
  by_cases h12 : r.iy=r.iz
  · by_cases h23 : r.iz=r.iw
    · rw [rowZFormula,if_pos h12,if_pos h23,actual_mass_eq_tLog_inner r ht,
        actual_uzw_inner_moment r h12 h23]
    · have hlt : r.iw<r.iz := lt_of_le_of_ne hchron.1 (Ne.symm h23)
      rw [rowZFormula,if_pos h12,if_neg h23,actual_mass_eq_tLog_inner r ht,
        actual_uz_inner_moment r h12 hlt]
      ring
  · have hlt12 : r.iz<r.iy := lt_of_le_of_ne hchron.2 (Ne.symm h12)
    by_cases h23 : r.iz=r.iw
    · rw [rowZFormula,if_neg h12,if_pos h23,actual_mass_eq_tLog_inner r ht,
        actual_zw_inner_moment r hlt12 h23]
      ring
    · have hlt23 : r.iw<r.iz := lt_of_le_of_ne hchron.1 (Ne.symm h23)
      rw [rowZFormula,if_neg h12,if_neg h23]
      exact strict_true_mass_eq_log_formula r ht hlt12 hlt23

/-- Instantiation on the exact retained seven-column archive crop. -/
theorem actual_retained_true_mass_formula (r : SourceRow) (hr : r∈actualRetainedRows) :
    parentUnweightedMass (fullParent r)=rowZFormula r := by
  have hd := decoded_of_mem_rawSelectedRows r (actualRetainedRows_policy r hr).1
  exact highBand_true_mass_formula r hd.1 ⟨hd.2.1,hd.2.2.1⟩

/-- Exact same parent required by the independent original n48 producer:
(39,47,0,0), with the signed source 1-ex-ex*L distinguished zw block. -/
theorem original_keyRow_mass (ordinal method floorQ : ℕ) :
    parentUnweightedMass (fullParent (P2N48OneActualTiedParentVolume.keyRow ordinal method floorQ))=
      Real.log ((53280 : ℝ)/52860)*Real.log ((36480 : ℝ)/36137)*
        ((240000 : ℝ)/20016)*
          (1-(20016 : ℝ)/20359-(20016 : ℝ)/20359*Real.log ((20359 : ℝ)/20016)) := by
  rw [highBand_true_mass_formula _ (by rfl) (by constructor <;> decide)]
  norm_num [rowZFormula,P2N48OneActualTiedParentVolume.keyRow,rowLog,rowLower,rowUpper,
    leftEnd,rightEnd,width,lowLo,highLo,moment01] <;> ring

end
end ImbalancedChen.P2N48AllHighBandWeightedMass
