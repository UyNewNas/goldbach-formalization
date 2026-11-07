import ImbalancedChen.P5ZU1011OriginalSourceGeometryMesh
import ImbalancedChen.P5ZU1011OriginalSixteenSnappedTable
import ImbalancedChen.P5ZU1011OriginalSixteenEligibilitySnapStability
import ImbalancedChen.P5ZU1011OriginalSwitchedOscillation

/-!
A genuine total-Ico mesh error for the ORIGINAL sixteen-policy nonlinear
minimum. The six source walls, every actual required eligibility wall,
and all31 capbranches times151 H248 knots are paid by one actual prime
thin-strip family. Off that family the ORIGINAL source geometry,
eligibility circuit, and H248 lookup are proved stable. Actual switched
and atom-frozen ordinary oscillation then supply one finite-minimum error.

For every epsilon one mesh, one strip width and one target threshold
precede EVERY moving tuple keep mask. The conclusion is the stronger
weighted sum of absolute errors. An arbitrary last-pair mask stays at
the original tuple; its value is never replaced by its mesh-corner value.
No moving-mask limit, per-policy/minimum exchange, hAgree, Lipschitz,
cell-bound, prime-wall-mass or final-mean supplier occurs.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenUniformEnvelopeMesh

open Set Filter Topology
open Classical
open U11Integral U11Canonical U11H248 U1011AdaptivePrimeError
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenOscillation
open U1011OriginalSixteenKnotPayment U1011OriginalSixteenSnappedTable
open U1011OriginalSourceGeometryMesh U1011OriginalSwitchedOscillation
open U1011H248Partition
open Part5UpperTables
open LiLiuPrereqBuchstab
open scoped BigOperators

noncomputable section

abbrev GateWall := {t : EligibilityStripVolume.StripIndex // EligibilityGridCertificates.Required t.1 t.2.1}

def gateWallForm (t : GateWall) : LogFour→L[ℝ]ℝ :=
  EligibilityGridCertificates.wall t.val.1 t.val.2.2 t.val.2.1

def gateWallBound (t : GateWall) : ℝ :=
  EligibilityGridCertificates.wallOffset t.val.1 t.val.2.2 t.val.2.1

def gateForms (i : Fin (Fintype.card GateWall)) : LogFour→L[ℝ]ℝ :=
  gateWallForm ((Fintype.equivFin GateWall).symm i)

def gateBounds (i : Fin (Fintype.card GateWall)) : ℝ :=
  gateWallBound ((Fintype.equivFin GateWall).symm i)

theorem gateForms_ne_zero (i : Fin (Fintype.card GateWall)) : gateForms i≠0 :=
  EligibilityGridCertificates.actual_wall_ne_zero _ _ _ ((Fintype.equivFin GateWall).symm i).property

theorem eligibilityUnion_subset_gateStrip (delta : ℝ) :
    EligibilityStripVolume.actualStripUnion delta ⊆primeAffineWallStrip gateForms gateBounds delta := by
  intro v hv
  obtain ⟨t,ht⟩:=Set.mem_iUnion.mp hv
  by_cases hreq : EligibilityGridCertificates.Required t.1 t.2.1
  · simp only [if_pos hreq] at ht
    rw [EligibilityStripVolume.required_strip_is_actual_wall _ _ _ hreq] at ht
    let z : GateWall := ⟨t,hreq⟩
    refine ⟨(Fintype.equivFin GateWall) z,?_⟩
    simpa only [gateForms,gateBounds,Equiv.symm_apply_apply,gateWallForm,gateWallBound,z] using ht.2
  · simp only [if_neg hreq,Set.mem_empty_iff_false] at ht
    exact ht.elim

abbrev KnotCount := Fintype.card U1011OriginalSixteenKnotPayment.Wall
abbrev GateCount := Fintype.card GateWall

def combinedForms : Fin (6+(KnotCount+GateCount))→LogFour→L[ℝ]ℝ :=
  Fin.append sourceForms (Fin.append U1011OriginalSixteenKnotPayment.wallForms gateForms)

def combinedBounds : Fin (6+(KnotCount+GateCount))→ℝ :=
  Fin.append sourceBounds (Fin.append U1011OriginalSixteenKnotPayment.wallBounds gateBounds)

theorem combinedForms_ne_zero : ∀ i,combinedForms i≠0 := by
  simp only [combinedForms,Fin.forall_fin_add,Fin.append_left,Fin.append_right]
  exact ⟨sourceForms_ne_zero,⟨U1011OriginalSixteenKnotPayment.wallForms_ne_zero,gateForms_ne_zero⟩⟩

def badStrip (delta : ℝ) : Set LogFour := primeAffineWallStrip combinedForms combinedBounds delta

theorem sourceStrip_subset_badStrip (delta : ℝ) : sourceStrip delta⊆badStrip delta := by
  rintro v ⟨i,hi⟩
  refine ⟨Fin.castAdd (KnotCount+GateCount) i,?_⟩
  simpa only [combinedForms,combinedBounds,Fin.append_left] using hi

theorem knotStrip_subset_badStrip (delta : ℝ) : knotStrip delta⊆badStrip delta := by
  rintro v ⟨i,hi⟩
  refine ⟨Fin.natAdd 6 (Fin.castAdd GateCount i),?_⟩
  simpa only [combinedForms,combinedBounds,Fin.append_left,Fin.append_right] using hi

theorem eligibilityUnion_subset_badStrip (delta : ℝ) :
    EligibilityStripVolume.actualStripUnion delta⊆badStrip delta := by
  intro v hv
  obtain ⟨i,hi⟩:=eligibilityUnion_subset_gateStrip delta hv
  refine ⟨Fin.natAdd 6 (Fin.natAdd KnotCount i),?_⟩
  simpa only [combinedForms,combinedBounds,Fin.append_right] using hi

def badMass (N : ℕ) (keep : (Fin 4→ℕ)→Prop) (delta : ℝ) : ℝ :=
  ∑ p∈(actualPrimeBoxTuples N (fun _ : Fin 4=>(417/5000:ℝ))
    (fun _=>(59/250:ℝ))).filter (fun p=>keep p ∧ actualPrimeTupleLog N p∈badStrip delta),
      ∏ i,1/((p i:ℝ)-1)

theorem badMass_nonneg (N : ℕ) (keep : (Fin 4→ℕ)→Prop) (delta : ℝ) :
    0≤badMass N keep delta := by
  apply Finset.sum_nonneg
  intro p hp
  exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

/-- The actual combined-family arithmetic reserve chooses its width
and target threshold BEFORE every moving keep mask. -/
theorem exists_uniform_badMass_reserve (eta : ℝ) (heta : 0<eta) :
    ∃ delta : ℝ,0<delta ∧ ∃ N0 : ℕ,2≤N0 ∧ ∀ N : ℕ,N0≤N →
      ∀ keep : (Fin 4→ℕ)→Prop,badMass N keep delta<eta := by
  obtain ⟨delta,hd,N0,hN0,hpay⟩:=exists_actualPrimeAffineWallStrip_mass_lt
    (by norm_num : (0:ℝ)<417/5000) (by norm_num : (417/5000:ℝ)<59/250)
    combinedForms combinedBounds combinedForms_ne_zero eta heta
  refine ⟨delta,hd,N0,hN0,?_⟩
  intro N hN keep
  apply lt_of_le_of_lt _ (hpay N hN)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp,hkeep,hs⟩:=Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp,hs⟩
  · intro p hp _
    exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

def actualSwitch : LogFour→ℝ := switchedKernel currentK buchstab

def totalEnvelope : LogFour→ℝ :=
  sourceDomain.indicator (originalEnvelope actualSwitch)

/-- The actual original total kernel is globally range bounded; its
zero extension uses only the six geometric source inequalities. -/
theorem totalEnvelope_bounds (v : LogFour) : 0≤totalEnvelope v ∧ totalEnvelope v≤1000 := by
  by_cases hv : v∈sourceDomain
  · simp only [totalEnvelope,indicator_of_mem hv]
    have he := guarded_envelope_bounds sourceDomain bank eligible actualSwitch
      (ordinaryKernel H248 residual)
      (fun v hv=>canonical_switched_nonneg ∅ currentK (by norm_num [currentK]) v hv)
      (fun j hj v hv he=>(ordinary_actual_bounds ∅ j v hv he).1) v hv
    have hs := abs_canonical_switched_le ∅ currentK v hv
    have hK : |currentK|/(417/5000:ℝ)≤1000 := by norm_num [currentK]
    exact ⟨he.1,he.2.trans ((le_abs_self _).trans (hs.trans hK))⟩
  · simp only [totalEnvelope,indicator_of_notMem hv]
    norm_num

private theorem ordinary_abs_sub_of_lookup_equal (p : Policy) (v w : LogFour)
    (hv : v∈sourceDomain) (hw : w∈sourceDomain)
    (hev : TypedEligible p v) (hew : TypedEligible p w)
    (hlookup : H248 (max 2 (typedResidual p v/v 3))=
      H248 (max 2 (typedResidual p w/w 3))) :
    |ordinaryKernel H248 residual p.val v-ordinaryKernel H248 residual p.val w|≤
      2000*l1Delta v w := by
  obtain ⟨a,ha⟩:=exists_scalarCell (typedResidual p v/v 3)
  have hvEq:=original_frozenOrdinary_eq_actual_on_cell ∅ a p v hv hev ha
  have hwClip : (417/5000:ℝ)≤typedResidual p w :=
    hw.1.trans (typedEligible_residual_gt_smallest p w hew).le
  have hr : residual p.val w=typedResidual p w := by simp only [residual,dif_pos p.isLt]
  have hwEq : ordinaryKernel H248 residual p.val w=frozenOrdinary (417/5000:ℝ) a p w := by
    unfold ordinaryKernel frozenOrdinary
    rw [hr,←hlookup,H248_eq_stateValue ha,max_eq_right hwClip]
  rw [←hvEq,hwEq]
  exact original_frozenOrdinary_abs_sub_le a p v w

/-- The existing generic min stability is instantiated with the ACTUAL
sixteen candidates. Only structural local gate/lookup equalities occur
in this private helper; both are discharged in the public theorem below. -/
private theorem envelope_abs_sub_of_stable_circuit (v w : LogFour)
    (hv : v∈sourceDomain) (hw : w∈sourceDomain)
    (helig : ∀ p : Policy,TypedEligible p v↔TypedEligible p w)
    (hlookup : ∀ p : Policy,H248 (max 2 (typedResidual p v/v 3))=
      H248 (max 2 (typedResidual p w/w 3))) :
    |originalEnvelope actualSwitch v-originalEnvelope actualSwitch w|≤10000*l1Delta v w := by
  let f := guarded eligible actualSwitch (ordinaryKernel H248 residual)
  have hs : |actualSwitch v-actualSwitch w|≤10000*l1Delta v w :=
    actual_switched_abs_sub_le ∅ v w hv hw
  have hd:=l1Delta_nonneg v w
  have h := envelope_abs_sub_le bank f (fun c _=>f c w) v (10000*l1Delta v w) (by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · simpa only [f,guarded,if_pos rfl] using hs
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hc
      have hj16 : j<16 := Finset.mem_range.mp hj
      have hequiv : eligible j v↔eligible j w := by
        simpa only [eligible,dif_pos hj16] using helig ⟨j,hj16⟩
      by_cases hev : eligible j v
      · have hew:=hequiv.mp hev
        have hev' : TypedEligible ⟨j,hj16⟩ v := by simpa only [eligible,dif_pos hj16] using hev
        have hew' : TypedEligible ⟨j,hj16⟩ w := by simpa only [eligible,dif_pos hj16] using hew
        have ho:=ordinary_abs_sub_of_lookup_equal ⟨j,hj16⟩ v w hv hw hev' hew' (hlookup ⟨j,hj16⟩)
        have hop : |ordinaryKernel H248 residual j v-ordinaryKernel H248 residual j w|≤
            10000*l1Delta v w := ho.trans (by nlinarith)
        simpa [f,guarded,hev,hew] using hop
      · have hew : ¬eligible j w := fun h=>hev (hequiv.mpr h)
        simpa [f,guarded,hev,hew] using hs)
  exact h

/-- No local equality, continuity, Lipschitz or cell-bound supplier is
requested: all stability follows from the actual proper-wall strips. -/
theorem totalEnvelope_abs_sub_off_badStrip (v w : LogFour) (delta : ℝ) (hd : 0<delta)
    (hoff : v∉badStrip delta) (hclose : l1Delta v w≤delta/12) :
    |totalEnvelope v-totalEnvelope w|≤10000*l1Delta v w := by
  have hsource : v∉sourceStrip delta := fun h=>hoff (sourceStrip_subset_badStrip delta h)
  have hknot : v∉knotStrip delta := fun h=>hoff (knotStrip_subset_badStrip delta h)
  have hgate : v∉EligibilityStripVolume.actualStripUnion delta :=
    fun h=>hoff (eligibilityUnion_subset_badStrip delta h)
  have hdom := sourceDomain_stable v w delta hd hsource (by linarith)
  by_cases hv : v∈sourceDomain
  · have hw:=hdom.mp hv
    have helig:=EligibilitySnapStability.actual_all_sixteen_eligibility_stable delta hd
      (EligibilitySnapStability.originalDomain_subset_unitCube ∅ hv) hgate hclose
    have hlookup (p : Policy) : H248 (max 2 (typedResidual p v/v 3))=
        H248 (max 2 (typedResidual p w/w 3)) :=
      H248_lookup_stable p v w delta hd
        (originalDomain_denominators_pos ∅ v hv).1 (originalDomain_denominators_pos ∅ w hw).1
        hknot (by linarith)
    simp only [totalEnvelope,indicator_of_mem hv,indicator_of_mem hw]
    exact envelope_abs_sub_of_stable_circuit v w hv hw helig hlookup
  · have hw : w∉sourceDomain := fun h=>hv (hdom.mpr h)
    simp only [totalEnvelope,indicator_of_notMem hv,indicator_of_notMem hw,sub_self,abs_zero]
    exact mul_nonneg (by norm_num) (l1Delta_nonneg v w)

/-- Strong absolute weighted error, with the moving keep mask evaluated
once on the original actual prime tuple. -/
def maskedMeshAbsoluteError (N m : ℕ) (keep : (Fin 4→ℕ)→Prop) : ℝ :=
  ∑ p∈actualPrimeBoxTuples N (fun _ : Fin 4=>(417/5000:ℝ)) (fun _=>(59/250:ℝ)),
    if keep p then (∏ i,1/((p i:ℝ)-1))*
      |totalEnvelope (actualPrimeTupleLog N p)-
        totalEnvelope (meshSnap (417/5000:ℝ) (59/250:ℝ) m (actualPrimeTupleLog N p))| else 0

theorem maskedMeshAbsoluteError_bound (N m : ℕ) (hN : 1<N)
    (keep : (Fin 4→ℕ)→Prop) (delta : ℝ) (hd : 0<delta)
    (hstep : 4*logPrimeMeshStep (417/5000:ℝ) (59/250:ℝ) m≤delta/12) :
    maskedMeshAbsoluteError N m keep≤
      40000*logPrimeMeshStep (417/5000:ℝ) (59/250:ℝ) m*
        actualPrimeBoxMass N (fun _ : Fin 4=>(417/5000:ℝ)) (fun _=>(59/250:ℝ))+
      1000*badMass N keep delta := by
  have hspos:=logPrimeMeshStep_pos (by norm_num : (417/5000:ℝ)<59/250) m
  unfold maskedMeshAbsoluteError actualPrimeBoxMass badMass
  rw [Finset.mul_sum,Finset.mul_sum,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hweight:=actualPrimeBoxWeight_nonneg hp
  have hbox:=((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).2
  obtain ⟨j,hcell⟩:=exists_logPrimeMeshCell (417/5000:ℝ) (59/250:ℝ) m hbox
  have hsnap:=meshSnap_eq_of_mem _ _ (by norm_num : (417/5000:ℝ)<59/250) m j _ hcell
  have hclose:=l1Delta_meshLo_le j hcell
  by_cases hk : keep p
  · simp only [hk,if_true,true_and]
    by_cases hb : actualPrimeTupleLog N p∈badStrip delta
    · rw [if_pos hb]
      have hv:=totalEnvelope_bounds (actualPrimeTupleLog N p)
      have hw:=totalEnvelope_bounds (meshSnap (417/5000:ℝ) (59/250:ℝ) m (actualPrimeTupleLog N p))
      have herr : |totalEnvelope (actualPrimeTupleLog N p)-
          totalEnvelope (meshSnap (417/5000:ℝ) (59/250:ℝ) m (actualPrimeTupleLog N p))|≤1000 := by
        apply abs_le.mpr
        constructor <;> linarith
      have hmul:=mul_le_mul_of_nonneg_left herr hweight
      have hnonneg:=mul_nonneg (show 0≤40000*logPrimeMeshStep (417/5000:ℝ) (59/250:ℝ) m by positivity) hweight
      nlinarith
    · rw [if_neg hb]
      have hdist : l1Delta (actualPrimeTupleLog N p)
          (meshSnap (417/5000:ℝ) (59/250:ℝ) m (actualPrimeTupleLog N p))≤delta/12 := by
        rw [hsnap]
        exact hclose.trans hstep
      have herr:=totalEnvelope_abs_sub_off_badStrip _ _ delta hd hb hdist
      have herr' : |totalEnvelope (actualPrimeTupleLog N p)-
          totalEnvelope (meshSnap (417/5000:ℝ) (59/250:ℝ) m (actualPrimeTupleLog N p))|≤
            40000*logPrimeMeshStep (417/5000:ℝ) (59/250:ℝ) m := by
        rw [hsnap] at herr ⊢
        nlinarith
      have hmul:=mul_le_mul_of_nonneg_left herr' hweight
      simpa only [mul_zero,add_zero,mul_comm] using hmul
  · simp only [hk,if_false,false_and,add_zero]
    exact mul_nonneg (by positivity) hweight

/-- ONE mesh/width/threshold before EVERY moving keep mask. This is
weighted absolute approximation, and asserts no arbitrary masked limit. -/
theorem exists_uniform_total_envelope_mesh (epsilon : ℝ) (he : 0<epsilon) :
    ∃ delta : ℝ,0<delta ∧ ∃ m N0 : ℕ,2≤N0 ∧
      ∀ N : ℕ,N0≤N → ∀ keep : (Fin 4→ℕ)→Prop,
        maskedMeshAbsoluteError N m keep<epsilon := by
  obtain ⟨delta,hd,Nwall,hNwall,hwall⟩:=exists_uniform_badMass_reserve
    (epsilon/4000) (by positivity)
  have hC : 0≤originalCubeMassBound := by
    unfold originalCubeMassBound
    positivity
  have hC1 : 0<originalCubeMassBound+1 := by positivity
  have hsmall : 0<min (delta/48) (epsilon/(80000*(originalCubeMassBound+1))) := by
    apply lt_min <;> positivity
  obtain ⟨m,hm⟩:=((tendsto_logPrimeMeshStep (417/5000:ℝ) (59/250:ℝ)).eventually
    (gt_mem_nhds hsmall)).exists
  have hmD : logPrimeMeshStep (417/5000:ℝ) (59/250:ℝ) m<delta/48 :=
    hm.trans_le (min_le_left _ _)
  have hmE : logPrimeMeshStep (417/5000:ℝ) (59/250:ℝ) m<
      epsilon/(80000*(originalCubeMassBound+1)) := hm.trans_le (min_le_right _ _)
  obtain ⟨Nmass,hNmass⟩:=eventually_atTop.mp eventually_originalCube_mass_bounded
  refine ⟨delta,hd,m,max Nwall (max Nmass 2),?_,?_⟩
  · exact (le_max_right Nmass 2).trans (le_max_right _ _)
  · intro N hN keep
    have hNW : Nwall≤N := (le_max_left _ _).trans hN
    have hNM : Nmass≤N := (le_max_left Nmass 2).trans ((le_max_right _ _).trans hN)
    have hN2 : 2≤N := (le_max_right Nmass 2).trans ((le_max_right _ _).trans hN)
    have hbad:=hwall N hNW keep
    have hmass:=hNmass N hNM
    have hstep:=logPrimeMeshStep_pos (by norm_num : (417/5000:ℝ)<59/250) m
    have herr:=maskedMeshAbsoluteError_bound N m (by omega) keep delta hd (by linarith)
    have hmul:=mul_le_mul_of_nonneg_left hmass
      (show 0≤40000*logPrimeMeshStep (417/5000:ℝ) (59/250:ℝ) m by positivity)
    have hmeshProduct : logPrimeMeshStep (417/5000:ℝ) (59/250:ℝ) m*
        (80000*(originalCubeMassBound+1))<epsilon :=
      (lt_div_iff₀ (by positivity : (0:ℝ)<80000*(originalCubeMassBound+1))).mp hmE
    have hextra : 0≤40000*logPrimeMeshStep (417/5000:ℝ) (59/250:ℝ) m := by positivity
    nlinarith

end

end ImbalancedChen.P5Z.U1011OriginalSixteenUniformEnvelopeMesh
