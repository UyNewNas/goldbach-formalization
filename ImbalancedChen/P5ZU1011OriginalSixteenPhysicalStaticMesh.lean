import ImbalancedChen.P5ZU1011OriginalSixteenPhysicalStaticProfiles

/-!
Uniform ACTUAL harmonic positive-error comparison of the STATIC physical
original16 cell compiler with the original U11 nonlinear envelope.
Ordinary policy tags are fixed by rational corner scores before N/tuples;
ordinary costs use the actual fixed near-cap Rphys/Zexp box profile.

The error is paid by the proved static endpoint L1 error, the actual H248
lookup jump strip, and the named actual-prime physical-buffer reserve.
Its BufferSup premise is discharged by actual fixed mesh geometry.
No hApprox, native-density=H248, source count, AP estimate or arbitrary
moving-mask limit is claimed. SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenPhysicalStaticMesh

open Set Filter Topology
open Classical
open U11Integral U11Canonical U11H248 U1011AdaptivePrimeError
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSourceGeometryMesh U1011OriginalSixteenUniformEnvelopeMesh
open U1011OriginalSixteenStaticCellWinner U1011OriginalSixteenStaticCellMesh
open U1011OriginalSixteenPhysicalStaticProfiles U1011OriginalSixteenSnappedTable
open U1011OriginalSixteenKnotPayment U1011OriginalSixteenOscillation
open U1011OriginalSwitchedOscillation U1011OriginalFifteenNativeGridCells
open BufferedPrimeErrorPayment BufferedOrdinaryClamp
open Part5UpperTables
open scoped BigOperators

noncomputable section

def pointPolicyExcess (m : ℕ) (p : Policy) (v : LogFour) : ℝ :=
  if v∈sourceDomain ∧ TypedEligible p v then
    max 0 (physicalCost (typedResidual p v) (v 3) (tauMap m p v) (xiMap m p v) (rhoMap m p v)-
      originalCost (typedResidual p v) (v 3)) else 0

def pointSum (m : ℕ) (v : LogFour) : ℝ := ∑ p : Policy,pointPolicyExcess m p v

theorem pointPolicyExcess_nonneg (m : ℕ) (p : Policy) (v : LogFour) : 0≤pointPolicyExcess m p v := by
  unfold pointPolicyExcess
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem pointSum_nonneg (m : ℕ) (v : LogFour) : 0≤pointSum m v :=
  Finset.sum_nonneg (fun p _=>pointPolicyExcess_nonneg m p v)

private theorem selected_excess_le_pointSum (m : ℕ) (p : Policy) (v : LogFour)
    (hvCube : v∈cube) (hv : v∈sourceDomain)
    (hcorner : corner (gridBox m (owner m v))∈sourceDomain)
    (htag : chosenTag (gridBox m (owner m v))=p.val.succ) :
    max 0 (U1011OriginalSixteenNearCapBoxProfiles.nativeCost p (gridBox m (owner m v)) (precision m)-
      originalCost (typedResidual p v) (v 3))≤pointSum m v := by
  have hvbox:=cell_subset_closed_box m (owner m v) (owner_mem m hvCube)
  have he:=chosen_ordinary_admissible _ p htag v hvbox
  have hnative:=selected_nativeCost_eq_buffered m p v hvCube hv hcorner htag
  have hterm : pointPolicyExcess m p v=
      max 0 (U1011OriginalSixteenNearCapBoxProfiles.nativeCost p (gridBox m (owner m v)) (precision m)-
        originalCost (typedResidual p v) (v 3)) := by
    unfold pointPolicyExcess
    rw [if_pos ⟨hv,he⟩,←hnative]
  rw [←hterm]
  exact Finset.single_le_sum (fun q _=>pointPolicyExcess_nonneg m q v) (Finset.mem_univ p)

private theorem selected_table_jump (m : ℕ) (p : Policy) (v : LogFour)
    (hvCube : v∈cube) (hv : v∈sourceDomain)
    (hcorner : corner (gridBox m (owner m v))∈sourceDomain)
    (htag : chosenTag (gridBox m (owner m v))=p.val.succ)
    (delta : ℝ) (hd : 0<delta) (hstep : 48*gridStep m≤delta) :
    |originalCost (typedResidual p v) (v 3)-staticKernel (gridBox m (owner m v)) v|≤
      (badStrip delta).indicator (fun _=>1000) v := by
  let B:=gridBox m (owner m v)
  have hvcell:=owner_mem m hvCube
  have hvbox:=cell_subset_closed_box m (owner m v) hvcell
  have he:=chosen_ordinary_admissible B p htag v hvbox
  by_cases hb : v∈badStrip delta
  · rw [indicator_of_mem hb]
    have he' : eligible p.val v := by simpa only [eligible,dif_pos p.isLt] using he
    have ho:=ordinary_actual_bounds ∅ p.val v hv he'
    have hs:=staticKernel_bounds B (originalDomain_subset_compactBox ∅ hv)
    rw [U1011OriginalSixteenNearCapBoxProfiles.originalCost_eq_actualOrdinary]
    apply abs_le.mpr
    constructor <;> norm_num at ho <;> linarith
  · rw [indicator_of_notMem hb]
    have hclose : l1Delta v (corner B)≤delta/8 := by
      rw [corner_gridBox]
      have hdist : l1Delta v (logPrimeMeshLo (lower:ℝ) (upper:ℝ) m (owner m v))≤4*gridStep m :=
        l1Delta_meshLo_le (owner m v) hvcell
      linarith
    have hknot : v∉knotStrip delta:=fun h=>hb (knotStrip_subset_badStrip delta h)
    have hlookup:=H248_lookup_stable p v (corner B) delta hd
      (originalDomain_denominators_pos ∅ v hv).1
      (originalDomain_denominators_pos ∅ (corner B) hcorner).1 hknot hclose
    have hclip : (417/5000:ℝ)≤typedResidual p v :=
      hv.1.trans (typedEligible_residual_gt_smallest p v he).le
    have heq : originalCost (typedResidual p v) (v 3)=staticKernel B v := by
      rw [staticKernel_eq_frozenOrdinary B p htag v]
      unfold originalCost frozenOrdinary
      rw [max_eq_right hclip,←cornerAtom_lookup B p,hlookup]
    simp only [heq,sub_self,abs_zero,le_refl]

/-- Pointwise comparison on the actual cube. The policy can change only
with the precompiled cell; scores are never recomputed at this point. -/
theorem physical_compiler_point_error (m : ℕ) (v : LogFour) (hvCube : v∈cube)
    (delta : ℝ) (hd : 0<delta) (hstep : 48*gridStep m≤delta) :
    max 0 (physicalCompiledKernel m v-totalEnvelope v)≤pointSum m v+
      (badStrip delta).indicator (fun _=>1000) v+|totalEnvelope v-compiledKernel m v| := by
  have hsum:=pointSum_nonneg m v
  have hind : 0≤(badStrip delta).indicator (fun _=>1000) v := by
    by_cases hb : v∈badStrip delta
    · rw [indicator_of_mem hb];norm_num
    · simp only [indicator_of_notMem hb,le_refl]
  have habs:=abs_nonneg (totalEnvelope v-compiledKernel m v)
  by_cases hv : v∈sourceDomain
  · let B:=gridBox m (owner m v)
    by_cases hcorner : corner B∈sourceDomain
    · have hstatic : compiledKernel m v=staticKernel B v := by
        simp only [compiledKernel,cellKernel,if_pos hcorner]
      cases htag : chosenTag B with
      | zero =>
        have hphysical : physicalCompiledKernel m v=actualSwitch v := by
          simp only [physicalCompiledKernel,indicator_of_mem hv]
          exact physicalCellKernel_eq_fallback m (owner m v) v hcorner htag
        have hstatic' : compiledKernel m v=actualSwitch v := by
          rw [hstatic,staticKernel_eq_fallback B htag v]
          exact extendedSwitched_eq_actual ∅ v hv
        rw [hphysical]
        apply max_le (by linarith)
        have hle:=le_abs_self (actualSwitch v-totalEnvelope v)
        rw [abs_sub_comm (actualSwitch v) (totalEnvelope v),←hstatic'] at hle
        linarith
      | succ j =>
        obtain ⟨hj,ht⟩:=chosen_successor_data B j htag
        let p : Policy:=⟨j,hj⟩
        have hphysical : physicalCompiledKernel m v=
            U1011OriginalSixteenNearCapBoxProfiles.nativeCost p B (precision m) := by
          simp only [physicalCompiledKernel,indicator_of_mem hv]
          exact physicalCellKernel_eq_nativeCost m (owner m v) p v hcorner htag
        have hP:=selected_excess_le_pointSum m p v hvCube hv hcorner htag
        have hT:=selected_table_jump m p v hvCube hv hcorner htag delta hd hstep
        rw [hphysical]
        apply max_le (by linarith)
        have hn:=le_max_right (0:ℝ)
          (U1011OriginalSixteenNearCapBoxProfiles.nativeCost p B (precision m)-originalCost (typedResidual p v) (v 3))
        have htgt:=(le_abs_self (originalCost (typedResidual p v) (v 3)-staticKernel B v)).trans hT
        have hlast : staticKernel B v-totalEnvelope v≤|totalEnvelope v-compiledKernel m v| := by
          rw [←hstatic]
          simpa only [abs_sub_comm] using le_abs_self (compiledKernel m v-totalEnvelope v)
        linarith
    · have hphysical : physicalCompiledKernel m v=0 := by
        simp only [physicalCompiledKernel,indicator_of_mem hv,physicalCellKernel,if_neg hcorner]
      have hF:=(totalEnvelope_bounds v).1
      rw [hphysical,max_eq_left (by linarith)]
      linarith
  · have hphysical : physicalCompiledKernel m v=0:=indicator_of_notMem hv _
    have hF : totalEnvelope v=0:=indicator_of_notMem hv _
    rw [hphysical,hF,sub_self,max_self]
    linarith

def pointSumMass (N m : ℕ) (keep : Tuple→Prop) : ℝ := ∑ t∈tuples N,
  if keep t then weight t*pointSum m (actualPrimeTupleLog N t) else 0

def policySum (N m : ℕ) (keep : Tuple→Prop) : ℝ := ∑ p : Policy,
  policyError N ∅ keep (tupleTau N m) (tupleXi N m) (tupleRho N m) p

theorem policySum_eq_pointSumMass (N m : ℕ) (keep : Tuple→Prop) :
    policySum N m keep=pointSumMass N m keep := by
  unfold policySum policyError pointSumMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hk : keep t
  · simp only [hk,true_and,if_true]
    rw [pointSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases ha : actualPrimeTupleLog N t∈sourceDomain ∧ TypedEligible p (actualPrimeTupleLog N t)
    · have ha' : actualPrimeTupleLog N t∈originalDomain ∅ ∧ TypedEligible p (actualPrimeTupleLog N t):=ha
      simp only [pointPolicyExcess,if_pos ha,if_pos ha',tupleTau,tupleXi,tupleRho]
    · have ha' : ¬(actualPrimeTupleLog N t∈originalDomain ∅ ∧ TypedEligible p (actualPrimeTupleLog N t)):=ha
      simp only [pointPolicyExcess,if_neg ha,if_neg ha',tupleTau,tupleXi,tupleRho,mul_zero]
  · simp only [hk,false_and,if_false,Finset.sum_const_zero]

theorem policySum_le_totalError (N m : ℕ) (keep : Tuple→Prop) :
    policySum N m keep≤totalError N ∅ keep (tupleTau N m) (tupleXi N m) (tupleRho N m) := by
  have henv : 0≤envelopeError N ∅ keep (tupleTau N m) (tupleXi N m) (tupleRho N m) := by
    unfold envelopeError
    apply Finset.sum_nonneg
    intro t ht
    split_ifs
    · exact mul_nonneg (actualPrimeBoxWeight_nonneg ht) (le_max_left _ _)
    · exact le_rfl
  unfold policySum totalError
  linarith

def maskedPhysicalStaticError (N m : ℕ) (keep : Tuple→Prop) : ℝ := ∑ t∈tuples N,
  if keep t then weight t*max 0 (physicalCompiledKernel m (actualPrimeTupleLog N t)-
    totalEnvelope (actualPrimeTupleLog N t)) else 0

/-- Real selected native error is paid by actual policy errors plus the
proved endpoint compiler error and the actual table-jump strip. -/
theorem maskedPhysicalStaticError_bound (N m : ℕ) (hN : 1<N) (keep : Tuple→Prop)
    (delta : ℝ) (hd : 0<delta) (hstep : 48*gridStep m≤delta) :
    maskedPhysicalStaticError N m keep≤policySum N m keep+
      1000*badMass N keep delta+maskedStaticAbsoluteError N m keep := by
  rw [policySum_eq_pointSumMass]
  unfold maskedPhysicalStaticError pointSumMass badMass maskedStaticAbsoluteError
  rw [Finset.mul_sum,Finset.sum_filter,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  have hw:=actualPrimeBoxWeight_nonneg ht
  have hbox:=((mem_actualPrimeBoxTuples_log_iff hN _ _ t).mp ht).2
  have hvCube : actualPrimeTupleLog N t∈cube:=by simpa [cube,lower,upper] using hbox
  by_cases hk : keep t
  · simp only [hk,true_and,if_true]
    have hpoint:=physical_compiler_point_error m (actualPrimeTupleLog N t) hvCube delta hd hstep
    have hmul:=mul_le_mul_of_nonneg_left hpoint hw
    by_cases hb : actualPrimeTupleLog N t∈badStrip delta
    · rw [if_pos hb]
      rw [indicator_of_mem hb] at hmul
      simp only [weight] at hmul ⊢
      nlinarith
    · rw [if_neg hb]
      rw [indicator_of_notMem hb] at hmul
      simp only [weight] at hmul ⊢
      nlinarith
  · simp only [hk,false_and,if_false,add_zero]
    exact le_rfl

/-- ONE finite STATIC native Rphys/Zexp policy table before N/tuples and
EVERY moving keep mask. The conclusion is positive-error only, on U11. -/
theorem exists_uniform_physical_static_compiler (epsilon : ℝ) (he : 0<epsilon) :
    ∃ delta : ℝ,0<delta ∧ ∃ m N0 : ℕ,2≤N0 ∧ ∀ N : ℕ,N0≤N →
      ∀ keep : Tuple→Prop,maskedPhysicalStaticError N m keep<epsilon := by
  obtain ⟨dPhys,hdPhys,beta,hbeta,Nphys,hNphys,hphys⟩:=
    BufferedPrimeReserve.exists_uniform_physical_prime_reserve (epsilon/4) (by positivity)
  obtain ⟨delta,hd,Nwall,hNwall,hwall⟩:=exists_uniform_badMass_reserve
    (epsilon/16000) (by positivity)
  have hC : 0≤originalCubeMassBound:=by unfold originalCubeMassBound;positivity
  have hC1 : 0<originalCubeMassBound+1:=by positivity
  have hsmall : 0<min (delta/48) (min (beta/12) (epsilon/(320000*(originalCubeMassBound+1)))) := by
    apply lt_min
    · positivity
    · apply lt_min <;> positivity
  obtain ⟨m,hm⟩:=((tendsto_logPrimeMeshStep (lower:ℝ) (upper:ℝ)).eventually
    (gt_mem_nhds hsmall)).exists
  have hmD : gridStep m<delta/48:=hm.trans_le (min_le_left _ _)
  have hmB : gridStep m<beta/12:=hm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hmE : gridStep m<epsilon/(320000*(originalCubeMassBound+1)):=
    hm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Nmass,hNmass⟩:=eventually_atTop.mp eventually_originalCube_mass_bounded
  let N0:=max Nwall (max Nphys (max Nmass 2))
  refine ⟨delta,hd,m,N0,?_,?_⟩
  · exact (le_max_right Nmass 2).trans ((le_max_right Nphys _).trans (le_max_right Nwall _))
  · intro N hN keep
    have hNW : Nwall≤N:=(le_max_left _ _).trans hN
    have hNP : Nphys≤N:=(le_max_left _ _).trans ((le_max_right _ _).trans hN)
    have hNM : Nmass≤N:=(le_max_left Nmass 2).trans ((le_max_right Nphys _).trans ((le_max_right Nwall _).trans hN))
    have hN2 : 2≤N:=(le_max_right Nmass 2).trans ((le_max_right Nphys _).trans ((le_max_right Nwall _).trans hN))
    have hSup:=actual_BufferSup N m (by omega) beta (by linarith)
    have hP:=(hphys N hNP ∅ keep (tupleTau N m) (tupleXi N m) (tupleRho N m) hSup).1
    have hPolicy:=(policySum_le_totalError N m keep).trans_lt hP
    have hbad:=hwall N hNW keep
    have hmass:=hNmass N hNM
    have hspos : 0<gridStep m:=logPrimeMeshStep_pos (by norm_num [lower,upper]) m
    have hStatic:=maskedStaticAbsoluteError_bound N m (by omega) keep delta hd (by linarith)
    have hError:=maskedPhysicalStaticError_bound N m (by omega) keep delta hd (by linarith)
    have hmul:=mul_le_mul_of_nonneg_left hmass (show 0≤80000*gridStep m by positivity)
    have hmeshProduct : gridStep m*(320000*(originalCubeMassBound+1))<epsilon:=
      (lt_div_iff₀ (by positivity : (0:ℝ)<320000*(originalCubeMassBound+1))).mp hmE
    have hextra : 0≤80000*gridStep m:=by positivity
    nlinarith

end

end ImbalancedChen.P5Z.U1011OriginalSixteenPhysicalStaticMesh
