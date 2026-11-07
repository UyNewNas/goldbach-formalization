import ImbalancedChen.P5ZU1011OriginalSixteenStaticCellWinner
import ImbalancedChen.P5ZU1011OriginalSixteenSeparateGridCoverage
import ImbalancedChen.P5ZU1011OriginalSixteenUniformEnvelopeMesh

/-!
The original16 STATIC cell-corner policy compiler has genuine uniform
actual-prime L1 approximation error. All cell tags and H248 atoms are
chosen from rational boxes before N or any arithmetic tuple. Only the
actual whole-box Boolean test admits an ordinary policy. The geometric
Ico owner chooses which already compiled cell applies to a tuple.

Every moving keep mask remains at the original tuple. No policy score is
recomputed there. The proof uses real all16 separate-test coverage, actual
proper-wall payment, actual kernel oscillation and actual Mertens mass.
No hApprox, hCellBound, policy mean, count, AP or H248 analytic licence is
a premise. SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenStaticCellMesh

open Set Filter Topology
open Classical
open U11Integral U11Canonical U11H248 U1011AdaptivePrimeError
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenPolicyBank.EligibilityGridCertificates
open U1011OriginalSixteenOscillation U1011OriginalSwitchedOscillation
open U1011OriginalSourceGeometryMesh U1011OriginalSixteenKnotPayment
open U1011OriginalSixteenUniformEnvelopeMesh U1011OriginalSixteenStaticCellWinner
open U1011OriginalSixteenSeparateGridCoverage U1011OriginalFifteenNativeGridCells
open Part5UpperTables LiLiuPrereqBuchstab
open scoped BigOperators

noncomputable section

def cellTag (m : ℕ) (j : Grid m) : ℕ := chosenTag (gridBox m j)

def cellKernel (m : ℕ) (j : Grid m) (v : LogFour) : ℝ :=
  if corner (gridBox m j)∈sourceDomain then staticKernel (gridBox m j) v else 0

def compiledKernel (m : ℕ) (v : LogFour) : ℝ := cellKernel m (owner m v) v

def gridStep (m : ℕ) : ℝ := logPrimeMeshStep (lower:ℝ) (upper:ℝ) m

theorem corner_gridBox (m : ℕ) (j : Grid m) :
    corner (gridBox m j)=logPrimeMeshLo (lower:ℝ) (upper:ℝ) m j := by
  funext i
  exact cast_grid_lo m j i

theorem cellTag_ordinary_admissible (m : ℕ) (j : Grid m) (p : Policy)
    (htag : cellTag m j=p.val.succ) :
    ∀ v∈(gridBox m j).region,TypedEligible p v :=
  chosen_ordinary_admissible (gridBox m j) p htag

/-- Global ranges on the actual compact coordinate box, including corners
outside ordered source geometry. The fallback is the genuine max-two extension. -/
theorem extendedSwitched_bounds {v : LogFour} (hv : v∈compactBox) :
    0≤extendedSwitched v ∧ extendedSwitched v≤1000 := by
  have hz : 0<v 2 := (show (0:ℝ)<417/5000 by norm_num).trans_le (hv.1 2)
  have harg : (1:ℝ)≤max 2 (argument v) := by linarith [le_max_left (2:ℝ) (argument v)]
  have hb0:=buchstab_nonneg harg
  have hb1:=buchstab_le_one harg
  have hK0 : 0≤currentK := by norm_num [currentK]
  have hK7 : currentK≤7 := by norm_num [currentK]
  unfold extendedSwitched
  constructor
  · exact div_nonneg (mul_nonneg hK0 hb0) hz.le
  · apply (div_le_iff₀ hz).2
    have hnum:=mul_le_mul_of_nonneg_left hb1 hK0
    have hlo:=hv.1 2
    nlinarith

theorem frozenOrdinary_bounds (a : U1011H248Partition.AtomState) (p : Policy) (v : LogFour) :
    0≤frozenOrdinary (417/5000:ℝ) a p v ∧ frozenOrdinary (417/5000:ℝ) a p v≤1000 := by
  have hb:=stateValue_bounds a
  have hden : (417/5000:ℝ)≤max (417/5000:ℝ) (typedResidual p v):=le_max_left _ _
  have hp : 0<max (417/5000:ℝ) (typedResidual p v) :=
    (show (0:ℝ)<417/5000 by norm_num).trans_le hden
  unfold frozenOrdinary
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hb.2)) hp.le
  · apply (div_le_iff₀ hp).2
    nlinarith [hb.1]

theorem staticKernel_bounds (B : Box) {v : LogFour} (hv : v∈compactBox) :
    0≤staticKernel B v ∧ staticKernel B v≤1000 := by
  cases htag : chosenTag B with
  | zero =>
    rw [staticKernel_eq_fallback B htag v]
    exact extendedSwitched_bounds hv
  | succ j =>
    obtain ⟨hj,ht⟩:=chosen_successor_data B j htag
    let p : Policy:=⟨j,hj⟩
    rw [staticKernel_eq_frozenOrdinary B p htag v]
    exact frozenOrdinary_bounds (cornerAtom B p) p v

theorem compiledKernel_bounds (m : ℕ) {v : LogFour} (hv : v∈compactBox) :
    0≤compiledKernel m v ∧ compiledKernel m v≤1000 := by
  unfold compiledKernel cellKernel
  split_ifs
  · exact staticKernel_bounds _ hv
  · norm_num

private theorem certificate_matches_corner (m : ℕ) (j : Grid m) (v : LogFour)
    (hvcell : v∈cell m j) (hv : v∈sourceDomain)
    (hw : corner (gridBox m j)∈sourceDomain) (delta : ℝ) (hd : 0<delta)
    (hoff : v∉badStrip delta) (hstep : 48*gridStep m≤delta) :
    ∀ p : Policy,wholeBoxEligibleTest p (gridBox m j)=true ↔
      TypedEligible p (corner (gridBox m j)) := by
  have hvbox:=cell_subset_closed_box m j hvcell
  have hwbox:=corner_mem_region (gridBox m j) (gridBox_valid m j)
  have hwidth:=U1011OriginalFifteenSeparateGridCoverage.grid_width m j
  have hgate : v∉EligibilityStripVolume.actualStripUnion delta :=
    fun h=>hoff (eligibilityUnion_subset_badStrip delta h)
  have hdist : l1Delta v (corner (gridBox m j))≤delta/12 := by
    rw [corner_gridBox]
    have hclose:=l1Delta_meshLo_le j hvcell
    dsimp [gridStep] at hstep
    linarith
  have helig:=EligibilitySnapStability.actual_all_sixteen_eligibility_stable delta hd
    (EligibilitySnapStability.originalDomain_subset_unitCube ∅ hv) hgate hdist
  intro p
  constructor
  · intro ht
    exact wholeBoxEligibleTest_sound p _ ht _ hwbox
  · intro hew
    have hev:=(helig p).mpr hew
    apply all_sixteen_wholeBoxTest_of_large_actual_margins p _ (gridStep m) hvbox hwidth
    intro g hg left
    have hpos:=(typedEligible_iff_positive_margins p v).mp hev g hg left
    have hsep:=EligibilitySnapStability.actual_margin_separated delta
      (EligibilitySnapStability.originalDomain_subset_unitCube ∅ hv) hgate p left g hg
    rw [abs_of_pos hpos] at hsep
    exact hstep.trans_lt hsep

private theorem static_corner_eq_actual (B : Box) (hw : corner B∈sourceDomain)
    (hcert : ∀ p : Policy,wholeBoxEligibleTest p B=true ↔ TypedEligible p (corner B)) :
    staticKernel B (corner B)=totalEnvelope (corner B) := by
  let w:=corner B
  have hext : extendedSwitched w=actualSwitch w := extendedSwitched_eq_actual ∅ w hw
  have hcandidate (c : ℕ) (hc : c∈tags bank) :
      candidateKernel B c w=guarded eligible actualSwitch (ordinaryKernel H248 residual) c w := by
    rcases Finset.mem_insert.mp hc with rfl | hc
    · simpa only [candidateKernel,guarded,if_pos rfl] using hext
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hc
      have hj16 : j<16:=Finset.mem_range.mp hj
      let p : Policy:=⟨j,hj16⟩
      by_cases ht : wholeBoxEligibleTest p B=true
      · have hew:=(hcert p).mp ht
        have he : eligible j w := by simpa only [eligible,dif_pos hj16] using hew
        have hclip : (417/5000:ℝ)≤typedResidual p w :=
          hw.1.trans (typedEligible_residual_gt_smallest p w hew).le
        have hr : residual j w=typedResidual p w := by simp only [residual,dif_pos hj16]
        have hscore : ordinary B j w=ordinaryKernel H248 residual j w := by
          have hordinary:=ordinary_corner B p
          change ordinary B j (corner B)=_ at hordinary
          rw [max_eq_right hclip] at hordinary
          simpa only [ordinaryKernel,hr,w] using hordinary
        simpa [candidateKernel,guarded,certified,hj16,ht,he,hscore] using hscore
      · have hew : ¬TypedEligible p w:=fun h=>ht ((hcert p).mpr h)
        have he : ¬eligible j w := by simpa only [eligible,dif_pos hj16] using hew
        simpa [candidateKernel,guarded,certified,hj16,ht,he] using hext
  have h := envelope_abs_sub_le bank (candidateKernel B)
    (guarded eligible actualSwitch (ordinaryKernel H248 residual)) w 0 (fun c hc=>by
      rw [hcandidate c hc]
      simp)
  have heq:=sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  simp only [totalEnvelope,indicator_of_mem hw]
  rw [staticKernel_corner_eq_minimum]
  exact heq

private theorem compact_of_cube {v : LogFour} (hv : v∈cube) : v∈compactBox := by
  have h:=mem_logPrimeBox.mp hv
  constructor <;> intro i
  · simpa [lower] using (h i).1
  · have hu: v i≤(upper:ℝ):=(h i).2.le
    simpa [upper] using hu

/-- Static policy/kernel selected before N approximates the actual
nonlinear bank on a whole good cell. Scores are never re-read at v. -/
theorem static_cell_error_off_badStrip (m : ℕ) (j : Grid m) (v : LogFour)
    (hvcell : v∈cell m j) (delta : ℝ) (hd : 0<delta)
    (hoff : v∉badStrip delta) (hstep : 48*gridStep m≤delta) :
    |totalEnvelope v-cellKernel m j v|≤80000*gridStep m := by
  let B:=gridBox m j
  let w:=corner B
  have hvCube : v∈cube:=logPrimeMeshCell_subset_box (by norm_num [lower,upper]) m j hvcell
  have hvCompact:=compact_of_cube hvCube
  have hwCompact : w∈compactBox := by
    rw [show w=logPrimeMeshLo (lower:ℝ) (upper:ℝ) m j by exact corner_gridBox m j]
    simpa [lower,upper] using meshLo_mem_compact m j
  have hdist : l1Delta v w≤4*gridStep m := by
    rw [show w=logPrimeMeshLo (lower:ℝ) (upper:ℝ) m j by exact corner_gridBox m j]
    exact l1Delta_meshLo_le j hvcell
  have hdistD : l1Delta v w≤delta/12 := by linarith
  have hsource : v∉sourceStrip delta:=fun h=>hoff (sourceStrip_subset_badStrip delta h)
  have hdom:=sourceDomain_stable v w delta hd hsource (by linarith)
  have hspos : 0<gridStep m:=logPrimeMeshStep_pos (by norm_num [lower,upper]) m
  by_cases hv : v∈sourceDomain
  · have hw:=hdom.mp hv
    have hcert:=certificate_matches_corner m j v hvcell hv hw delta hd hoff hstep
    have hcorner:=static_corner_eq_actual B hw hcert
    have hF:=totalEnvelope_abs_sub_off_badStrip v w delta hd hoff hdistD
    have hS:=staticKernel_abs_sub_le B v w hvCompact hwCompact
    have heq : totalEnvelope v-cellKernel m j v=
        (totalEnvelope v-totalEnvelope w)+(staticKernel B w-staticKernel B v) := by
      simp only [cellKernel,if_pos hw]
      rw [hcorner]
      ring
    rw [heq]
    have htri:=abs_add_le (totalEnvelope v-totalEnvelope w) (staticKernel B w-staticKernel B v)
    rw [abs_sub_comm (staticKernel B w) (staticKernel B v)] at htri
    nlinarith
  · have hw : w∉sourceDomain:=fun h=>hv (hdom.mpr h)
    simp only [totalEnvelope,indicator_of_notMem hv,cellKernel,if_neg hw,sub_self,abs_zero]
    positivity

/-- Strong actual-prime L1 error of the complete STATIC compiler. -/
def maskedStaticAbsoluteError (N m : ℕ) (keep : (Fin 4→ℕ)→Prop) : ℝ :=
  ∑ p∈actualPrimeBoxTuples N (fun _ : Fin 4=>(417/5000:ℝ)) (fun _=>(59/250:ℝ)),
    if keep p then (∏ i,1/((p i:ℝ)-1))*
      |totalEnvelope (actualPrimeTupleLog N p)-compiledKernel m (actualPrimeTupleLog N p)| else 0

theorem maskedStaticAbsoluteError_bound (N m : ℕ) (hN : 1<N)
    (keep : (Fin 4→ℕ)→Prop) (delta : ℝ) (hd : 0<delta) (hstep : 48*gridStep m≤delta) :
    maskedStaticAbsoluteError N m keep≤80000*gridStep m*
      actualPrimeBoxMass N (fun _ : Fin 4=>(417/5000:ℝ)) (fun _=>(59/250:ℝ))+
        1000*badMass N keep delta := by
  have hspos : 0<gridStep m:=logPrimeMeshStep_pos (by norm_num [lower,upper]) m
  unfold maskedStaticAbsoluteError actualPrimeBoxMass badMass
  rw [Finset.mul_sum,Finset.mul_sum,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hweight:=actualPrimeBoxWeight_nonneg hp
  have hbox:=((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).2
  have hvCube : actualPrimeTupleLog N p∈cube := by simpa [cube,lower,upper] using hbox
  have hvCompact:=compact_of_cube hvCube
  have hvcell:=owner_mem m hvCube
  by_cases hk : keep p
  · simp only [hk,if_true,true_and]
    by_cases hb : actualPrimeTupleLog N p∈badStrip delta
    · rw [if_pos hb]
      have hv:=totalEnvelope_bounds (actualPrimeTupleLog N p)
      have hw:=compiledKernel_bounds m hvCompact
      have herr : |totalEnvelope (actualPrimeTupleLog N p)-compiledKernel m (actualPrimeTupleLog N p)|≤1000 := by
        apply abs_le.mpr
        constructor <;> linarith
      have hmul:=mul_le_mul_of_nonneg_left herr hweight
      have hnonneg:=mul_nonneg (show 0≤80000*gridStep m by positivity) hweight
      nlinarith
    · rw [if_neg hb]
      have herr:=static_cell_error_off_badStrip m (owner m (actualPrimeTupleLog N p))
        (actualPrimeTupleLog N p) hvcell delta hd hb hstep
      have hmul:=mul_le_mul_of_nonneg_left herr hweight
      simpa only [compiledKernel,mul_zero,add_zero,mul_comm] using hmul
  · simp only [hk,if_false,false_and,add_zero]
    exact mul_nonneg (by positivity) hweight

/-- ONE finite STATIC policy/atom table (indexed by m's rational cells),
width and target threshold precede EVERY arbitrary moving keep mask. -/
theorem exists_uniform_static_cell_compiler (epsilon : ℝ) (he : 0<epsilon) :
    ∃ delta : ℝ,0<delta ∧ ∃ m N0 : ℕ,2≤N0 ∧ ∀ N : ℕ,N0≤N →
      ∀ keep : (Fin 4→ℕ)→Prop,maskedStaticAbsoluteError N m keep<epsilon := by
  obtain ⟨delta,hd,Nwall,hNwall,hwall⟩:=exists_uniform_badMass_reserve
    (epsilon/4000) (by positivity)
  have hC : 0≤originalCubeMassBound := by unfold originalCubeMassBound;positivity
  have hC1 : 0<originalCubeMassBound+1:=by positivity
  have hsmall : 0<min (delta/48) (epsilon/(160000*(originalCubeMassBound+1))) := by
    apply lt_min <;> positivity
  obtain ⟨m,hm⟩:=((tendsto_logPrimeMeshStep (lower:ℝ) (upper:ℝ)).eventually
    (gt_mem_nhds hsmall)).exists
  have hmD : gridStep m<delta/48:=hm.trans_le (min_le_left _ _)
  have hmE : gridStep m<epsilon/(160000*(originalCubeMassBound+1)):=hm.trans_le (min_le_right _ _)
  obtain ⟨Nmass,hNmass⟩:=eventually_atTop.mp eventually_originalCube_mass_bounded
  refine ⟨delta,hd,m,max Nwall (max Nmass 2),?_,?_⟩
  · exact (le_max_right Nmass 2).trans (le_max_right _ _)
  · intro N hN keep
    have hNW : Nwall≤N:=(le_max_left _ _).trans hN
    have hNM : Nmass≤N:=(le_max_left Nmass 2).trans ((le_max_right _ _).trans hN)
    have hN2 : 2≤N:=(le_max_right Nmass 2).trans ((le_max_right _ _).trans hN)
    have hbad:=hwall N hNW keep
    have hmass:=hNmass N hNM
    have hspos : 0<gridStep m:=logPrimeMeshStep_pos (by norm_num [lower,upper]) m
    have herr:=maskedStaticAbsoluteError_bound N m (by omega) keep delta hd (by linarith)
    have hmul:=mul_le_mul_of_nonneg_left hmass (show 0≤80000*gridStep m by positivity)
    have hmeshProduct : gridStep m*(160000*(originalCubeMassBound+1))<epsilon:=
      (lt_div_iff₀ (by positivity : (0:ℝ)<160000*(originalCubeMassBound+1))).mp hmE
    have hextra : 0≤80000*gridStep m:=by positivity
    nlinarith

end

end ImbalancedChen.P5Z.U1011OriginalSixteenStaticCellMesh
