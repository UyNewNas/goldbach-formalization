import ImbalancedChen.P5ZU1011OriginalSixteenStaticCellMesh
import ImbalancedChen.P5ZU1011OriginalSixteenNearCapBoxProfiles
import ImbalancedChen.P5ZU1011BufferedPrimeReserve

/-!
Actual physical profiles of the STATIC original16 cell compiler, on the
original U11 source only. Precision is the exact rational mesh step; all
native parameters and the already selected corner tag precede N and tuples.
Ordinary cell cost is the actual fixed Rphys/Zexp H248 expression, not its
endpoint frozen-atom surrogate. No native-density=H248 identity is asserted.

Zero extension off actual source/certified cells produces tuple buffer
maps satisfying the named actual-prime BufferSup contract from the true
12*meshstep geometric bound. No perturbation or approximation premise is
supplied. SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenPhysicalStaticProfiles

open Set
open Classical
open U11Integral U11Canonical U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSourceGeometryMesh U1011OriginalSixteenUniformEnvelopeMesh
open U1011OriginalSixteenStaticCellWinner U1011OriginalSixteenStaticCellMesh
open U1011OriginalFifteenNativeGridCells
open scoped BigOperators

noncomputable section

def precision (m : ℕ) : ℚ := (upper-lower)/(m+1:ℚ)

theorem precision_pos (m : ℕ) : 0<precision m := by
  unfold precision
  exact div_pos (by norm_num [lower,upper]) (by positivity)

theorem cast_precision (m : ℕ) : (precision m:ℝ)=gridStep m := by
  simp [precision,gridStep,logPrimeMeshStep]

def physicalOrdinary (B : Box) (eta : ℚ) (j : ℕ) : ℝ :=
  if hj : j<16 then U1011OriginalSixteenNearCapBoxProfiles.nativeCost ⟨j,hj⟩ B eta else 0

def physicalCellKernel (m : ℕ) (j : Grid m) (v : LogFour) : ℝ :=
  if corner (gridBox m j)∈sourceDomain then
    if chosenTag (gridBox m j)=0 then actualSwitch v
    else physicalOrdinary (gridBox m j) (precision m) (chosenTag (gridBox m j)).pred
  else 0

/-- The source filter is the actual original U11 domain. No D10 support
is claimed to be a subset, and the arbitrary keep mask stays at the tuple. -/
def physicalCompiledKernel (m : ℕ) : LogFour→ℝ :=
  sourceDomain.indicator (fun v=>physicalCellKernel m (owner m v) v)

def active (m : ℕ) (p : Policy) (v : LogFour) : Prop :=
  v∈sourceDomain ∧ corner (gridBox m (owner m v))∈sourceDomain ∧
    wholeBoxEligibleTest p (gridBox m (owner m v))=true

def tauMap (m : ℕ) (p : Policy) (v : LogFour) : ℝ :=
  if active m p v then U1011OriginalSixteenNearCapBoxProfiles.tau p
    (gridBox m (owner m v)) (precision m) v else 0

def xiMap (m : ℕ) (p : Policy) (v : LogFour) : ℝ :=
  if active m p v then U1011OriginalSixteenNearCapBoxProfiles.xiEff p
    (gridBox m (owner m v)) (precision m) v else 0

def rhoMap (m : ℕ) (p : Policy) (v : LogFour) : ℝ :=
  if active m p v then (U1011OriginalSixteenNearCapBoxProfiles.rho p
    (gridBox m (owner m v)) (precision m):ℝ) else 0

def tupleTau (N m : ℕ) : BufferedPrimeErrorPayment.BufferMap :=
  fun p t=>tauMap m p (actualPrimeTupleLog N t)

def tupleXi (N m : ℕ) : BufferedPrimeErrorPayment.BufferMap :=
  fun p t=>xiMap m p (actualPrimeTupleLog N t)

def tupleRho (N m : ℕ) : BufferedPrimeErrorPayment.BufferMap :=
  fun p t=>rhoMap m p (actualPrimeTupleLog N t)

/-- Actual all16 buffers have one geometric mesh bound, including W.
The extension is identically zero on every inactive policy/source point. -/
theorem buffer_bounds (m : ℕ) (p : Policy) (v : LogFour) (hvCube : v∈cube) :
    0≤tauMap m p v ∧ tauMap m p v≤12*gridStep m ∧
      0≤xiMap m p v ∧ xiMap m p v≤12*gridStep m ∧
      0≤rhoMap m p v ∧ rhoMap m p v≤12*gridStep m := by
  have hspos : 0<gridStep m:=logPrimeMeshStep_pos (by norm_num [lower,upper]) m
  by_cases ha : active m p v
  · have hvcell:=owner_mem m hvCube
    have hvbox:=cell_subset_closed_box m (owner m v) hvcell
    have hside:=U1011OriginalFifteenSeparateGridCoverage.grid_width m (owner m v)
    have hb:=U1011OriginalSixteenNearCapBoxProfiles.uniform_buffer_bound_of_coordinate_side
      p (gridBox m (owner m v)) (precision m) (gridBox_valid m (owner m v))
      (gridBox_lower_positive m (owner m v) 3) ha.2.2 (precision_pos m)
      (gridStep m) hspos.le hside (by rw [cast_precision]) v hvbox
    have ht : U1011OriginalSixteenNearCapBoxProfiles.tau p (gridBox m (owner m v)) (precision m) v≤12*gridStep m :=
      (le_max_left _ _).trans hb.2.2.2
    have hx : U1011OriginalSixteenNearCapBoxProfiles.xiEff p (gridBox m (owner m v)) (precision m) v≤12*gridStep m :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hb.2.2.2)
    have hr : (U1011OriginalSixteenNearCapBoxProfiles.rho p (gridBox m (owner m v)) (precision m):ℝ)≤12*gridStep m :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hb.2.2.2)
    simp only [tauMap,xiMap,rhoMap,if_pos ha]
    exact ⟨hb.1,ht,hb.2.1,hx,hb.2.2.1,hr⟩
  · simp only [tauMap,xiMap,rhoMap,if_neg ha]
    exact ⟨le_rfl,by positivity,le_rfl,by positivity,le_rfl,by positivity⟩

/-- The generic actual-prime buffer premise is discharged by fixed mesh
geometry. beta is chosen by the genuine prime reserve before the mesh. -/
theorem actual_BufferSup (N m : ℕ) (hN : 1<N) (beta : ℝ)
    (hsmall : 12*gridStep m≤beta) :
    BufferedPrimeReserve.BufferSup N beta (tupleTau N m) (tupleXi N m) (tupleRho N m) := by
  intro p t ht
  have hbox:=((mem_actualPrimeBoxTuples_log_iff hN _ _ t).mp ht).2
  have hvCube : actualPrimeTupleLog N t∈cube := by simpa [cube,lower,upper] using hbox
  have hb:=buffer_bounds m p _ hvCube
  exact ⟨hb.1,hb.2.1.trans hsmall,hb.2.2.1,hb.2.2.2.1.trans hsmall,
    hb.2.2.2.2.1,hb.2.2.2.2.2.trans hsmall⟩

theorem physicalCellKernel_eq_nativeCost (m : ℕ) (j : Grid m) (p : Policy) (v : LogFour)
    (hcorner : corner (gridBox m j)∈sourceDomain)
    (htag : chosenTag (gridBox m j)=p.val.succ) :
    physicalCellKernel m j v=U1011OriginalSixteenNearCapBoxProfiles.nativeCost p (gridBox m j) (precision m) := by
  simp only [physicalCellKernel,if_pos hcorner,htag,Nat.succ_ne_zero,if_false,Nat.pred_succ,
    physicalOrdinary,dif_pos p.isLt]

theorem physicalCellKernel_eq_fallback (m : ℕ) (j : Grid m) (v : LogFour)
    (hcorner : corner (gridBox m j)∈sourceDomain) (htag : chosenTag (gridBox m j)=0) :
    physicalCellKernel m j v=actualSwitch v := by
  simp only [physicalCellKernel,if_pos hcorner,htag,if_pos rfl]

/-- The compiled selected cell cost is EXACTLY the real physicalCost of
these actual buffer maps, using the same fixed rational native R and Z. -/
theorem selected_nativeCost_eq_buffered (m : ℕ) (p : Policy) (v : LogFour)
    (hvCube : v∈cube) (hv : v∈sourceDomain)
    (hcorner : corner (gridBox m (owner m v))∈sourceDomain)
    (htag : chosenTag (gridBox m (owner m v))=p.val.succ) :
    U1011OriginalSixteenNearCapBoxProfiles.nativeCost p (gridBox m (owner m v)) (precision m)=
      BufferedOrdinaryClamp.physicalCost (typedResidual p v) (v 3)
        (tauMap m p v) (xiMap m p v) (rhoMap m p v) := by
  have htest:=chosen_ordinary_certificate _ p htag
  have ha : active m p v:=⟨hv,hcorner,htest⟩
  simp only [tauMap,xiMap,rhoMap,if_pos ha]
  exact U1011OriginalSixteenNearCapBoxProfiles.nativeCost_eq_physicalCost p _ (precision m)
    (gridBox_valid m (owner m v)) (gridBox_lower_positive m (owner m v) 3) htest (precision_pos m) v

end

end ImbalancedChen.P5Z.U1011OriginalSixteenPhysicalStaticProfiles
