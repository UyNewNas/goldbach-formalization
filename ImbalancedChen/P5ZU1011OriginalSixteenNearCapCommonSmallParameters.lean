import ImbalancedChen.P5ZU1011OriginalSixteenCommonSmallParameters
import ImbalancedChen.P5ZU1011OriginalSixteenJointNearCapCompiler
import ImbalancedChen.P5ZU1011OriginalW16JointSmallBeta

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Actual near-cap version of the finite STATIC native bank. Choose eta>0
first, then ONE positive rational common kappa range and beta exponent
for all selected cells, BEFORE N and every JOINT low/high tuple or atom.
The near-cap deltas are exactly the all16 physical-profile/native compiler
deltas, with true ordinary15 and W constructors. No uniform positive
kappa as eta->0 is claimed. No rho is relabelled as the relative cutoff r;
the r conditions and analytic/AP/coefficient licences remain OPEN.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenNearCapCommonSmallParameters
noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (boxPolicy boxPolicy_certificate selectedPolicy ownerBox tupleTag)
open U1011OriginalSixteenCommonSmallParameters (selectedCells mem_selectedCells owner_mem_selected)
open U1011OriginalW16SmallBetaMonomials (SmallBetaActive)
open P5U1011JointOverlap

def cellDelta (n : ℕ) (eta : ℚ) (j : Grid n) : ℚ :=
  U1011OriginalSixteenNearCapBoxProfiles.delta (boxPolicy (gridBox n j)) (gridBox n j) eta

theorem selected_delta_pos {n : ℕ} (eta : ℚ) (heta : 0<eta) (j : Grid n) (hj : j∈selectedCells n) :
    0<cellDelta n eta j := by
  have hcert := (boxPolicy_certificate (gridBox n j) ((mem_selectedCells j).mp hj)).2
  exact (U1011OriginalSixteenNearCapBoxProfiles.rational_parameters (boxPolicy (gridBox n j))
    (gridBox n j) eta (gridBox_valid n j) (gridBox_lower_positive n j 3) hcert heta).2.2.1

def kappaValues (n : ℕ) (eta : ℚ) : Finset ℚ := insert (1/8)
  ((selectedCells n).image (fun j => cellDelta n eta j/64))
def betaValues (n : ℕ) (eta : ℚ) : Finset ℚ := insert (1/8)
  ((selectedCells n).image (fun j => cellDelta n eta j/2))
theorem kappaValues_nonempty (n : ℕ) (eta : ℚ) : (kappaValues n eta).Nonempty := ⟨1/8,Finset.mem_insert_self _ _⟩
theorem betaValues_nonempty (n : ℕ) (eta : ℚ) : (betaValues n eta).Nonempty := ⟨1/8,Finset.mem_insert_self _ _⟩
def kappaMax (n : ℕ) (eta : ℚ) : ℚ := (kappaValues n eta).min' (kappaValues_nonempty n eta)
def ellMax (n : ℕ) (eta : ℚ) : ℚ := (betaValues n eta).min' (betaValues_nonempty n eta)

theorem kappaMax_pos (n : ℕ) (eta : ℚ) (heta : 0<eta) : 0<kappaMax n eta := by
  unfold kappaMax
  have hmem := Finset.min'_mem (kappaValues n eta) (kappaValues_nonempty n eta)
  rcases Finset.mem_insert.mp hmem with heq|hmem
  · rw [heq]; norm_num
  · obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp hmem
    rw [←heq]
    exact div_pos (selected_delta_pos eta heta j hj) (by norm_num)
theorem ellMax_pos (n : ℕ) (eta : ℚ) (heta : 0<eta) : 0<ellMax n eta := by
  unfold ellMax
  have hmem := Finset.min'_mem (betaValues n eta) (betaValues_nonempty n eta)
  rcases Finset.mem_insert.mp hmem with heq|hmem
  · rw [heq]; norm_num
  · obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp hmem
    rw [←heq]
    exact div_pos (selected_delta_pos eta heta j hj) (by norm_num)

theorem kappaMax_le_eighth (n : ℕ) (eta : ℚ) : kappaMax n eta≤1/8 :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)
theorem ellMax_le_eighth (n : ℕ) (eta : ℚ) : ellMax n eta≤1/8 :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)
theorem kappaMax_le_cell {n : ℕ} (eta : ℚ) (j : Grid n) (hj : j∈selectedCells n) :
    kappaMax n eta≤cellDelta n eta j/64 := by
  apply Finset.min'_le
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨j,hj,rfl⟩))
theorem ellMax_le_cell {n : ℕ} (eta : ℚ) (j : Grid n) (hj : j∈selectedCells n) :
    ellMax n eta≤cellDelta n eta j/2 := by
  apply Finset.min'_le
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨j,hj,rfl⟩))

theorem common_ranges (n : ℕ) (eta : ℚ) (heta : 0<eta) :
    0<kappaMax n eta ∧ kappaMax n eta≤1/8 ∧ 0<ellMax n eta ∧ ellMax n eta≤1/8 ∧
      ∀j∈selectedCells n,kappaMax n eta≤cellDelta n eta j/64 ∧ ellMax n eta≤cellDelta n eta j/2 :=
  ⟨kappaMax_pos n eta heta,kappaMax_le_eighth n eta,ellMax_pos n eta heta,ellMax_le_eighth n eta,
    fun j hj => ⟨kappaMax_le_cell eta j hj,ellMax_le_cell eta j hj⟩⟩

theorem empty_selected_defaults (n : ℕ) (eta : ℚ) (hempty : selectedCells n=∅) :
    kappaMax n eta=1/8 ∧ ellMax n eta=1/8 := by
  simp [kappaMax,ellMax,kappaValues,betaValues,hempty]

/-- Exact binding to the selected physical-profile delta used by the
actual all16 JOINT eta-native compiler. No second eta family is defined. -/
theorem actual_selected_common_bounds {n N : ℕ} (eta : ℚ) {t : Four} (htag : tupleTag n N t≠0)
    {kappa : ℝ} (hk0 : 0<kappa) (hk : kappa≤(kappaMax n eta:ℝ)) :
    kappa≤(1/8:ℝ) ∧
      kappa≤(U1011OriginalSixteenNearCapBoxProfiles.delta (selectedPolicy n N t) (ownerBox n N t) eta:ℝ)/64 ∧
      (ellMax n eta:ℝ)≤(U1011OriginalSixteenNearCapBoxProfiles.delta (selectedPolicy n N t) (ownerBox n N t) eta:ℝ)/2 := by
  have hj := owner_mem_selected htag
  have hκ : (kappaMax n eta:ℝ)≤(cellDelta n eta (owner n (coordinates N t)):ℝ)/64 := by
    exact_mod_cast kappaMax_le_cell eta _ hj
  have hβ : (ellMax n eta:ℝ)≤(cellDelta n eta (owner n (coordinates N t)):ℝ)/2 := by
    exact_mod_cast ellMax_le_cell eta _ hj
  have heighth : (kappaMax n eta:ℝ)≤(1/8:ℝ) := by exact_mod_cast kappaMax_le_eighth n eta
  exact ⟨hk.trans heighth,hk.trans hκ,hβ⟩

theorem selected_W_delta {n : ℕ} (eta : ℚ) (j : Grid n) (hW : boxPolicy (gridBox n j)=wPolicy) :
    cellDelta n eta j=U1011OriginalW16NearCapNative.delta (gridBox n j) eta := by
  simp only [cellDelta,hW,U1011OriginalSixteenNearCapBoxProfiles.delta,
    U1011OriginalSixteenNearCapBoxProfiles.G,U1011OriginalW16NearCapNative.delta,
    wPolicy,show ¬(15:ℕ)<15 by omega,if_false]

/-- The actual active beta size is simultaneously legal at ALL selected
near-cap policy cells; eta, kappa range and ell are fixed first. -/
theorem common_active_beta_size {n N enumeration e : ℕ} (hN : 1<N)
    (eta : ℚ) (j : Grid n) (hj : j∈selectedCells n) (w : ℝ)
    (he : SmallBetaActive N enumeration e w (ellMax n eta:ℝ)) :
    0<e ∧ (e:ℝ)<(N:ℝ)^(ellMax n eta:ℝ) ∧ (e:ℝ)<(N:ℝ)^((cellDelta n eta j:ℝ)/2) := by
  obtain ⟨hepos,hesize,hesupport⟩ := U1011OriginalW16SmallBetaMonomials.active_small_beta_data he
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hbeta : (ellMax n eta:ℝ)≤(cellDelta n eta j:ℝ)/2 := by exact_mod_cast ellMax_le_cell eta j hj
  exact ⟨hepos,hesize,hesize.trans_le (Real.rpow_le_rpow_of_exponent_le hn.le hbeta)⟩

theorem selected_W_common_monomials {n N : ℕ} (hN : 1<N) (eta : ℚ) (heta : 0<eta)
    {E : ℕ×ℕ → Prop} {t : Four} (ht : t∈jointSelector N E)
    (j : Grid n) (hj : j∈selectedCells n) (hW : boxPolicy (gridBox n j)=wPolicy)
    (hbox : coordinates N t∈(gridBox n j).region)
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ)
    (hresidual : actualDwellSupport (U1011OriginalW16NearCapNative.D (gridBox n j) eta N) tail)
    (hrough : ∀q∈tail,Nat.Prime q ∧ (q:ℝ)<U1011OriginalW16NearCapNative.Z (gridBox n j) eta N) :
    let abc := U1011OriginalW16JointFactors.completedFactors (gridBox n j) eta N t A tail
    let delta := (cellDelta n eta j:ℝ)
    abc.1*abc.2.1*abc.2.2=fullPrefix t*tail.prod ∧
      0<abc.1 ∧ 0<abc.2.1 ∧ 0<abc.2.2 ∧ (abc.1:ℝ)≤A ∧
      ∀kappa:ℝ,0<kappa → kappa≤(kappaMax n eta:ℝ) →
        A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2≤(N:ℝ)^(1-4*delta) ∧
        (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤(N:ℝ)^(2-4*delta) ∧
        (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤
          (N:ℝ)^(2-39*delta/8) := by
  have hcert := (boxPolicy_certificate (gridBox n j) ((mem_selectedCells j).mp hj)).2
  rw [hW] at hcert
  obtain ⟨hprod,ha,hb,hc,haA,hu⟩ :=
    U1011OriginalW16JointFactors.fixed_factors_uniform_residue hN ht (gridBox n j) eta heta
      (gridBox_valid n j) (gridBox_lower_positive n j 3) hcert hbox A hA hAupper tail hresidual hrough
  rw [selected_W_delta eta j hW]
  refine ⟨hprod,ha,hb,hc,haA,?_⟩
  intro kappa hk0 hk
  have hd : (0:ℝ)<(cellDelta n eta j:ℝ) := by exact_mod_cast selected_delta_pos eta heta j hj
  have hmin : (kappaMax n eta:ℝ)≤(cellDelta n eta j:ℝ)/64 := by exact_mod_cast kappaMax_le_cell eta j hj
  have hkcell : kappa≤(U1011OriginalW16NearCapNative.delta (gridBox n j) eta:ℝ) := by
    rw [←selected_W_delta eta j hW]
    linarith
  exact hu kappa hk0.le hkcell

/-- TRUE JOINT W consequence for both original bands, with actual beta
attachment and one common range. No high-band source premise occurs. -/
theorem selected_W_common_beta_monomials {n N enumeration e : ℕ} (hN : 1<N)
    (eta : ℚ) (heta : 0<eta) {E : ℕ×ℕ → Prop} {t : Four} (ht : t∈jointSelector N E)
    (j : Grid n) (hj : j∈selectedCells n) (hW : boxPolicy (gridBox n j)=wPolicy)
    (hbox : coordinates N t∈(gridBox n j).region)
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ)
    (hresidual : actualDwellSupport (U1011OriginalW16NearCapNative.D (gridBox n j) eta N) tail)
    (hrough : ∀q∈tail,Nat.Prime q ∧ (q:ℝ)<U1011OriginalW16NearCapNative.Z (gridBox n j) eta N)
    (w : ℝ) (he : SmallBetaActive N enumeration e w (ellMax n eta:ℝ)) :
    let abc := U1011OriginalW16JointSmallBeta.attachedFactors (gridBox n j) eta N t A tail e
    let delta := (cellDelta n eta j:ℝ)
    abc.1*abc.2.1*abc.2.2=e*(fullPrefix t*tail.prod) ∧
      0<abc.1 ∧ 0<abc.2.1 ∧ 0<abc.2.2 ∧ (abc.1:ℝ)≤A ∧
      ∀kappa:ℝ,0<kappa → kappa≤(kappaMax n eta:ℝ) →
        A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2≤(N:ℝ)^(1-3*delta) ∧
        (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤(N:ℝ)^(2-3*delta) ∧
        (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤
          (N:ℝ)^(2-2*delta) := by
  have hcert := (boxPolicy_certificate (gridBox n j) ((mem_selectedCells j).mp hj)).2
  rw [hW] at hcert
  have hell : (0:ℝ)<(ellMax n eta:ℝ) := by exact_mod_cast ellMax_pos n eta heta
  have hbeta : (ellMax n eta:ℝ)≤(U1011OriginalW16NearCapNative.delta (gridBox n j) eta:ℝ)/2 := by
    rw [←selected_W_delta eta j hW]
    exact_mod_cast ellMax_le_cell eta j hj
  obtain ⟨hprod,ha,hb,hc,haA,hu⟩ :=
    U1011OriginalW16JointSmallBeta.fixed_beta_attached_monomials hN ht (gridBox n j) eta heta
      (gridBox_valid n j) (gridBox_lower_positive n j 3) hcert hbox A hA hAupper tail hresidual hrough
      w (ellMax n eta:ℝ) hell hbeta he
  rw [selected_W_delta eta j hW]
  refine ⟨hprod,ha,hb,hc,haA,?_⟩
  intro kappa hk0 hk
  have hd : (0:ℝ)<(cellDelta n eta j:ℝ) := by exact_mod_cast selected_delta_pos eta heta j hj
  have hmin : (kappaMax n eta:ℝ)≤(cellDelta n eta j:ℝ)/64 := by exact_mod_cast kappaMax_le_cell eta j hj
  have hkcell : kappa≤(U1011OriginalW16NearCapNative.delta (gridBox n j) eta:ℝ) := by
    rw [←selected_W_delta eta j hW]
    linarith
  exact hu kappa hk0.le hkcell

end
end ImbalancedChen.P5Z.U1011OriginalSixteenNearCapCommonSmallParameters
