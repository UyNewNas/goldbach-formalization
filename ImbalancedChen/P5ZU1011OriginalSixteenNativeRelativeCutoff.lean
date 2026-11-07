import ImbalancedChen.P5ZU1011OriginalSixteenNearCapCommonSmallParameters

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The native RELATIVE cutoff is r=zeta/Rexp, where Rexp is the actual
residual level exponent and zeta the actual lowered cutoff exponent.
It is NOT rho. Both the midpoint and eta-native selected families retain
their exact D/Z parameter dictionary. Actual rational grid constructors
give a<=Rexp<=1, wLo>=a, xi<=wLo/2 and 0<rho<1; these imply
zeta>=a/3 and r>=a/3>1/64. The already constructed COMMON kappa range
therefore gives kappa^2<r without an r-bound input.

Only this native D/Z dictionary is asserted. No automatic identification
with a P3 global nu, distribution theorem, density, coefficient-unit or
beta/rough coprimality licence is made.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenNativeRelativeCutoff
noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (boxPolicy boxPolicy_certificate rowNu rowDelta rowD rowZ)
open U1011OriginalSixteenNearCapBoxProfiles (G Tplus)

def a : ℚ := 417/5000
def fixedXi (p : Policy) (B : Box) : ℚ := min (B.lo 3/2) (rowDelta p B)
def fixedRho (p : Policy) (B : Box) : ℚ := rowDelta p B
def fixedLocalNu (p : Policy) (B : Box) : ℚ := rowNu p B-Tplus B-20*rowDelta p B
def fixedZeta (p : Policy) (B : Box) : ℚ := min (B.lo 3-fixedXi p B) (fixedLocalNu p B/(2+fixedRho p B))
def fixedRelativeCutoff (p : Policy) (B : Box) : ℚ := fixedZeta p B/fixedLocalNu p B
def nearLocalNu (p : Policy) (B : Box) (eta : ℚ) : ℚ := U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p B eta
def nearZeta (p : Policy) (B : Box) (eta : ℚ) : ℚ := U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta
def nearRelativeCutoff (p : Policy) (B : Box) (eta : ℚ) : ℚ := nearZeta p B eta/nearLocalNu p B eta

theorem grid_lo_ge_a (n : ℕ) (j : Grid n) (i : Fin 4) : a≤(gridBox n j).lo i := by
  have h := (logPrimeMeshLoHi_bounds (by norm_num [lower,upper] : (lower:ℝ)<(upper:ℝ)) n j i).1
  rw [←cast_grid_lo] at h
  change (417/5000:ℚ)≤(gridBox n j).lo i
  exact_mod_cast h

private theorem capLower_lt_one (p : Policy) (B : Box) (hhi : ∀i,0≤B.hi i) : capLower p B<1 := by
  have hs : 0≤selectedMassQ p B.hi := by
    apply Finset.sum_nonneg
    intro i hi
    by_cases h : Selected p i <;> simp [h,hhi i]
  by_cases hp : p.val<15
  · have hmin := min_le_right ((1+selectedMassQ p B.lo)/2)
      (57/64-(3/2:ℚ)*selectedMassQ p B.hi)
    simp only [capLower,if_pos hp]
    linarith
  · simp only [capLower,if_neg hp]
    linarith [hhi 2]

private theorem fixed_delta_formula (p : Policy) (B : Box) :
    rowDelta p B=min (3/4096) (min ((rowNu p B-G p B)/64) ((capLower p B-rowNu p B)/64)) := by
  by_cases hp : p.val<15
  · simp only [rowDelta,rowNu,G,if_pos hp,U1011OriginalFifteenFixedCellNative.delta]
  · simp only [rowDelta,rowNu,G,if_neg hp,U1011OriginalW16FixedCellNative.delta]

/-- Every bound is produced by the actual certified native box. The
last full-square upper endpoint pays the common prefix and44delta. -/
theorem fixed_native_box_facts (p : Policy) (B : Box) (hvalid : B.Valid)
    (hlo : ∀i,a≤B.lo i) (htest : wholeBoxEligibleTest p B=true) :
    a≤fixedLocalNu p B ∧ fixedLocalNu p B≤1 ∧
      0<fixedRho p B ∧ fixedRho p B<1 ∧ fixedXi p B≤B.lo 3/2 := by
  have ha : (0:ℚ)<a := by norm_num [a]
  have hpositive : 0<B.lo 3 := ha.trans_le (hlo 3)
  have hp := U1011OriginalSixteenStaticNativeCompiler.row_parameters p B hvalid hpositive htest
  have hδ := hp.2
  have hcap := hp.1
  have hupper := U1011OriginalSixteenNearCapBoxProfiles.fullUpper_le_G p B (3:Fin 4)
  rw [U1011OriginalSixteenNearCapBoxProfiles.lastUpper_eq_Tplus] at hupper
  have hformula := fixed_delta_formula p B
  have hdle : rowDelta p B≤(rowNu p B-G p B)/64 := by
    rw [hformula]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hdcap : rowDelta p B≤3/4096 := by rw [hformula]; exact min_le_left _ _
  have hhi : ∀i,0≤B.hi i := fun i => ha.le.trans ((hlo i).trans (hvalid i))
  have hT : 0≤Tplus B := by
    change 0≤B.hi 0+B.hi 1+B.hi 2+B.hi 3
    linarith [hhi 0,hhi 1,hhi 2,hhi 3]
  have hcapone := capLower_lt_one p B hhi
  refine ⟨?_,?_,hδ,?_,min_le_left _ _⟩
  · unfold fixedLocalNu
    linarith [hlo 3,hvalid 3]
  · unfold fixedLocalNu
    linarith
  · change rowDelta p B<1
    linarith

theorem near_native_box_facts (p : Policy) (B : Box) (eta : ℚ) (heta : 0<eta)
    (hvalid : B.Valid) (hlo : ∀i,a≤B.lo i) (htest : wholeBoxEligibleTest p B=true) :
    a≤nearLocalNu p B eta ∧ nearLocalNu p B eta≤1 ∧
      0<U1011OriginalSixteenNearCapBoxProfiles.rho p B eta ∧
      U1011OriginalSixteenNearCapBoxProfiles.rho p B eta<1 ∧
      U1011OriginalSixteenNearCapBoxProfiles.xi p B eta≤B.lo 3/2 := by
  have ha : (0:ℚ)<a := by norm_num [a]
  have hpositive : 0<B.lo 3 := ha.trans_le (hlo 3)
  have hp := U1011OriginalSixteenNearCapBoxProfiles.rational_parameters p B eta hvalid hpositive htest heta
  have hδ := hp.2.2.1
  have hnu := hp.2.1
  have hupper := U1011OriginalSixteenNearCapBoxProfiles.fullUpper_le_G p B (3:Fin 4)
  rw [U1011OriginalSixteenNearCapBoxProfiles.lastUpper_eq_Tplus] at hupper
  have hG : Tplus B+B.lo 3≤G p B := by linarith [hvalid 3]
  have hR := NearCapRationalParameters.residual_lower (G p B) (capLower p B) eta (Tplus B) (B.lo 3) hG
  have hdcap := NearCapRationalParameters.delta_le_cap (G p B) (capLower p B) eta
  have hxi := NearCapRationalParameters.xi_le_half (G p B) (capLower p B) eta (B.lo 3)
  have hhi : ∀i,0≤B.hi i := fun i => ha.le.trans ((hlo i).trans (hvalid i))
  have hT : 0≤Tplus B := by
    change 0≤B.hi 0+B.hi 1+B.hi 2+B.hi 3
    linarith [hhi 0,hhi 1,hhi 2,hhi 3]
  have hcapone := capLower_lt_one p B hhi
  change B.lo 3+44*U1011OriginalSixteenNearCapBoxProfiles.delta p B eta≤nearLocalNu p B eta at hR
  refine ⟨by linarith [hlo 3],?_,hp.2.2.2.2.1,?_,hxi⟩
  · change U1011OriginalSixteenNearCapBoxProfiles.nu p B eta-Tplus B-
      20*U1011OriginalSixteenNearCapBoxProfiles.delta p B eta≤1
    linarith
  · change NearCapRationalParameters.delta (G p B) (capLower p B) eta<1
    linarith

/-- Elementary relative-cutoff geometry after the native constructor.
The two terms of the REAL min are retained; zeta is never replaced by a. -/
theorem relative_geometry (R w xi rho : ℚ) (hRlo : a≤R) (hRhi : R≤1)
    (hw : a≤w) (hxi : xi≤w/2) (hrho : 0<rho) (hrho1 : rho<1) :
    let zeta := min (w-xi) (R/(2+rho))
    let r := zeta/R
    R*r=zeta ∧ a/3≤zeta ∧ a/3≤r ∧ 0<r ∧
      r≤1/(2+rho) ∧ (1/(2+rho):ℚ)<1/2 ∧ R*r<1 := by
  have ha : (0:ℚ)<a := by norm_num [a]
  have hR : 0<R := ha.trans_le hRlo
  have hden : 0<2+rho := by linarith
  have hz1 : a/3≤w-xi := by linarith
  have hz2 : a/3≤R/(2+rho) := by
    apply (le_div_iff₀ hden).2
    have hm := mul_le_mul_of_nonneg_left hrho1.le (show (0:ℚ)≤a/3 by linarith)
    nlinarith
  have hz : a/3≤min (w-xi) (R/(2+rho)) := le_min hz1 hz2
  have hzl : min (w-xi) (R/(2+rho))≤R/(2+rho) := min_le_right _ _
  have hrlo : a/3≤min (w-xi) (R/(2+rho))/R := by
    apply (le_div_iff₀ hR).2
    have hm := mul_le_mul_of_nonneg_left hRhi (show (0:ℚ)≤a/3 by linarith)
    nlinarith
  have hrhi : min (w-xi) (R/(2+rho))/R≤1/(2+rho) := by
    apply (div_le_iff₀ hR).2
    calc
      _ ≤ R/(2+rho) := hzl
      _ = (1/(2+rho))*R := by ring
  have hrhalf : (1/(2+rho):ℚ)<1/2 := by
    apply (div_lt_iff₀ hden).2
    linarith
  have hprod : R*(min (w-xi) (R/(2+rho))/R)=min (w-xi) (R/(2+rho)) := by
    field_simp [hR.ne'] <;> ring
  refine ⟨hprod,hz,hrlo,by linarith,hrhi,hrhalf,?_⟩
  have hrpos : 0<min (w-xi) (R/(2+rho))/R := by linarith
  have hm := mul_le_mul_of_nonneg_right hRhi hrpos.le
  nlinarith

theorem fixed_grid_dictionary (n : ℕ) (j : Grid n) (p : Policy)
    (htest : wholeBoxEligibleTest p (gridBox n j)=true) :
    fixedLocalNu p (gridBox n j)*fixedRelativeCutoff p (gridBox n j)=fixedZeta p (gridBox n j) ∧
      a/3≤fixedZeta p (gridBox n j) ∧ a/3≤fixedRelativeCutoff p (gridBox n j) ∧
      0<fixedRelativeCutoff p (gridBox n j) ∧
      fixedRelativeCutoff p (gridBox n j)≤1/(2+fixedRho p (gridBox n j)) ∧
      (1/(2+fixedRho p (gridBox n j)):ℚ)<1/2 ∧
      fixedLocalNu p (gridBox n j)*fixedRelativeCutoff p (gridBox n j)<1 := by
  have hf := fixed_native_box_facts p (gridBox n j) (gridBox_valid n j) (grid_lo_ge_a n j) htest
  exact relative_geometry _ _ _ _ hf.1 hf.2.1 (grid_lo_ge_a n j 3) hf.2.2.2.2 hf.2.2.1 hf.2.2.2.1

theorem near_grid_dictionary (n : ℕ) (j : Grid n) (p : Policy) (eta : ℚ) (heta : 0<eta)
    (htest : wholeBoxEligibleTest p (gridBox n j)=true) :
    nearLocalNu p (gridBox n j) eta*nearRelativeCutoff p (gridBox n j) eta=nearZeta p (gridBox n j) eta ∧
      a/3≤nearZeta p (gridBox n j) eta ∧ a/3≤nearRelativeCutoff p (gridBox n j) eta ∧
      0<nearRelativeCutoff p (gridBox n j) eta ∧
      nearRelativeCutoff p (gridBox n j) eta≤1/(2+U1011OriginalSixteenNearCapBoxProfiles.rho p (gridBox n j) eta) ∧
      (1/(2+U1011OriginalSixteenNearCapBoxProfiles.rho p (gridBox n j) eta):ℚ)<1/2 ∧
      nearLocalNu p (gridBox n j) eta*nearRelativeCutoff p (gridBox n j) eta<1 := by
  have hf := near_native_box_facts p (gridBox n j) eta heta (gridBox_valid n j) (grid_lo_ge_a n j) htest
  exact relative_geometry _ _ _ _ hf.1 hf.2.1 (grid_lo_ge_a n j 3) hf.2.2.2.2 hf.2.2.1 hf.2.2.2.1

/-- Exact physical D/Z dictionary at every original midpoint policy.
These are actual level and cutoff exponents, not the original global cap. -/
theorem fixed_physical_dictionary (p : Policy) (B : Box) (N : ℕ) :
    rowD p B N=(N:ℝ)^(fixedLocalNu p B:ℝ) ∧ rowZ p B N=(N:ℝ)^(fixedZeta p B:ℝ) := by
  constructor
  · simpa only [fixedLocalNu,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat] using
      U1011OriginalSixteenJointNativeCompiler.rowD_exact p B N
  · by_cases hp : p.val<15
    · simp only [rowZ,rowNu,rowDelta,if_pos hp,U1011OriginalFifteenFixedCellNative.Z,
        U1011OriginalFifteenFixedCellNative.cutoffExponent,U1011OriginalFifteenFixedCellNative.residualExponent,
        U1011OriginalFifteenFixedCellNative.xi,U1011OriginalFifteenFixedCellNative.rho,
        fixedZeta,fixedLocalNu,fixedXi,fixedRho,U1011OriginalSixteenNearCapBoxProfiles.Tplus]
    · simp only [rowZ,rowNu,rowDelta,if_neg hp,U1011OriginalW16FixedCellNative.Z,
        U1011OriginalW16FixedCellNative.cutoffExponent,U1011OriginalW16FixedCellNative.residualExponent,
        U1011OriginalW16FixedCellNative.xi,U1011OriginalW16FixedCellNative.rho,
        fixedZeta,fixedLocalNu,fixedXi,fixedRho,U1011OriginalSixteenNearCapBoxProfiles.Tplus,
        U1011OriginalFifteenFixedCellNative.Tplus,U1011OriginalW16FixedCellNative.Tplus]

theorem near_physical_dictionary (p : Policy) (B : Box) (eta : ℚ) (N : ℕ) :
    U1011OriginalSixteenJointNearCapCompiler.rowD p B eta N=(N:ℝ)^(nearLocalNu p B eta:ℝ) ∧
      U1011OriginalSixteenJointNearCapCompiler.rowZ p B eta N=(N:ℝ)^(nearZeta p B eta:ℝ) := ⟨rfl,rfl⟩

theorem small_kappa_square {r kappa : ℝ} (hr : (a:ℝ)/3≤r)
    (hk0 : 0<kappa) (hk : kappa≤1/8) : kappa^2<r := by
  have hprod := mul_nonneg (show (0:ℝ)≤1/8-kappa by linarith) (show (0:ℝ)≤1/8+kappa by linarith)
  have ha : (1/64:ℝ)<(a:ℝ)/3 := by norm_num [a]
  nlinarith

theorem fixed_selected_common_kappa_square {n : ℕ} (j : Grid n)
    (hj : j∈U1011OriginalSixteenCommonSmallParameters.selectedCells n)
    {kappa : ℝ} (hk0 : 0<kappa)
    (hk : kappa≤(U1011OriginalSixteenCommonSmallParameters.kappaMax n:ℝ)) :
    kappa^2<(fixedRelativeCutoff (boxPolicy (gridBox n j)) (gridBox n j):ℝ) := by
  have ht := (boxPolicy_certificate (gridBox n j)
    ((U1011OriginalSixteenCommonSmallParameters.mem_selectedCells j).mp hj)).2
  have hrQ := (fixed_grid_dictionary n j _ ht).2.2.1
  have hr : (a:ℝ)/3≤(fixedRelativeCutoff (boxPolicy (gridBox n j)) (gridBox n j):ℝ) := by exact_mod_cast hrQ
  have hkmax : (U1011OriginalSixteenCommonSmallParameters.kappaMax n:ℝ)≤1/8 := by
    exact_mod_cast U1011OriginalSixteenCommonSmallParameters.kappaMax_le_eighth n
  exact small_kappa_square hr hk0 (hk.trans hkmax)

theorem near_selected_common_kappa_square {n : ℕ} (eta : ℚ) (heta : 0<eta) (j : Grid n)
    (hj : j∈U1011OriginalSixteenCommonSmallParameters.selectedCells n)
    {kappa : ℝ} (hk0 : 0<kappa)
    (hk : kappa≤(U1011OriginalSixteenNearCapCommonSmallParameters.kappaMax n eta:ℝ)) :
    kappa^2<(nearRelativeCutoff (boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ) := by
  have ht := (boxPolicy_certificate (gridBox n j)
    ((U1011OriginalSixteenCommonSmallParameters.mem_selectedCells j).mp hj)).2
  have hrQ := (near_grid_dictionary n j _ eta heta ht).2.2.1
  have hr : (a:ℝ)/3≤(nearRelativeCutoff (boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ) := by exact_mod_cast hrQ
  have hkmax : (U1011OriginalSixteenNearCapCommonSmallParameters.kappaMax n eta:ℝ)≤1/8 := by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.kappaMax_le_eighth n eta
  exact small_kappa_square hr hk0 (hk.trans hkmax)

end
end ImbalancedChen.P5Z.U1011OriginalSixteenNativeRelativeCutoff
