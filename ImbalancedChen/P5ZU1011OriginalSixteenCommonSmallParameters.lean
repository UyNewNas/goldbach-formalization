import ImbalancedChen.P5ZU1011OriginalSixteenStaticNativeCompiler
import ImbalancedChen.P5ZU1011OriginalW16FixedCellSmallBeta

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

ONE positive rational kappa range and ONE positive rational beta exponent
for the ACTUAL finite STATIC selected native grid. The selected cells are
the literal nonzero chosenTag cells; each delta is the actual ordinary15
or distinct W16 native delta. Its positivity is proved from the real cell
constructor and its whole-box certificate, never assumed for an abstract
family. All choices precede N, prime tuples and residual atoms.

The empty selected bank uses explicit default 1/8. The W consequences
below invoke the existing fixed-cell physical caller on its actual U11
source scope; no JOINT high-band membership is fabricated. The parameter
bounds themselves apply to ALL selected tuples on either joint band.
The relative cutoff parameter r has not been identified with rho or
delta: kappa^2<=r and the original nu/r conditions remain OPEN pending
their actual physical definition. Size bounds do not supply beta/rough
coprimality, coefficient unit bounds, an AP estimate or a W density licence.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenCommonSmallParameters
noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler
open U1011OriginalW16SmallBetaMonomials (SmallBetaActive)

def selectedCells (n : ℕ) : Finset (Grid n) := Finset.univ.filter
  (fun j => U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox n j)≠0)
theorem mem_selectedCells {n : ℕ} (j : Grid n) : j∈selectedCells n ↔
    U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox n j)≠0 := by simp [selectedCells]
abbrev SelectedCell (n : ℕ) := {j : Grid n // j∈selectedCells n}

def cellDelta (n : ℕ) (j : Grid n) : ℚ := rowDelta (boxPolicy (gridBox n j)) (gridBox n j)
def cellNu (n : ℕ) (j : Grid n) : ℚ := rowNu (boxPolicy (gridBox n j)) (gridBox n j)

/-- Actual STATIC certificate -> actual native positivity, with both
ordinary15/W branches already distinguished by the native compiler. -/
theorem selected_delta_pos {n : ℕ} (j : Grid n) (hj : j∈selectedCells n) : 0<cellDelta n j := by
  have hchosen := (mem_selectedCells j).mp hj
  have hcert := (boxPolicy_certificate (gridBox n j) hchosen).2
  exact (row_parameters (boxPolicy (gridBox n j)) (gridBox n j) (gridBox_valid n j)
    (gridBox_lower_positive n j 3) hcert).2

def kappaValues (n : ℕ) : Finset ℚ := insert (1/8)
  ((selectedCells n).image (fun j => cellDelta n j/64))
def betaValues (n : ℕ) : Finset ℚ := insert (1/8)
  ((selectedCells n).image (fun j => cellDelta n j/2))
theorem kappaValues_nonempty (n : ℕ) : (kappaValues n).Nonempty := ⟨1/8,Finset.mem_insert_self _ _⟩
theorem betaValues_nonempty (n : ℕ) : (betaValues n).Nonempty := ⟨1/8,Finset.mem_insert_self _ _⟩
def kappaMax (n : ℕ) : ℚ := (kappaValues n).min' (kappaValues_nonempty n)
def ellMax (n : ℕ) : ℚ := (betaValues n).min' (betaValues_nonempty n)

theorem kappaMax_pos (n : ℕ) : 0<kappaMax n := by
  unfold kappaMax
  have hmem := Finset.min'_mem (kappaValues n) (kappaValues_nonempty n)
  rcases Finset.mem_insert.mp hmem with heq|hmem
  · rw [heq]
    norm_num
  · obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp hmem
    rw [←heq]
    exact div_pos (selected_delta_pos j hj) (by norm_num)
theorem ellMax_pos (n : ℕ) : 0<ellMax n := by
  unfold ellMax
  have hmem := Finset.min'_mem (betaValues n) (betaValues_nonempty n)
  rcases Finset.mem_insert.mp hmem with heq|hmem
  · rw [heq]
    norm_num
  · obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp hmem
    rw [←heq]
    exact div_pos (selected_delta_pos j hj) (by norm_num)

theorem kappaMax_le_eighth (n : ℕ) : kappaMax n≤1/8 :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)
theorem ellMax_le_eighth (n : ℕ) : ellMax n≤1/8 :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)
theorem kappaMax_le_cell {n : ℕ} (j : Grid n) (hj : j∈selectedCells n) :
    kappaMax n≤cellDelta n j/64 := by
  apply Finset.min'_le
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨j,hj,rfl⟩))
theorem ellMax_le_cell {n : ℕ} (j : Grid n) (hj : j∈selectedCells n) : ellMax n≤cellDelta n j/2 := by
  apply Finset.min'_le
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨j,hj,rfl⟩))

/-- No existence or positivity premise is requested from a caller. -/
theorem common_ranges (n : ℕ) :
    0<kappaMax n ∧ kappaMax n≤1/8 ∧ 0<ellMax n ∧ ellMax n≤1/8 ∧
      ∀j∈selectedCells n,kappaMax n≤cellDelta n j/64 ∧ ellMax n≤cellDelta n j/2 :=
  ⟨kappaMax_pos n,kappaMax_le_eighth n,ellMax_pos n,ellMax_le_eighth n,
    fun j hj => ⟨kappaMax_le_cell j hj,ellMax_le_cell j hj⟩⟩

theorem empty_selected_defaults (n : ℕ) (hempty : selectedCells n=∅) :
    kappaMax n=1/8 ∧ ellMax n=1/8 := by
  simp [kappaMax,ellMax,kappaValues,betaValues,hempty]

/-- Even the empty/fallback case is tied to the actual static tags. -/
theorem all_fallback_defaults (n : ℕ)
    (hf : ∀j:Grid n,U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox n j)=0) :
    selectedCells n=∅ ∧ kappaMax n=1/8 ∧ ellMax n=1/8 := by
  have he : selectedCells n=∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro j hj
    exact (mem_selectedCells j).mp hj (hf j)
  exact ⟨he,empty_selected_defaults n he⟩

theorem owner_mem_selected {n N : ℕ} {t : Four} (htag : tupleTag n N t≠0) :
    owner n (coordinates N t)∈selectedCells n := (mem_selectedCells _).mpr htag

/-- The scope of these parameter inequalities is ANY actual selected
tuple, including low JOINT tuples. It is independent of source membership. -/
theorem actual_selected_common_bounds {n N : ℕ} {t : Four} (htag : tupleTag n N t≠0)
    {kappa : ℝ} (hk0 : 0<kappa) (hk : kappa≤(kappaMax n:ℝ)) :
    kappa≤(1/8:ℝ) ∧
      kappa≤(rowDelta (selectedPolicy n N t) (ownerBox n N t):ℝ)/64 ∧
      (ellMax n:ℝ)≤(rowDelta (selectedPolicy n N t) (ownerBox n N t):ℝ)/2 := by
  have hj := owner_mem_selected htag
  have hκ : (kappaMax n:ℝ)≤(cellDelta n (owner n (coordinates N t)):ℝ)/64 := by
    exact_mod_cast kappaMax_le_cell _ hj
  have hβ : (ellMax n:ℝ)≤(cellDelta n (owner n (coordinates N t)):ℝ)/2 := by
    exact_mod_cast ellMax_le_cell _ hj
  have heighth : (kappaMax n:ℝ)≤(1/8:ℝ) := by exact_mod_cast kappaMax_le_eighth n
  exact ⟨hk.trans heighth,hk.trans hκ,hβ⟩

theorem selected_W_delta {n : ℕ} (j : Grid n) (hW : boxPolicy (gridBox n j)=wPolicy) :
    cellDelta n j=U1011OriginalW16FixedCellNative.delta (gridBox n j) := by
  simp only [cellDelta,hW,rowDelta,wPolicy,show ¬(15:ℕ)<15 by omega,if_false]

/-- Common kappa simultaneously enters every actual selected W cell's
SAME-factor theorem. The caller supplies genuine residual well/rough
support, not the desired factorization or monomial. -/
theorem selected_W_common_monomials {n N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) (j : Grid n) (hj : j∈selectedCells n)
    (hW : boxPolicy (gridBox n j)=wPolicy) (hbox : coordinates N t∈(gridBox n j).region)
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ)
    (hresidual : actualDwellSupport (U1011OriginalW16FixedCellNative.D (gridBox n j) N) tail)
    (hrough : ∀q∈tail,Nat.Prime q ∧ (q:ℝ)<U1011OriginalW16FixedCellNative.Z (gridBox n j) N) :
    let abc := U1011OriginalW16FixedCellFactors.completedFactors (gridBox n j) N t A tail
    let delta := (cellDelta n j:ℝ)
    abc.1*abc.2.1*abc.2.2=fullPrefix t*tail.prod ∧
      0<abc.1 ∧ 0<abc.2.1 ∧ 0<abc.2.2 ∧ (abc.1:ℝ)≤A ∧
      ∀kappa:ℝ,0<kappa → kappa≤(kappaMax n:ℝ) →
        A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2≤(N:ℝ)^(1-4*delta) ∧
        (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤(N:ℝ)^(2-4*delta) ∧
        (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤
          (N:ℝ)^(2-39*delta/8) := by
  have hc := (boxPolicy_certificate (gridBox n j) ((mem_selectedCells j).mp hj)).2
  rw [hW] at hc
  obtain ⟨hprod,ha,hb,hcpos,haA,hu⟩ :=
    U1011OriginalW16FixedCellFactors.fixed_factors_uniform_residue hN ht (gridBox n j)
      (gridBox_valid n j) (gridBox_lower_positive n j 3) hc hbox A hA hAupper tail hresidual hrough
  rw [selected_W_delta j hW]
  refine ⟨hprod,ha,hb,hcpos,haA,?_⟩
  intro kappa hk0 hk
  have hd : (0:ℝ)<(cellDelta n j:ℝ) := by exact_mod_cast selected_delta_pos j hj
  have hmin : (kappaMax n:ℝ)≤(cellDelta n j:ℝ)/64 := by exact_mod_cast kappaMax_le_cell j hj
  have hkcell : kappa≤(U1011OriginalW16FixedCellNative.delta (gridBox n j):ℝ) := by
    rw [←selected_W_delta j hW]
    linarith
  exact hu kappa hk0.le hkcell

/-- The real active small coefficient supplies its positive integer and
the common beta support bound simultaneously for EVERY selected policy,
including W. No beta/rough coprimality or coefficient-unit claim follows. -/
theorem common_active_beta_size {n N enumeration e : ℕ} (hN : 1<N)
    (j : Grid n) (hj : j∈selectedCells n) (w : ℝ)
    (he : SmallBetaActive N enumeration e w (ellMax n:ℝ)) :
    0<e ∧ (e:ℝ)<(N:ℝ)^(ellMax n:ℝ) ∧ (e:ℝ)<(N:ℝ)^((cellDelta n j:ℝ)/2) := by
  obtain ⟨hepos,hesize,hesupport⟩ := U1011OriginalW16SmallBetaMonomials.active_small_beta_data he
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hbeta : (ellMax n:ℝ)≤(cellDelta n j:ℝ)/2 := by exact_mod_cast ellMax_le_cell j hj
  exact ⟨hepos,hesize,hesize.trans_le (Real.rpow_le_rpow_of_exponent_le hn.le hbeta)⟩

/-- Both common parameters are chosen from the STATIC finite bank before
N. The actual active beta block attaches to the same W third factor and
the resulting factorization is uniform over the common kappa interval. -/
theorem selected_W_common_beta_monomials {n N enumeration e : ℕ} (hN : 1<N)
    {E : ℕ×ℕ → Prop} {t : Four} (ht : t∈U11Adaptive.source N E)
    (j : Grid n) (hj : j∈selectedCells n) (hW : boxPolicy (gridBox n j)=wPolicy)
    (hbox : coordinates N t∈(gridBox n j).region)
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ)
    (hresidual : actualDwellSupport (U1011OriginalW16FixedCellNative.D (gridBox n j) N) tail)
    (hrough : ∀q∈tail,Nat.Prime q ∧ (q:ℝ)<U1011OriginalW16FixedCellNative.Z (gridBox n j) N)
    (w : ℝ) (he : SmallBetaActive N enumeration e w (ellMax n:ℝ)) :
    let abc := U1011OriginalW16FixedCellSmallBeta.attachedFactors (gridBox n j) N t A tail e
    let delta := (cellDelta n j:ℝ)
    abc.1*abc.2.1*abc.2.2=e*(fullPrefix t*tail.prod) ∧
      0<abc.1 ∧ 0<abc.2.1 ∧ 0<abc.2.2 ∧ (abc.1:ℝ)≤A ∧
      ∀kappa:ℝ,0<kappa → kappa≤(kappaMax n:ℝ) →
        A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2≤(N:ℝ)^(1-3*delta) ∧
        (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤(N:ℝ)^(2-3*delta) ∧
        (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤
          (N:ℝ)^(2-2*delta) := by
  have hcert := (boxPolicy_certificate (gridBox n j) ((mem_selectedCells j).mp hj)).2
  rw [hW] at hcert
  have hell : (0:ℝ)<(ellMax n:ℝ) := by exact_mod_cast ellMax_pos n
  have hbeta : (ellMax n:ℝ)≤(U1011OriginalW16FixedCellNative.delta (gridBox n j):ℝ)/2 := by
    rw [←selected_W_delta j hW]
    exact_mod_cast ellMax_le_cell j hj
  obtain ⟨hprod,ha,hb,hc,haA,hu⟩ :=
    U1011OriginalW16FixedCellSmallBeta.fixed_beta_attached_monomials hN ht (gridBox n j)
      (gridBox_valid n j) (gridBox_lower_positive n j 3) hcert hbox A hA hAupper tail hresidual hrough
      w (ellMax n:ℝ) hell hbeta he
  rw [selected_W_delta j hW]
  refine ⟨hprod,ha,hb,hc,haA,?_⟩
  intro kappa hk0 hk
  have hd : (0:ℝ)<(cellDelta n j:ℝ) := by exact_mod_cast selected_delta_pos j hj
  have hmin : (kappaMax n:ℝ)≤(cellDelta n j:ℝ)/64 := by exact_mod_cast kappaMax_le_cell j hj
  have hkcell : kappa≤(U1011OriginalW16FixedCellNative.delta (gridBox n j):ℝ) := by
    rw [←selected_W_delta j hW]
    linarith
  exact hu kappa hk0.le hkcell

end
end ImbalancedChen.P5Z.U1011OriginalSixteenCommonSmallParameters
