import ImbalancedChen.P5OriginalWActiveMarkFixedMedium

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The selected W rectangles form one finite family indexed by the actual
prefix owner, bounded canonical rough rank and one fixed fine-mesh label.
The W completion group lists depend on this atom key and the HB length,
not on the arithmetic mark or the sign of a discrepancy. One threshold
pays all selected W owner cells after the finite bank is fixed.
-/
namespace ImbalancedChen.P5Z.OriginalWSelectedAtomFamily
noncomputable section
open Classical Set
open scoped BigOperators
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler
open U1011OriginalSixteenNearCapBoxProfiles
open U1011OriginalSixteenCommonSmallParameters (selectedCells owner_mem_selected)
open U1011OriginalSixteenNearCapCommonSmallParameters
open OriginalCommonBetaActualParameters OriginalJointCommonBetaModel
open OriginalOrdinaryPresievedSigma
open OriginalPresievedRoughPrimeSlots OriginalPresievedRoughRank
open OriginalWOwnerOccurrenceBinding OriginalWFixedMeshBudgets
open OriginalWActiveMarkFixedMedium OriginalWWholeBoxRealRun
open OriginalWWholeBoxEndpointMonomials
open U1011OriginalFifteenMediumNumericGates (NumericGates innerQuery)

def selectedWCells (n : ℕ) : Finset (Grid n) :=
  (selectedCells n).filter
    (fun J => boxPolicy (gridBox n J) = wPolicy)

theorem mem_selectedWCells {n : ℕ} {J : Grid n} :
    J ∈ selectedWCells n ↔
      J ∈ selectedCells n ∧ boxPolicy (gridBox n J) = wPolicy := by
  simp [selectedWCells]

/-- The single physical fine-rectangle index set is finite. The rough
rank bound and fine precision are fixed by the common beta parameters. -/
abbrev WAtomKey (n : ℕ) (eta : ℚ) (nu0 epsilon : ℝ) :=
  Σ J : {J : Grid n // J ∈ selectedWCells n},
    Σ r : Fin (rankBound nu0 epsilon + 1),
      PresievedRoughGateMeshReserve.Grid r.val
        (roughMeshPrecision n eta nu0 epsilon)

instance WAtomKey_fintype (n : ℕ) (eta : ℚ) (nu0 epsilon : ℝ) :
    Fintype (WAtomKey n eta nu0 epsilon) := inferInstance

def atomOwner {n : ℕ} {eta : ℚ} {nu0 epsilon : ℝ}
    (key : WAtomKey n eta nu0 epsilon) : Box := gridBox n key.1.val

def atomUpperPrefix {n : ℕ} {eta : ℚ} {nu0 epsilon : ℝ}
    (key : WAtomKey n eta nu0 epsilon) : LogFour :=
  paddedOwnerCorner (atomOwner key) eta

def atomUpperRough {n : ℕ} {eta : ℚ} {nu0 epsilon : ℝ}
    (key : WAtomKey n eta nu0 epsilon) : Fin key.2.1.val → ℝ :=
  logPrimeMeshHi (nu0 * epsilon ^ 2)
    (U1011OriginalW16NearCapNative.cutoffExponent (atomOwner key) eta : ℝ)
    (roughMeshPrecision n eta nu0 epsilon) key.2.2

/-- These lists are selected once from the atom's fixed upper endpoints
and one HB length. The actual prime tuple and signed error are absent. -/
def atomGroups {n N : ℕ} {eta : ℚ} {nu0 epsilon : ℝ}
    (key : WAtomKey n eta nu0 epsilon) (A : ℝ) :
    Part3.ActualWThreeCapacityRun.Bins (Occ key.2.1.val) :=
  wGroups N (atomOwner key) eta (atomUpperPrefix key)
    (atomUpperRough key) A

/-- The actual finite bank's ellMax pays every W delta simultaneously.
The chart z is fixed after the bank and before N, x and all atom labels. -/
private theorem selected_W_cell_eventual {n : ℕ} {eta : ℚ}
    (heta : 0 < eta) {c z kappa0 : ℝ}
    (hc : 0 < c) (hz : 0 < z) (hzu : z ≤ 1 / 128)
    (hsmall : z ≤ (ellMax n eta : ℝ) / 512)
    (hk0 : 0 ≤ kappa0) (hk : kappa0 ≤ z)
    {J : Grid n} (hJ : J ∈ selectedWCells n) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - kappa0) ≤ x →
      (N : ℝ) ^ (1 - 2 * (cellDelta n eta J : ℝ)) ≤ x ^ (1 - 3 * z) ∧
      (N : ℝ) ^ (2 - 2 * (cellDelta n eta J : ℝ)) ≤ x ^ (2 - 3 * z) ∧
      (N : ℝ) ^ (2 - 39 * (cellDelta n eta J : ℝ) / 16) ≤ x ^ (2 - 3 * z) := by
  have hselected := (mem_selectedWCells.mp hJ).1
  have hdelta : 0 < (cellDelta n eta J : ℝ) := by
    exact_mod_cast selected_delta_pos eta heta J hselected
  have hmin : (ellMax n eta : ℝ) ≤ (cellDelta n eta J : ℝ) / 2 := by
    exact_mod_cast ellMax_le_cell eta J hselected
  have hreserve : 1024 * z ≤ (cellDelta n eta J : ℝ) := by linarith
  exact W_eventual_local_scale_payments hc hdelta hz hzu hreserve hk0 hk

/-- One threshold works for the entire finite W owner bank, before N,
local x, HB length, arithmetic mark, or signed discrepancy. -/
theorem selected_W_family_common_threshold {n : ℕ} {eta : ℚ}
    (heta : 0 < eta) {c z kappa0 : ℝ}
    (hc : 0 < c) (hz : 0 < z) (hzu : z ≤ 1 / 128)
    (hsmall : z ≤ (ellMax n eta : ℝ) / 512)
    (hk0 : 0 ≤ kappa0) (hk : kappa0 ≤ z) :
    ∃ N0 : ℕ, ∀ J ∈ selectedWCells n, ∀ N : ℕ, N0 ≤ N →
      ∀ x : ℝ, c * (N : ℝ) ^ (1 - kappa0) ≤ x →
      (N : ℝ) ^ (1 - 2 * (cellDelta n eta J : ℝ)) ≤ x ^ (1 - 3 * z) ∧
      (N : ℝ) ^ (2 - 2 * (cellDelta n eta J : ℝ)) ≤ x ^ (2 - 3 * z) ∧
      (N : ℝ) ^ (2 - 39 * (cellDelta n eta J : ℝ) / 16) ≤ x ^ (2 - 3 * z) := by
  let T : Grid n → ℕ := fun J =>
    if hJ : J ∈ selectedWCells n then
      Classical.choose (selected_W_cell_eventual heta hc hz hzu hsmall hk0 hk hJ)
    else 0
  refine ⟨(selectedWCells n).sup T, ?_⟩
  intro J hJ N hN x hx
  have hT : T J ≤ (selectedWCells n).sup T := Finset.le_sup hJ
  have hspec := Classical.choose_spec
    (selected_W_cell_eventual heta hc hz hzu hsmall hk0 hk hJ)
  have hTeq : T J =
      Classical.choose (selected_W_cell_eventual heta hc hz hzu hsmall hk0 hk hJ) :=
    dif_pos hJ
  have hTle : Classical.choose
      (selected_W_cell_eventual heta hc hz hzu hsmall hk0 hk hJ) ≤ N := by
    rw [←hTeq]
    exact hT.trans hN
  exact hspec N hTle x hx

/-- A physical nonzero W mark is classified into exactly one finite
prefix-owner and rough fine-cell atom. The arithmetic endpoint is included
literally; equality at a fine lower face remains in that half-open atom.
The selected atom's group lists are the lists that pass all four M gates. -/
theorem active_W_mark_in_selected_atom {n N r : ℕ} {eta : ℚ}
    {nu0 epsilon : ℝ} (hN : 1 < N) (heta : 0 < eta)
    (hnu0 : 0 < nu0) (heps : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu0)
    (E : ℕ × ℕ → Prop) {t : Four}
    (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hW : selectedPolicy n N t = wPolicy)
    (hr : r ∈ rowSupport n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2)) t)
    (hq : ImbalancedChen.P5Z.OriginalJointPresievedCompiler.jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
      ((N : ℝ) ^ (nu0 * epsilon)) E (fullPrefix t * r) ≠ 0)
    {x U z : ℝ} (hx : 1 < x) (hz : 0 < z) (hU : 0 < U)
    (hA1 : 1 ≤ innerQuery x U z)
    (hAupper : innerQuery x U z ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (hpay1 : (N : ℝ) ^ (1 - 2 *
      (delta wPolicy (ownerBox n N t) eta : ℝ)) ≤ x ^ (1 - 3 * z))
    (hpay2 : (N : ℝ) ^ (2 - 2 *
      (delta wPolicy (ownerBox n N t) eta : ℝ)) ≤ x ^ (2 - 3 * z))
    (hpay3 : (N : ℝ) ^ (2 - 39 *
      (delta wPolicy (ownerBox n N t) eta : ℝ) / 16) ≤ x ^ (2 - 3 * z)) :
    ∃ key : WAtomKey n eta nu0 epsilon,
      ∃ e d : ℕ,
        let ps := canonicalSlots N
          (Nat.ceil (U1011OriginalW16NearCapNative.Z (atomOwner key) eta N))
          ((N : ℝ) ^ (nu0 * epsilon ^ 2))
          (U1011OriginalW16NearCapNative.Z (atomOwner key) eta N) d
        let actual := physicalOccurrence t ps
        let out := atomGroups (N := N) key (innerQuery x U z)
        let a := (out.left.map actual).prod
        let b := (out.middle.map actual).prod
        let c := e * (out.right.map actual).prod
        owner n (coordinates N t) = key.1.val ∧
          ps.length = key.2.1.val ∧
          actualPrimeTupleLog N (slotVector ps) ∈
            PresievedRoughGateMeshReserve.cell (nu0 * epsilon ^ 2)
              (U1011OriginalW16NearCapNative.cutoffExponent (atomOwner key) eta : ℝ)
              (roughMeshPrecision n eta nu0 epsilon) key.2.2 ∧
          1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧
          a * b * c = fullPrefix t * r ∧
          NumericGates N x U (a : ℝ) (b : ℝ) (c : ℝ) (z / 2000) := by
  obtain ⟨e,d,j,hrank,her,hrough,ha,hb,hc,hprod,hM⟩ :=
    active_W_mark_fixed_four_M hN heta hnu0 heps heBudget E ht hW hr hq
      hx hz hU hA1 hAupper hpay1 hpay2 hpay3
  let J := owner n (coordinates N t)
  have htag := (Finset.mem_filter.mp ht).2
  have hselected : J ∈ selectedCells n := owner_mem_selected htag
  have hWJ : boxPolicy (gridBox n J) = wPolicy := hW
  have hJW : J ∈ selectedWCells n := (mem_selectedWCells).mpr ⟨hselected,hWJ⟩
  let key : WAtomKey n eta nu0 epsilon :=
    ⟨⟨J,hJW⟩,⟨⟨_,Nat.lt_succ_of_le hrank⟩,j⟩⟩
  refine ⟨key,e,d,?_,?_,?_,ha,hb,hc,hprod,hM⟩
  · rfl
  · rfl
  · simpa only [atomOwner, key, ownerBox] using hrough

end
end ImbalancedChen.P5Z.OriginalWSelectedAtomFamily
