import ImbalancedChen.P5ActualNativeSigmaPrimeProductAtoms
import ImbalancedChen.P5ActualRankLogAtomEuler

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
The atom bank below is read from the literal low/base/removed-row sets in
the production FULL16 sigma expansion, at its active native owners.
It records physical prefix rank FOUR only. It is not an inventory of the
independent external PP test word u, nor of an adopted lower CapPlan.
Multiplicity and signs remain in smooth_sigma_primeProduct_box_atoms;
this finite set is used only to select one shared derivative bound.
-/
namespace ImbalancedChen.P5Z.ActualNativePhysicalAtomOrderedFields
noncomputable section
open Classical Set
open scoped BigOperators
open U11Integral U11Canonical
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenAffineState
open U1011OriginalMaskSmoothBoxRealization
open U1011NativeMaskPhysicalBoxAtoms U1011NativeUnmaskedLowBoxAtoms
open U1011FourDimensionalSmoothBoxAtoms U1011AffineSmoothBoxCover
open U1011OriginalSixteenNativeHarmonic

abbrev AtomKey (n : ℕ) := Bool × Grid n

def actualPhysicalAtomBank (inner : Bool) (S : Finset Row) (m n : ℕ) :
    Finset (AtomKey n) :=
  Finset.univ.filter (fun key => ∃ k : Grid m,
    U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) ≠ 0 ∧
    ∃ s : State,
      (key.1 = inner ∧
        (key.2 ∈ (if inner then innerCells (lowGates s m k) n
          else outerCells (lowGates s m k) n) ∨
         key.2 ∈ (if inner then innerCells (baseGates s m k) n
          else outerCells (baseGates s m k) n))) ∨
      (key.1 = !inner ∧ ∃ row ∈ S,
        key.2 ∈ (if inner then outerCells (removedGates s m k row) n
          else innerCells (removedGates s m k row) n)))

theorem low_occurrence_mem (inner : Bool) (S : Finset Row) (m n : ℕ)
    (k : Grid m) (s : State)
    (hk : U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) ≠ 0)
    (j : Grid n) (hj : j ∈ (if inner then innerCells (lowGates s m k) n
      else outerCells (lowGates s m k) n)) :
    (inner, j) ∈ actualPhysicalAtomBank inner S m n := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, k, hk, s, Or.inl ⟨rfl, Or.inl hj⟩⟩

theorem base_occurrence_mem (inner : Bool) (S : Finset Row) (m n : ℕ)
    (k : Grid m) (s : State)
    (hk : U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) ≠ 0)
    (j : Grid n) (hj : j ∈ (if inner then innerCells (baseGates s m k) n
      else outerCells (baseGates s m k) n)) :
    (inner, j) ∈ actualPhysicalAtomBank inner S m n := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, k, hk, s, Or.inl ⟨rfl, Or.inr hj⟩⟩

theorem removed_occurrence_mem (inner : Bool) (S : Finset Row) (m n : ℕ)
    (k : Grid m) (s : State)
    (hk : U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) ≠ 0)
    (row : Row) (hrow : row ∈ S) (j : Grid n)
    (hj : j ∈ (if inner then outerCells (removedGates s m k row) n
      else innerCells (removedGates s m k row) n)) :
    (!inner, j) ∈ actualPhysicalAtomBank inner S m n := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, k, hk, s, Or.inr ⟨rfl, row, hrow, hj⟩⟩

theorem actual_bank_native_branch_licence (inner : Bool) (S : Finset Row)
    (m n : ℕ) (key : AtomKey n)
    (hkey : key ∈ actualPhysicalAtomBank inner S m n) :
    ∃ k : Grid m,
      U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) ≠ 0 ∧
      U1011OriginalSixteenPolicyBank.BoxCertificates.wholeBoxEligibleTest
        (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox m k))
        (gridBox m k) = true := by
  obtain ⟨k, hk, hs⟩ := (Finset.mem_filter.mp hkey).2
  exact ⟨k, hk,
    (U1011OriginalSixteenStaticNativeCompiler.boxPolicy_certificate _ hk).2⟩

def atomProfile (δ : ℝ) {n : ℕ} (key : AtomKey n) (N : ℕ) :
    (Fin 4 → ℝ) → ℝ :=
  ActualRankLogAtomEuler.profile key.1 δ (lower : ℝ) (upper : ℝ) n key.2 N

-- Both sides preexist independently: the production physicalBoxAtom,
-- and the peer log-prime profile with a real smooth zero extension.
theorem physicalBoxAtom_eq_profile {N : ℕ} (hN : 2 ≤ N)
    (δ : ℝ) (n : ℕ) (key : AtomKey n) (m : ℕ) (eta : ℚ)
    (k : Grid m) (q : ℕ) :
    physicalBoxAtom key.1 δ n key.2 m N eta k q =
      ∑ p ∈ boxTuples N, atomProfile δ key N (fun i => (p i : ℝ)) *
        residualPhysicalCoefficient m N eta k p q := by
  unfold physicalBoxAtom physicalTest
  apply Finset.sum_congr rfl
  intro p hp
  have hpPos : ∀ i, 0 < p i :=
    fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
  have he := ActualRankLogAtomEuler.profile_integer_atom
    key.1 δ (lower : ℝ) (upper : ℝ) key.2 hN p hpPos
  change _ = ActualRankLogAtomEuler.profile key.1 δ
    (lower : ℝ) (upper : ℝ) n key.2 N (fun i => (p i : ℝ)) * _
  rw [he]
  rfl

theorem atomProfile_smooth {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (key : AtomKey n) (N : ℕ) : ContDiff ℝ ∞ (atomProfile δ key N) :=
  ActualRankLogAtomEuler.profile_global_smooth hδ key.1 key.2 N

theorem atomProfile_zero_below_native_floor {δ : ℝ} (hδ : 0 < δ)
    {n N : ℕ} (hN : 2 ≤ N) (key : AtomKey n) (p : Fin 4 → ℝ)
    (i : Fin 4)
    (hi : p i ≤ Real.exp (Real.log (N : ℝ) *
      (logPrimeMeshLo (lower : ℝ) (upper : ℝ) n key.2 i - δ))) :
    atomProfile δ key N p = 0 :=
  ActualRankLogAtomEuler.profile_zero_below_floor hδ key.1 key.2 hN p i hi

theorem atomProfile_amplitude (δ : ℝ) {n : ℕ} (key : AtomKey n)
    (N : ℕ) (p : Fin 4 → ℝ) :
    0 ≤ atomProfile δ key N p ∧ atomProfile δ key N p ≤ 1 := by
  unfold atomProfile ActualRankLogAtomEuler.profile
  split_ifs
  · exact PresievedRoughSmoothBoxAtoms.atom_bounds _ _ _ _ _ _ _
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨le_rfl, zero_le_one⟩

theorem actual_physical_bank_ordered_budget {δ : ℝ} (hδ : 0 < δ)
    (inner : Bool) (S : Finset Row) (m n order : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ key ∈ actualPhysicalAtomBank inner S m n,
      ∀ N (w : List (Fin 4)) p, w.length ≤ order →
        |AdmissibleAllRankIntegerGeometricFamily.eulerWord w
          (atomProfile δ key N) p| ≤ (C : ℝ) := by
  obtain ⟨C, hC, hb⟩ :=
    ActualRankLogAtomEuler.finite_rank_bank_mixedEuler
      (a := (lower : ℝ)) (b := (upper : ℝ)) hδ 4 n order
  refine ⟨C, hC, ?_⟩
  intro key hkey N w p hw
  let peerKey : ActualRankLogAtomEuler.AtomKey 4 n :=
    (key.1, ⟨⟨4, by omega⟩, key.2⟩)
  exact hb peerKey N w p hw

end
end ImbalancedChen.P5Z.ActualNativePhysicalAtomOrderedFields
