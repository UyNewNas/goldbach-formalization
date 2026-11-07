import ImbalancedChen.Part3OriginalPoissonFrequencyOwnership
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.
Actual primitive-q source modes are extended by zero, and the owned
half-open rough windows are reconciled with the physical closed windows.
The resulting cell is the existing constructed block's full rawBox sum,
including every nonclean complete-lcm/root term.
-/

noncomputable section
open Classical Finset Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumPhysicalE3RowReindex
open ImbalancedChen.Part3.OriginalMediumPhysicalQAbel
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalTrimmedCleanE3Assembly20261028
open ImbalancedChen.Part3.OriginalSourcePoissonFamilyDictionary20261028
open ImbalancedChen.Part3.OriginalPoissonFrequencyOwnership20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumGenuinePoissonFibre20261028

namespace ImbalancedChen.Part3.OriginalPoissonCarrierCells20261028

attribute [local instance] Classical.propDecidable

/-- The original primitive-q carrier, extended by actual zero. -/
def maskedMode (atom : MediumAtom) (z y : ℝ) (k : Key)
    (v : FibreIndex) (h : ℤ) : ℂ :=
  if v.1.1.Coprime atom.residue.natAbs then sourceMode atom z y k v h else 0

theorem maskedMode_eq_actual_family_term {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (q r s n1 n2 : ℕ) (h : ℤ) :
    maskedMode atom z y k (sourceFibre q small r s n1 n2) h =
      coefficientPhysicalTerm (poissonAtlasBlock atom z y k hA Csep j small hd negative)
        (physicalIndex q r s n1 n2 h) := by
  by_cases hq : q.Coprime atom.residue.natAbs
  · rw [maskedMode, if_pos hq]
    exact sourceMode_eq_actual_family_term atom z y k hA Csep j small hd negative
      q r s n1 n2 h hq
  · simp only [maskedMode, sourceFibre, if_neg hq]
    unfold coefficientPhysicalTerm
    simp only [physicalIndex, poissonAtlasBlock_atom, hq, false_and, if_false]

theorem maskedMode_zero_left {atom : MediumAtom} {z y : ℝ} {k : Key}
    {q small r s n1 n2 : ℕ} {h : ℤ} (hr : r ∉ dyadicWindow k.w) :
    maskedMode atom z y k (sourceFibre q small r s n1 n2) h = 0 := by
  unfold maskedMode
  split_ifs
  · exact sourceMode_zero_of_left_rough_outside atom z y k q small r s n1 n2 h hr
  · rfl

theorem maskedMode_zero_right {atom : MediumAtom} {z y : ℝ} {k : Key}
    {q small r s n1 n2 : ℕ} {h : ℤ} (hs : s ∉ dyadicWindow k.w) :
    maskedMode atom z y k (sourceFibre q small r s n1 n2) h = 0 := by
  unfold maskedMode
  split_ifs
  · exact sourceMode_zero_of_right_rough_outside atom z y k q small r s n1 n2 h hs
  · rfl

theorem maskedMode_zero_d {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) {z y : ℝ} {k : Key}
    {q small r s n1 n2 : ℕ} {h : ℤ}
    (hd : ¬small.Coprime atom.residue.natAbs) :
    maskedMode atom z y k (sourceFibre q small r s n1 n2) h = 0 := by
  unfold maskedMode
  split_ifs
  · exact sourceMode_zero_of_nonprimitive_d hA z y k q small r s n1 n2 h hd
  · rfl

/-- Integer dyadic ownership lies in the physical closed rough carrier. -/
theorem ownedRough_subset_closed (k : Key) :
    dyadicWindow k.w ⊆ factorCarrier (keyR k) := by
  intro r hr
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hr
  have hcast : (2 : ℝ) * (((2 : ℕ) ^ k.w : ℕ) : ℝ) =
      (((2 : ℕ) ^ (k.w + 1) : ℕ) : ℝ) := by
    rw [pow_succ]
    push_cast
    ring
  change r ∈ Finset.Icc (Nat.ceil ((((2 : ℕ) ^ k.w : ℕ) : ℝ)))
    (Nat.floor (2 * ((((2 : ℕ) ^ k.w : ℕ) : ℝ))))
  rw [Nat.ceil_natCast, hcast, Nat.floor_natCast]
  exact Finset.mem_Icc.mpr ⟨hlo, hhi.le⟩

/-- One actual signed-q/d cell; only its rough carrier is a parameter. -/
def modeCell (atom : MediumAtom) (z y : ℝ) (k : Key)
    (rough : Finset ℕ) (q small : ℕ) (negative : Bool) : ℂ :=
  ∑ r ∈ rough, ∑ s ∈ rough,
    ∑ n1 ∈ atom.alphaCarrier, ∑ n2 ∈ atom.alphaCarrier,
      ∑ h ∈ signedHWindow (keyRealH atom k) negative,
        maskedMode atom z y k (sourceFibre q small r s n1 n2) h

/-- The closed upper endpoints add no mass: actual lambdaTrim supplies
the zero, independently on the left and right rough labels. -/
theorem modeCell_closed_eq_owned (atom : MediumAtom) (z y : ℝ)
    (k : Key) (q small : ℕ) (negative : Bool) :
    modeCell atom z y k (factorCarrier (keyR k)) q small negative =
      modeCell atom z y k (dyadicWindow k.w) q small negative := by
  unfold modeCell
  have hsub := ownedRough_subset_closed k
  calc
    _ = ∑ r ∈ dyadicWindow k.w, ∑ s ∈ factorCarrier (keyR k),
        ∑ n1 ∈ atom.alphaCarrier, ∑ n2 ∈ atom.alphaCarrier,
          ∑ h ∈ signedHWindow (keyRealH atom k) negative,
            maskedMode atom z y k (sourceFibre q small r s n1 n2) h := by
      symm
      apply Finset.sum_subset hsub
      intro r hr hrnot
      simp_rw [maskedMode_zero_left hrnot]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      symm
      apply Finset.sum_subset hsub
      intro s hs hsnot
      simp_rw [maskedMode_zero_right hsnot]
      simp

theorem modeCell_zero_d {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key)
    (rough : Finset ℕ) (q small : ℕ) (negative : Bool)
    (hd : ¬small.Coprime atom.residue.natAbs) :
    modeCell atom z y k rough q small negative = 0 := by
  unfold modeCell
  simp_rw [maskedMode_zero_d hA hd]
  simp

/-- This equality reaches the existing rawBox, not a new definition
called the physical source. All original six coordinates are retained. -/
theorem blockRaw_eq_q_cells {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    coefficientRawSum (poissonAtlasBlock atom z y k hA Csep j small hd negative) =
      ∑ q ∈ qPiece atom.Q1 j,
        modeCell atom z y k (dyadicWindow k.w) q small negative := by
  unfold coefficientRawSum
  simp only [rawBox, Finset.sum_product]
  change (∑ q ∈ qPiece atom.Q1 j, ∑ r ∈ factorCarrier (keyR k),
    ∑ s ∈ factorCarrier (keyR k), ∑ n1 ∈ atom.alphaCarrier,
    ∑ n2 ∈ atom.alphaCarrier,
    ∑ h ∈ signedHWindow (keyRealH atom k) negative,
      coefficientPhysicalTerm (poissonAtlasBlock atom z y k hA Csep j small hd negative)
        (physicalIndex q r s n1 n2 h)) = _
  simp_rw [← maskedMode_eq_actual_family_term atom z y k hA Csep j small hd negative]
  change (∑ q ∈ qPiece atom.Q1 j,
    modeCell atom z y k (factorCarrier (keyR k)) q small negative) = _
  simp_rw [modeCell_closed_eq_owned]

end ImbalancedChen.Part3.OriginalPoissonCarrierCells20261028
