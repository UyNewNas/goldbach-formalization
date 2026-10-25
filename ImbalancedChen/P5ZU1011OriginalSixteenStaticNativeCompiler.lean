import ImbalancedChen.P5ZU1011OriginalW16NativeGridCells
import ImbalancedChen.P5ZU1011OriginalSixteenStaticCellWinner

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Native FULL16 compiler for the STATIC corner winner. Policy, table atom,
native rational parameters and coefficient family are chosen by the rational
grid box BEFORE N and before the prime tuple. Policies0..14 use their actual
selected-mask fixed native family; policy15 uses the DISTINCT actual W fixed
native family. Only the common Rosser support/coefficient form is shared.

The tag0 fallback retains its actual original count. Endpoint scalar scores
are never identified with native density or cardinal bounds. No H248/native
density, AP, PP or switched-count licence is an assumption or conclusion.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenStaticNativeCompiler

noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenArithmeticEligibility
open U1011OriginalFifteenNativeGridCells
open P5U1011JointOverlap
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

def boxPolicy (B : Box) : Policy :=
  if hj : (U1011OriginalSixteenStaticCellWinner.chosenTag B).pred < 16 then
    ⟨(U1011OriginalSixteenStaticCellWinner.chosenTag B).pred,hj⟩ else first

theorem boxPolicy_certificate (B : Box) (h : U1011OriginalSixteenStaticCellWinner.chosenTag B ≠ 0) :
    U1011OriginalSixteenStaticCellWinner.chosenTag B = (boxPolicy B).val + 1 ∧
      wholeBoxEligibleTest (boxPolicy B) B = true := by
  cases ht : U1011OriginalSixteenStaticCellWinner.chosenTag B with
  | zero => exact (h ht).elim
  | succ j =>
    obtain ⟨hj,hcert⟩ := U1011OriginalSixteenStaticCellWinner.chosen_successor_data B j ht
    simpa only [boxPolicy,ht,Nat.pred_succ,dif_pos hj] using And.intro (rfl : j.succ = j+1) hcert

def rowNu (p : Policy) (B : Box) : ℚ :=
  if p.val < 15 then U1011OriginalFifteenFixedCellNative.nu p B else U1011OriginalW16FixedCellNative.nu B
def rowDelta (p : Policy) (B : Box) : ℚ :=
  if p.val < 15 then U1011OriginalFifteenFixedCellNative.delta p B else U1011OriginalW16FixedCellNative.delta B
def rowZ (p : Policy) (B : Box) (N : ℕ) : ℝ :=
  if p.val < 15 then U1011OriginalFifteenFixedCellNative.Z p B N else U1011OriginalW16FixedCellNative.Z B N
def rowD (p : Policy) (B : Box) (N : ℕ) : ℝ :=
  if p.val < 15 then U1011OriginalFifteenFixedCellNative.D p B N else U1011OriginalW16FixedCellNative.D B N
def rowSupport (p : Policy) (B : Box) (N : ℕ) : Finset ℕ :=
  actualSmallRosserSupport N (Nat.ceil (rowZ p B N)) (rowZ p B N)
def rowCoefficient (p : Policy) (B : Box) (N d : ℕ) : ℝ :=
  actualSmallRosserPlus N (Nat.ceil (rowZ p B N)) (rowZ p B N) (rowD p B N) d

private theorem not_mask_eq_W (p : Policy) (hp : ¬p.val < 15) : p = wPolicy := by
  apply Fin.ext
  have h := p.isLt
  change p.val = 15
  omega

theorem row_parameters (p : Policy) (B : Box) (hvalid : B.Valid) (hpositive : 0 < B.lo 3)
    (htest : wholeBoxEligibleTest p B = true) : rowNu p B < capLower p B ∧ 0 < rowDelta p B := by
  by_cases hp : p.val < 15
  · have h := U1011OriginalFifteenFixedCellNative.rational_parameters p hp B hvalid hpositive htest
    simpa only [rowNu,rowDelta,if_pos hp] using And.intro h.2.1 h.2.2.1
  · have heq := not_mask_eq_W p hp
    subst p
    have h := U1011OriginalW16FixedCellNative.rational_parameters B hvalid hpositive htest
    simpa only [rowNu,rowDelta,wPolicy,show ¬(15 : ℕ)<15 by omega,if_false] using And.intro h.2.1 h.2.2.1

theorem row_legality {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ U11Adaptive.source N E) (p : Policy) (B : Box) (hvalid : B.Valid)
    (hpositive : 0 < B.lo 3) (htest : wholeBoxEligibleTest p B = true)
    (hbox : coordinates N t ∈ B.region) :
    0 < rowZ p B N ∧ 1 < rowD p B N ∧ rowZ p B N ≤ (t.1.1 : ℝ) ∧ rowZ p B N ≤ rowD p B N := by
  by_cases hp : p.val < 15
  · simpa only [rowZ,rowD,if_pos hp] using U1011OriginalFifteenFixedCellNative.native_legality
      hN ht p hp B hvalid hpositive htest hbox
  · have heq := not_mask_eq_W p hp
    subst p
    simpa only [rowZ,rowD,wPolicy,show ¬(15 : ℕ)<15 by omega,if_false] using
      U1011OriginalW16FixedCellNative.native_legality hN ht B hvalid hpositive htest hbox

theorem row_active_full_modulus_cap {N d : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ U11Adaptive.source N E)
    (p : Policy) (B : Box) (hbox : coordinates N t ∈ B.region) (hd : rowCoefficient p B N d ≠ 0) :
    ((fullPrefix t*d : ℕ) : ℝ) < (N : ℝ) ^ ((rowNu p B : ℝ)-20*(rowDelta p B : ℝ)) := by
  by_cases hp : p.val < 15
  · have hd' : U1011OriginalFifteenFixedCellNative.coefficient p B N d ≠ 0 := by
      simpa only [rowCoefficient,rowZ,rowD,if_pos hp] using hd
    simpa only [rowNu,rowDelta,if_pos hp] using
      U1011OriginalFifteenFixedCellNative.active_full_modulus_cap hN ht p hp B hbox hd'
  · have heq := not_mask_eq_W p hp
    subst p
    have hd' : U1011OriginalW16FixedCellNative.coefficient B N d ≠ 0 := by
      simpa only [rowCoefficient,rowZ,rowD,wPolicy,show ¬(15 : ℕ)<15 by omega,if_false] using hd
    simpa only [rowNu,rowDelta,wPolicy,show ¬(15 : ℕ)<15 by omega,if_false] using
      (U1011OriginalW16FixedCellNative.active_full_modulus_cap hN ht B hbox hd').2

def ownerBox (n N : ℕ) (t : Four) : Box := gridBox n (owner n (coordinates N t))
def tupleTag (n N : ℕ) (t : Four) : ℕ := U1011OriginalSixteenStaticCellWinner.chosenTag (ownerBox n N t)
def selectedPolicy (n N : ℕ) (t : Four) : Policy := boxPolicy (ownerBox n N t)
def support (n N : ℕ) (t : Four) : Finset ℕ := rowSupport (selectedPolicy n N t) (ownerBox n N t) N
def coefficient (n N : ℕ) (t : Four) (d : ℕ) : ℝ := rowCoefficient (selectedPolicy n N t) (ownerBox n N t) N d
def Z (n N : ℕ) (t : Four) : ℝ := rowZ (selectedPolicy n N t) (ownerBox n N t) N
def D (n N : ℕ) (t : Four) : ℝ := rowD (selectedPolicy n N t) (ownerBox n N t) N
def ordinaryTuples (n N : ℕ) (E : ℕ × ℕ → Prop) : Finset Four :=
  (U11Adaptive.source N E).filter (fun t => tupleTag n N t ≠ 0)
def fallbackTuples (n N : ℕ) (E : ℕ × ℕ → Prop) : Finset Four :=
  (U11Adaptive.source N E).filter (fun t => tupleTag n N t = 0)

theorem compiled_row_static_on_cell (n N : ℕ) {t : Four} {j : Grid n}
    (ht : coordinates N t ∈ cell n j) :
    selectedPolicy n N t = boxPolicy (gridBox n j) ∧
      support n N t = rowSupport (boxPolicy (gridBox n j)) (gridBox n j) N ∧
      ∀ d, coefficient n N t d = rowCoefficient (boxPolicy (gridBox n j)) (gridBox n j) N d := by
  have ho := owner_eq_of_mem n ht
  simp only [selectedPolicy,ownerBox,support,coefficient,ho,true_and]

theorem compiled_legality {n N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ ordinaryTuples n N E) :
    0 < Z n N t ∧ 1 < D n N t ∧ Z n N t ≤ (t.1.1 : ℝ) ∧ Z n N t ≤ D n N t := by
  obtain ⟨hsource,htag⟩ := Finset.mem_filter.mp ht
  have hcert := (boxPolicy_certificate (ownerBox n N t) htag).2
  have hgeom := owner_mem n (U1011OriginalFifteenNativeGridDispatch.source_coordinates_cube hN hsource)
  exact row_legality hN hsource _ _ (gridBox_valid n _) (gridBox_lower_positive n _ 3)
    hcert (cell_subset_closed_box n _ hgeom)

theorem selected_branch_native_active {n N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ ordinaryTuples n N E) :
    (∃ hp : (selectedPolicy n N t).val < 15,
      (⟨(selectedPolicy n N t).val,hp⟩,owner n (coordinates N t)) ∈ activeCells n) ∨
      (selectedPolicy n N t = wPolicy ∧ owner n (coordinates N t) ∈ U1011OriginalW16NativeGridCells.WActiveCells n) := by
  have hcert := (boxPolicy_certificate (ownerBox n N t) (Finset.mem_filter.mp ht).2).2
  by_cases hp : (selectedPolicy n N t).val < 15
  · exact Or.inl ⟨hp,(mem_activeCells _).mpr hcert⟩
  · have heq := not_mask_eq_W (selectedPolicy n N t) hp
    exact Or.inr ⟨heq,(U1011OriginalW16NativeGridCells.mem_WActiveCells _).mpr (by simpa only [heq] using hcert)⟩

def main (n N : ℕ) (t : Four) : ℝ := trueLogarithmicIntegral N / (Nat.totient (fullPrefix t) : ℝ) *
  actualSmallRosserPlusDensity N (Nat.ceil (Z n N t)) (Z n N t) (D n N t)
def signedAP (n N : ℕ) (t : Four) : ℝ := ∑ d ∈ support n N t, coefficient n N t d *
  chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (fullPrefix t*d)
def signedCentre (n N : ℕ) (t : Four) : ℝ := ∑ d ∈ support n N t, coefficient n N t d *
  chenCentrePrimeAPCount N N (fullPrefix t*d)
def estimator (n N : ℕ) (t : Four) : ℝ := ∑ d ∈ support n N t, coefficient n N t d *
  (chenPrimeAPCount N N (fullPrefix t*d)-chenCentrePrimeAPCount N N (fullPrefix t*d))

theorem compiled_estimator_identity {n N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ ordinaryTuples n N E) :
    estimator n N t = main n N t + signedAP n N t - signedCentre n N t := by
  have hsource := (Finset.mem_filter.mp ht).1
  have hjoint := originalU11_mem_joint (by exact_mod_cast (Nat.le_of_lt hN)) hsource
  have hleg := compiled_legality hN ht
  have hZ : Z n N t ≤ (slots t 3 : ℝ) := by simpa only [slots,Matrix.cons_val_three] using hleg.2.2.1
  have hcop := fullPrefix_coprime_lowered_sieve hjoint hZ
  exact currentChen_quotient_actualRosser_plus_main_and_errors N (fullPrefix t)
    (Nat.ceil (Z n N t)) (Z n N t) (D n N t) (Nat.le_ceil _) hcop

theorem compiled_row_upper {n N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ ordinaryTuples n N E) :
    U11Adaptive.weight N t ≤ main n N t + signedAP n N t - signedCentre n N t := by
  have hsource := (Finset.mem_filter.mp ht).1
  have hleg := compiled_legality hN ht
  have h12 := (U11LoweredRosser.original_carrier_order (by exact_mod_cast (Nat.le_of_lt hN)) hsource).2.2.2.2.1
  have hz2 : Z n N t ≤ (t.1.2 : ℝ) := hleg.2.2.1.trans (by exact_mod_cast h12.le)
  have hweight : U11Adaptive.weight N t =
      ((chenSiftedQuotientPrimeSource N (fullPrefix t) (t.1.2 : ℝ)).card : ℝ) := by
    rw [fullPrefix_eq_multiplier]
    rfl
  have hcount : U11Adaptive.weight N t ≤ ((chenSiftedQuotientPrimeSource N (fullPrefix t) (Z n N t)).card : ℝ) := by
    rw [hweight]
    exact_mod_cast Finset.card_le_card (U11LoweredRosser.siftedSource_subset_lowered N _ _ _ hz2)
  have hupper := currentChen_quotient_actualRosser_upper N (fullPrefix t) (Nat.ceil (Z n N t))
    (Z n N t) (D n N t) (Nat.le_ceil _) hleg.2.1 hleg.2.2.2
  exact (hcount.trans hupper).trans_eq (compiled_estimator_identity hN ht)

theorem source_partition (n N : ℕ) (E : ℕ × ℕ → Prop) (F : Four → ℝ) :
    (∑ t ∈ U11Adaptive.source N E,F t) = (∑ t ∈ fallbackTuples n N E,F t) +
      ∑ t ∈ ordinaryTuples n N E,F t :=
  (Finset.sum_filter_add_sum_filter_not (U11Adaptive.source N E) (fun t => tupleTag n N t=0) F).symm

theorem original_source_upper {n N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop) :
    currentChenUpsilon11 N E ≤ (∑ t ∈ fallbackTuples n N E,U11Adaptive.weight N t) +
      ∑ t ∈ ordinaryTuples n N E,main n N t+signedAP n N t-signedCentre n N t := by
  rw [U11Adaptive.current_eq_sum_weight,source_partition n N E]
  apply add_le_add_left
  exact Finset.sum_le_sum (fun t ht => compiled_row_upper hN ht)

end
end ImbalancedChen.P5Z.U1011OriginalSixteenStaticNativeCompiler
