import ImbalancedChen.P5ZU1011CompactLogIntervalSmoothing
import ImbalancedChen.P5ZU1011OriginalPairedRowPrimeTests

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual adopted 17572-row mask, with its original t,u orientation,
receives compact multiplicatively separated log weights. Mixed derivatives
are the literal iterated scalar derivatives, not an assumed test norm.
This smooths the OUTER ROW mask only: order walls and policy-cell walls
still require their own geometric decomposition before strong distribution.
-/
namespace ImbalancedChen.P5Z.U1011AdoptedRowSmoothTensor
noncomputable section
open Set
open Certificates.PairedV2
open U1011CompactLogIntervalSmoothing
open P4B

abbrev Row := FullMask.Row

def loT (r : Row) : ℝ := tLower (FullMask.indices r).1
def hiT (r : Row) : ℝ := tUpper (FullMask.indices r).1
def loU (r : Row) : ℝ := uLower (FullMask.indices r).2
def hiU (r : Row) : ℝ := uUpper (FullMask.indices r).2

def atom (inner : Bool) (δ : ℝ) (r : Row) (x : ℝ × ℝ) : ℝ :=
  weight inner δ (loT r) (hiT r) x.1 * weight inner δ (loU r) (hiU r) x.2

def rowIndicator (r : Row) (x : ℝ × ℝ) : ℝ :=
  if x ∈ FullMask.P1E0E1.pairCell r then 1 else 0

theorem rowIndicator_eq_product (r : Row) (x : ℝ × ℝ) :
    rowIndicator r x = literal (loT r) (hiT r) x.1 * literal (loU r) (hiU r) x.2 := by
  have hcell : x ∈ FullMask.P1E0E1.pairCell r ↔
      (loT r ≤ x.1 ∧ x.1 < hiT r) ∧ (loU r ≤ x.2 ∧ x.2 < hiU r) := by
    simp only [FullMask.P1E0E1.pairCell, mem_setOf_eq, loT, hiT, loU, hiU]
    tauto
  by_cases ht : loT r ≤ x.1 ∧ x.1 < hiT r
  <;> by_cases hu : loU r ≤ x.2 ∧ x.2 < hiU r
  <;> simp [rowIndicator, hcell, literal, ht, hu]

theorem atom_bounds (inner : Bool) (δ : ℝ) (r : Row) (x : ℝ × ℝ) :
    0 ≤ atom inner δ r x ∧ atom inner δ r x ≤ 1 := by
  obtain ⟨h0, h1⟩ := bounds inner δ (loT r) (hiT r) x.1
  obtain ⟨g0, g1⟩ := bounds inner δ (loU r) (hiU r) x.2
  exact ⟨mul_nonneg h0 g0, (mul_le_mul h1 g1 g0 zero_le_one).trans_eq (one_mul 1)⟩

theorem inner_le_row {δ : ℝ} (hδ : 0 < δ) (r : Row) (x : ℝ × ℝ) :
    atom true δ r x ≤ rowIndicator r x := by
  rw [rowIndicator_eq_product]
  apply mul_le_mul (inner_le_literal hδ _ _ _) (inner_le_literal hδ _ _ _)
    (bounds true δ (loU r) (hiU r) x.2).1
  unfold literal
  split_ifs <;> norm_num

theorem row_le_outer {δ : ℝ} (hδ : 0 < δ) (r : Row) (x : ℝ × ℝ) :
    rowIndicator r x ≤ atom false δ r x := by
  rw [rowIndicator_eq_product]
  apply mul_le_mul (literal_le_outer hδ _ _ _) (literal_le_outer hδ _ _ _)
  · unfold literal
    split_ifs <;> norm_num
  · exact (bounds false δ (loT r) (hiT r) x.1).1

theorem contDiff_atom (inner : Bool) (δ : ℝ) (r : Row) {n : ℕ∞} :
    ContDiff ℝ n (atom inner δ r) :=
  ((contDiff_weight inner δ (loT r) (hiT r)).comp contDiff_fst).mul
    ((contDiff_weight inner δ (loU r) (hiU r)).comp contDiff_snd)

/-- The compact support is genuine on the entire real pair plane. -/
theorem hasCompactSupport_atom {δ : ℝ} (hδ : 0 < δ) (inner : Bool) (r : Row) :
    HasCompactSupport (atom inner δ r) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc : IsCompact (Icc (loT r - δ) (hiT r + δ))).prod
      (isCompact_Icc : IsCompact (Icc (loU r - δ) (hiU r + δ))))
  intro x hx
  have hn : atom inner δ r x ≠ 0 := hx
  have hnon := mul_ne_zero_iff.mp hn
  have hcoord (a b z : ℝ) (hz : weight inner δ a b z ≠ 0) :
      z ∈ Icc (a - δ) (b + δ) := by
    have hs : 0 ≤ shift inner δ := by cases inner <;> simp [shift, hδ.le]
    have hl : smoothGateUpperStep δ (z - a - shift inner δ) ≠ 0 :=
      (mul_ne_zero_iff.mp hz).1
    have hu : smoothGateUpperStep δ (b - z - shift inner δ) ≠ 0 :=
      (mul_ne_zero_iff.mp hz).2
    have h1 := P4B.smoothGateUpperStep_nonzero_support hδ hl
    have h2 := P4B.smoothGateUpperStep_nonzero_support hδ hu
    constructor <;> linarith
  exact ⟨hcoord _ _ _ hnon.1, hcoord _ _ _ hnon.2⟩

/-- Actual mixed derivative: first in t, then in u. -/
def mixedJet (i j : ℕ) (inner : Bool) (δ : ℝ) (r : Row) (x : ℝ × ℝ) : ℝ :=
  iteratedDeriv j (fun u => iteratedDeriv i (fun t => atom inner δ r (t, u)) x.1) x.2

theorem mixedJet_eq_tensor (i j : ℕ) (inner : Bool) (δ : ℝ) (r : Row) (x : ℝ × ℝ) :
    mixedJet i j inner δ r x =
      iteratedDeriv i (weight inner δ (loT r) (hiT r)) x.1 *
        iteratedDeriv j (weight inner δ (loU r) (hiU r)) x.2 := by
  simp only [mixedJet, atom, iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field]

/-- Fixed mixed-order budget, uniform in every actual row and all widths.
No row-dependent derivative constant or N-dependent modulus is hidden. -/
theorem exists_mixedJet_budget (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (inner : Bool) (δ : ℝ), 0 < δ → ∀ (r : Row) (x : ℝ × ℝ),
      |mixedJet i j inner δ r x| ≤ C / δ ^ (i + j) := by
  obtain ⟨A, hA, ha⟩ := exists_derivative_budget i
  obtain ⟨B, hB, hb⟩ := exists_derivative_budget j
  refine ⟨A * B, mul_nonneg hA hB, ?_⟩
  intro inner δ hδ r x
  rw [mixedJet_eq_tensor, abs_mul]
  calc
    _ ≤ (A / δ ^ i) * (B / δ ^ j) :=
      mul_le_mul (ha inner δ hδ _ _ _) (hb inner δ hδ _ _ _)
        (abs_nonneg _) (div_nonneg hA (pow_nonneg hδ.le i))
    _ = (A * B) / δ ^ (i + j) := by rw [pow_add]; ring

/-- The SAME physical prime-log point used by the original native mask.
Native (p3,p4) is passed in increasing order, hence read once as (p4,p3). -/
def nativeAtom (inner : Bool) (δ : ℝ) (r : Row) (N : ℕ) (p : ℕ × ℕ) : ℝ :=
  atom inner δ r (FullMask.P1E0E1.primePairCoordinates (N : ℝ) p)

theorem nativeAtom_exact_log_pullback (inner : Bool) (δ : ℝ) (r : Row)
    (N : ℕ) (p : Fin 4 → ℕ) :
    nativeAtom inner δ r N (p 1, p 0) =
      atom inner δ r (U1011OriginalPairedRowPrimeTests.outerPair (actualPrimeTupleLog N p)) := rfl

end
end ImbalancedChen.P5Z.U1011AdoptedRowSmoothTensor
