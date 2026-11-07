import ImbalancedChen.Part3MediumPrimitivePsiSource
import Mathlib.Tactic

/-! Source only; uncompiled; zero formal credit.
Actual same-d, primitive-q, same-paperPsi S1/S2/S3 pair carriers.
Diagonal, off-diagonal and single-zero restoration terms are all retained.
No off-diagonal estimate or zero-mode cancellation is assumed.
-/
namespace ImbalancedChen.Part3.MediumLiteralS3Stages20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3.MediumPrimitivePsiSource20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumLiteralS3Deleted20261028
open ImbalancedChen.Part3.MediumDeletedIndicatorShift20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028

abbrev PairIndex := OuterIndex × ((ℕ × ℕ) × (ℕ × ℕ))

def pairedCarrier (atom : MediumAtom) (k : Key) : Finset PairIndex :=
  primitiveSmoothOuter atom k ×ˢ (innerCarrier atom k ×ˢ innerCarrier atom k)

def oldIndex (t : PairIndex) : Index :=
  ⟨t.1.1, t.1.2.1, t.2.1.1, t.2.2.1, t.2.1.2, t.2.2.2, t.1.2.2⟩

def pairCoefficient (atom : MediumAtom) (z y : ℝ) (k : Key) (t : PairIndex) : ℂ :=
  (jointPsi atom t.1 : ℂ) * lambdaTrim atom z y k t.1.2.1 t.2.1.1 *
    star (lambdaTrim atom z y k t.1.2.1 t.2.2.1) *
    atom.alpha t.2.1.2 * star (atom.alpha t.2.2.2)

def S1Term (atom : MediumAtom) (z y : ℝ) (k : Key) (t : PairIndex) : ℂ :=
  pairCoefficient atom z y k t *
    literalMeanKernel atom t.1.1 t.1.2.1 t.2.1.1 t.2.1.2 t.1.2.2 *
    star (literalMeanKernel atom t.1.1 t.1.2.1 t.2.2.1 t.2.2.2 t.1.2.2)

def S2Term (atom : MediumAtom) (z y : ℝ) (k : Key) (t : PairIndex) : ℂ :=
  pairCoefficient atom z y k t * firstDeleted atom.residue (oldIndex t) *
    star (literalMeanKernel atom t.1.1 t.1.2.1 t.2.2.1 t.2.2.2 t.1.2.2)

def S3DeletedTerm (atom : MediumAtom) (z y : ℝ) (k : Key) (t : PairIndex) : ℂ :=
  pairCoefficient atom z y k t * firstDeleted atom.residue (oldIndex t) *
    star (secondDeleted atom.residue (oldIndex t))

def primitiveS1 (atom : MediumAtom) (z y : ℝ) (k : Key) : ℝ :=
  ∑ t ∈ primitiveSmoothOuter atom k, jointPsi atom t *
    ‖principalRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2

def primitiveS2 (atom : MediumAtom) (z y : ℝ) (k : Key) : ℝ :=
  ∑ t ∈ primitiveSmoothOuter atom k, jointPsi atom t *
    (progressionRow atom z y k t.1 t.2.1 t.2.2 *
      star (principalRow atom z y k t.1 t.2.1 t.2.2)).re

def primitiveS3 (atom : MediumAtom) (z y : ℝ) (k : Key) : ℝ :=
  ∑ t ∈ primitiveSmoothOuter atom k, jointPsi atom t *
    ‖progressionRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2

theorem primitive_dispersion_identity (atom : MediumAtom) (z y : ℝ) (k : Key) :
    primitiveQuadratic atom z y k =
      primitiveS3 atom z y k - 2 * primitiveS2 atom z y k + primitiveS1 atom z y k := by
  unfold primitiveQuadratic primitiveS1 primitiveS2 primitiveS3
  simp_rw [preliminaryRow_eq_progression_sub_principal]
  simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, starRingEnd_apply]
  rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  ring

/-- Each of the actual signed carriers is expanded, not assumed to be
some independent primitive array. In particular no q endpoint is lost. -/
theorem primitiveS1_eq_paired (atom : MediumAtom) (z y : ℝ) (k : Key) :
    (primitiveS1 atom z y k : ℂ) = ∑ t ∈ pairedCarrier atom k, S1Term atom z y k t := by
  unfold primitiveS1 pairedCarrier S1Term pairCoefficient
  rw [Complex.ofReal_sum]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, sum_product]
  apply sum_congr rfl
  intro t ht
  rw [show ((‖principalRow atom z y k t.1 t.2.1 t.2.2‖ : ℂ) ^ 2) =
      principalRow atom z y k t.1 t.2.1 t.2.2 *
        star (principalRow atom z y k t.1 t.2.1 t.2.2) from (Complex.mul_conj' _).symm]
  unfold principalRow
  rw [star_sum, sum_mul_sum]
  simp only [mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  simp only [star_mul]
  ring

theorem primitiveS2_eq_paired_re (atom : MediumAtom) (z y : ℝ) (k : Key) :
    primitiveS2 atom z y k = (∑ t ∈ pairedCarrier atom k, S2Term atom z y k t).re := by
  have h : (∑ t ∈ primitiveSmoothOuter atom k, (jointPsi atom t : ℂ) *
      (progressionRow atom z y k t.1 t.2.1 t.2.2 *
        star (principalRow atom z y k t.1 t.2.1 t.2.2))) =
      ∑ t ∈ pairedCarrier atom k, S2Term atom z y k t := by
    unfold pairedCarrier S2Term pairCoefficient
    simp only [sum_product]
    apply sum_congr rfl
    intro t ht
    unfold progressionRow principalRow
    rw [star_sum, sum_mul_sum]
    simp only [mul_sum]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    simp only [oldIndex, firstDeleted, star_mul]
    ring
  rw [← h]
  simp [primitiveS2, Complex.mul_re]

theorem primitiveS3_eq_paired_deleted (atom : MediumAtom) (z y : ℝ) (k : Key) :
    (primitiveS3 atom z y k : ℂ) = ∑ t ∈ pairedCarrier atom k, S3DeletedTerm atom z y k t := by
  unfold primitiveS3 pairedCarrier S3DeletedTerm pairCoefficient
  rw [Complex.ofReal_sum]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, sum_product]
  apply sum_congr rfl
  intro t ht
  rw [show ((‖progressionRow atom z y k t.1 t.2.1 t.2.2‖ : ℂ) ^ 2) =
      progressionRow atom z y k t.1 t.2.1 t.2.2 *
        star (progressionRow atom z y k t.1 t.2.1 t.2.2) from (Complex.mul_conj' _).symm]
  unfold progressionRow
  rw [star_sum, sum_mul_sum]
  simp only [mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  simp only [oldIndex, firstDeleted, secondDeleted, star_mul]
  ring

def diagonalCarrier (atom : MediumAtom) (k : Key) : Finset PairIndex :=
  (pairedCarrier atom k).filter (fun t => (oldIndex t).n1 = (oldIndex t).n2)

def offDiagonalCarrier (atom : MediumAtom) (k : Key) : Finset PairIndex :=
  (pairedCarrier atom k).filter (fun t => (oldIndex t).n1 ≠ (oldIndex t).n2)

theorem S3_exact_diagonal_offDiagonal (atom : MediumAtom) (z y : ℝ) (k : Key) :
    (primitiveS3 atom z y k : ℂ) =
      (∑ t ∈ diagonalCarrier atom k, S3DeletedTerm atom z y k t) +
      ∑ t ∈ offDiagonalCarrier atom k, S3DeletedTerm atom z y k t := by
  rw [primitiveS3_eq_paired_deleted]
  unfold diagonalCarrier offDiagonalCarrier
  simp only [sum_filter]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  by_cases h : (oldIndex t).n1 = (oldIndex t).n2 <;> simp [h]

theorem paired_m_positive {atom : MediumAtom} {k : Key} (hM : 0 < atom.V)
    {t : PairIndex} (ht : t ∈ pairedCarrier atom k) : 0 < (oldIndex t).m := by
  have ho := (mem_product.mp ht).1
  have hbase := (mem_filter.mp ho).1
  have hm := (mem_product.mp (mem_product.mp hbase).2).2
  have hlo := (mem_Icc.mp hm).1
  have hceilR : (0 : ℝ) < Nat.ceil (atom.V / 2) :=
    lt_of_lt_of_le (by linarith) (Nat.le_ceil _)
  have hceil : 0 < Nat.ceil (atom.V / 2) := by exact_mod_cast hceilR
  exact hceil.trans_le hlo

def S3FullTerm (atom : MediumAtom) (z y : ℝ) (k : Key) (t : PairIndex) : ℂ :=
  pairCoefficient atom z y k t *
    fullIndicator atom.residue (((oldIndex t).q * (oldIndex t).d) * (oldIndex t).r)
      (oldIndex t).n1 (oldIndex t).m *
    star (fullIndicator atom.residue (((oldIndex t).q * (oldIndex t).d) * (oldIndex t).s)
      (oldIndex t).n2 (oldIndex t).m)

def firstZeroTerm (atom : MediumAtom) (z y : ℝ) (k : Key) (t : PairIndex) : ℂ :=
  pairCoefficient atom z y k t * zeroIndicator atom.residue (oldIndex t).n1 (oldIndex t).m *
    star (secondDeleted atom.residue (oldIndex t))

def secondZeroTerm (atom : MediumAtom) (z y : ℝ) (k : Key) (t : PairIndex) : ℂ :=
  pairCoefficient atom z y k t * firstDeleted atom.residue (oldIndex t) *
    star (zeroIndicator atom.residue (oldIndex t).n2 (oldIndex t).m)

/-- Restore exactly the two single zeros only on the actual off-diagonal
carrier; the double zero is impossible because the same m is positive. -/
theorem offDiagonal_full_eq_deleted_add_single_zeros
    {atom : MediumAtom} {z y : ℝ} {k : Key} (hM : 0 < atom.V)
    {t : PairIndex} (ht : t ∈ offDiagonalCarrier atom k) :
    S3FullTerm atom z y k t = S3DeletedTerm atom z y k t +
      firstZeroTerm atom z y k t + secondZeroTerm atom z y k t := by
  obtain ⟨ht, h12⟩ := mem_filter.mp ht
  have h := full_two_indicators_restore_single_zeros atom.residue (oldIndex t)
    (paired_m_positive hM ht) h12
  unfold S3FullTerm S3DeletedTerm firstZeroTerm secondZeroTerm
  calc
    _ = pairCoefficient atom z y k t *
        (fullIndicator atom.residue (((oldIndex t).q * (oldIndex t).d) * (oldIndex t).r)
          (oldIndex t).n1 (oldIndex t).m *
        star (fullIndicator atom.residue (((oldIndex t).q * (oldIndex t).d) * (oldIndex t).s)
          (oldIndex t).n2 (oldIndex t).m)) := by ring
    _ = _ := by rw [h]; ring

theorem offDiagonal_restore_identity (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hM : 0 < atom.V) :
    (∑ t ∈ offDiagonalCarrier atom k, S3FullTerm atom z y k t) =
      (∑ t ∈ offDiagonalCarrier atom k, S3DeletedTerm atom z y k t) +
      (∑ t ∈ offDiagonalCarrier atom k, firstZeroTerm atom z y k t) +
      ∑ t ∈ offDiagonalCarrier atom k, secondZeroTerm atom z y k t := by
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  exact offDiagonal_full_eq_deleted_add_single_zeros hM ht

/-- Exact source bookkeeping AFTER deletion and off-diagonal restoration.
Every diagonal and both single-zero corrections remain explicit. No zero
Fourier mode is declared to cancel against S1 or S2. -/
theorem primitive_dispersion_with_restoration (atom : MediumAtom) (z y : ℝ)
    (k : Key) (hM : 0 < atom.V) :
    primitiveQuadratic atom z y k =
      (∑ t ∈ pairedCarrier atom k, S1Term atom z y k t).re -
      2 * (∑ t ∈ pairedCarrier atom k, S2Term atom z y k t).re +
      (∑ t ∈ diagonalCarrier atom k, S3DeletedTerm atom z y k t).re +
      (∑ t ∈ offDiagonalCarrier atom k, S3FullTerm atom z y k t).re -
      (∑ t ∈ offDiagonalCarrier atom k, firstZeroTerm atom z y k t).re -
      (∑ t ∈ offDiagonalCarrier atom k, secondZeroTerm atom z y k t).re := by
  have h1 : primitiveS1 atom z y k =
      (∑ t ∈ pairedCarrier atom k, S1Term atom z y k t).re := by
    simpa using congrArg Complex.re (primitiveS1_eq_paired atom z y k)
  have h3 : (primitiveS3 atom z y k : ℂ) =
      (∑ t ∈ diagonalCarrier atom k, S3DeletedTerm atom z y k t) +
      (∑ t ∈ offDiagonalCarrier atom k, S3FullTerm atom z y k t) -
      (∑ t ∈ offDiagonalCarrier atom k, firstZeroTerm atom z y k t) -
      (∑ t ∈ offDiagonalCarrier atom k, secondZeroTerm atom z y k t) := by
    rw [S3_exact_diagonal_offDiagonal, offDiagonal_restore_identity atom z y k hM]
    ring
  have h3R := congrArg Complex.re h3
  simp at h3R
  rw [primitive_dispersion_identity, h1, primitiveS2_eq_paired_re, h3R]
  ring

end
end ImbalancedChen.Part3.MediumLiteralS3Stages20261028
