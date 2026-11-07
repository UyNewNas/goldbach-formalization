import ImbalancedChen.Part3OriginalWholePoissonCarrierReindex
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.
The genuine original S3 is connected to the whole constructed family.
Its deleted diagonal, both restored single-zero corrections, retained
diagonal, genuine zero mode and omitted modes remain explicit. No zero
mode cancellation, Gram estimate, nonclean bound or E2 estimate is used.
-/

noncomputable section
open Classical Finset Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalTrimmedCleanE3Assembly20261028
open ImbalancedChen.Part3.OriginalSourcePoissonFamilyDictionary20261028
open ImbalancedChen.Part3.OriginalWholePoissonCarrierReindex20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumGenuinePoissonFibre20261028

namespace ImbalancedChen.Part3.OriginalPoissonSourceCorrections20261028

attribute [local instance] Classical.propDecidable

def diagonalRetained (atom : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ v ∈ fibreCarrier atom k, if v.2.1.2 = v.2.2.2 then
    headCoefficient atom (strictReceiverCutoff z) y k v *
      retainedModes atom (sourceKeyH atom k) v else 0

def offDiagonalRetained (atom : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ v ∈ fibreCarrier atom k, if v.2.1.2 ≠ v.2.2.2 then
    headCoefficient atom (strictReceiverCutoff z) y k v *
      retainedModes atom (sourceKeyH atom k) v else 0

def offDiagonalZero (atom : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ v ∈ fibreCarrier atom k, if v.2.1.2 ≠ v.2.2.2 then
    headCoefficient atom (strictReceiverCutoff z) y k v * zeroMode atom v else 0

def offDiagonalOmitted (atom : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ v ∈ fibreCarrier atom k, if v.2.1.2 ≠ v.2.2.2 then
    headCoefficient atom (strictReceiverCutoff z) y k v *
      omittedModes atom (sourceKeyH atom k) v else 0

theorem retainedSourceKey_eq_diagonal_add_offDiagonal
    (atom : MediumAtom) (z y : ℝ) (k : Key) :
    retainedSourceKey atom z y k =
      diagonalRetained atom z y k + offDiagonalRetained atom z y k := by
  unfold retainedSourceKey diagonalRetained offDiagonalRetained
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h12 : v.2.1.2 = v.2.2.2 <;> simp [h12]

theorem restoredOffDiagonal_eq_three_packets
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key) :
    (∑ t ∈ offDiagonalCarrier atom k,
      S3FullTerm atom (strictReceiverCutoff z) y k t) =
      offDiagonalZero atom z y k + offDiagonalRetained atom z y k +
        offDiagonalOmitted atom z y k := by
  rw [literal_offDiagonal_source_at_actual_keyH hA z y k]
  unfold offDiagonalZero offDiagonalRetained offDiagonalOmitted
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h12 : v.2.1.2 ≠ v.2.2.2 <;> simp [h12, mul_add]

/-- Precise diagonal correction between the actual off-diagonal source
and the full raw family. It is not absorbed into a source definition. -/
theorem restoredOffDiagonal_eq_full_retained_with_corrections
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key) :
    (∑ t ∈ offDiagonalCarrier atom k,
      S3FullTerm atom (strictReceiverCutoff z) y k t) =
      retainedSourceKey atom z y k + offDiagonalZero atom z y k +
        offDiagonalOmitted atom z y k - diagonalRetained atom z y k := by
  rw [restoredOffDiagonal_eq_three_packets hA z y k,
    retainedSourceKey_eq_diagonal_add_offDiagonal]
  ring

/-- All corrections belong to independently defined original source
terms. In particular there is no declaration that zero modes cancel. -/
def sourceCorrectionKey (atom : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  (∑ t ∈ diagonalCarrier atom k,
    S3DeletedTerm atom (strictReceiverCutoff z) y k t) +
  offDiagonalZero atom z y k + offDiagonalOmitted atom z y k -
  diagonalRetained atom z y k -
  (∑ t ∈ offDiagonalCarrier atom k,
    firstZeroTerm atom (strictReceiverCutoff z) y k t) -
  ∑ t ∈ offDiagonalCarrier atom k,
    secondZeroTerm atom (strictReceiverCutoff z) y k t

/-- The actual primitive S3, before a centering bound, equals the full
retained source plus every restoration/diagonal/Fourier correction. -/
theorem literalS3_eq_retained_add_corrections
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key) :
    (primitiveS3 atom (strictReceiverCutoff z) y k : ℂ) =
      retainedSourceKey atom z y k + sourceCorrectionKey atom z y k := by
  have hM : 0 < atom.V := lt_of_lt_of_le zero_lt_one hA.2.1
  calc
    _ = (∑ t ∈ diagonalCarrier atom k,
          S3DeletedTerm atom (strictReceiverCutoff z) y k t) +
        (∑ t ∈ offDiagonalCarrier atom k,
          S3FullTerm atom (strictReceiverCutoff z) y k t) -
        (∑ t ∈ offDiagonalCarrier atom k,
          firstZeroTerm atom (strictReceiverCutoff z) y k t) -
        ∑ t ∈ offDiagonalCarrier atom k,
          secondZeroTerm atom (strictReceiverCutoff z) y k t := by
      rw [S3_exact_diagonal_offDiagonal,
        offDiagonal_restore_identity atom (strictReceiverCutoff z) y k hM]
      ring
    _ = _ := by
      rw [restoredOffDiagonal_eq_full_retained_with_corrections hA z y k]
      unfold sourceCorrectionKey
      ring

theorem literalS3_eq_actual_family_add_corrections
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key) (Csep : ℕ) :
    (primitiveS3 atom (strictReceiverCutoff z) y k : ℂ) =
      keyRawFamily atom z y k hA Csep + sourceCorrectionKey atom z y k := by
  rw [literalS3_eq_retained_add_corrections hA z y k,
    retainedSourceKey_eq_keyRawFamily hA z y k Csep]

def literalS3Normalized (atom : MediumAtom) (z y : ℝ) : ℂ :=
  ∑ k ∈ keyBank atom (strictReceiverCutoff z) y,
    (primitiveS3 atom (strictReceiverCutoff z) y k : ℂ) / (atom.V : ℂ)

def sourceCorrectionsNormalized (atom : MediumAtom) (z y : ℝ) : ℂ :=
  ∑ k ∈ keyBank atom (strictReceiverCutoff z) y,
    sourceCorrectionKey atom z y k / (atom.V : ℂ)

/-- Whole actual source connection, including BOTH diagonal corrections
and every nonclean complete-modulus/root packet. No estimate is assumed. -/
theorem literalS3Normalized_eq_typed_nonclean_corrections
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (Csep : ℕ) :
    literalS3Normalized atom z y =
      genuineTypedE3 atom z y hA Csep + genuineNoncleanE2 atom z y hA Csep +
        sourceCorrectionsNormalized atom z y := by
  have hsource : literalS3Normalized atom z y =
      retainedSourceTotal atom z y + sourceCorrectionsNormalized atom z y := by
    unfold literalS3Normalized retainedSourceTotal sourceCorrectionsNormalized
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [literalS3_eq_retained_add_corrections hA z y k, add_div]
  rw [hsource, retainedSourceTotal_eq_typed_plus_nonclean hA z y Csep]

end ImbalancedChen.Part3.OriginalPoissonSourceCorrections20261028
