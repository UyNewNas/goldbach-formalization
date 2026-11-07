import ImbalancedChen.Part3ActualCuspFourierSection
import ImbalancedChen.Part3OriginalPrimaryPacketRows
import Mathlib.Algebra.Star.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The two Fourier coefficients below are the existing normalized-Haar
integrals of the actual Gamma0-invariant function in its old/new cusp-one
charts. Complex conjugation changes both the function and the Fourier
index. It does not assert that an individual form has real coefficients.

The final identities use the original primary row, its full nCarrier and
blockBeta, with the original sign flag. No arbitrary rho maps, spectral
basis, trace formula, A/J estimate, or energy bound are inputs.

These fixed-height Fourier coefficients are NOT identified with the
height-independent automorphic R(n). Such an identification still needs
the actual Maass/Eisenstein expansion and its Whittaker normalization.

The import of Part3ActualCuspFourierSection uses the minimal corrected
source recorded in repairs/ and REGISTRY.json. Both old modules' only
replacement is AddCircle.fourier* -> _root_.fourier*, as required by the
exact mathlib pin e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
-/

namespace ImbalancedChen.Part3.OriginalSignedNativeCuspFourier20261102

noncomputable section

open MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate MatrixGroups UpperHalfPlane
open ActualCuspFourierSectionSourceOnly
open P3CuspTranslationFourierPhaseSourceOnly
open P3ActualLiteralPacketIntegralSourceOnly
open OriginalCompletedReciprocalSource20261102
open OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102

/-- Conjugation is applied to the actual upper-half-plane function. -/
def conjugateForm (f : ℍ → ℂ) : ℍ → ℂ := fun w => conj (f w)

theorem conjugateForm_involutive (f : ℍ → ℂ) :
    conjugateForm (conjugateForm f) = f := by
  funext w
  simp only [conjugateForm, Complex.conj_conj]

theorem conjugateForm_continuous (f : ℍ → ℂ) (hf : Continuous f) :
    Continuous (conjugateForm f) := by
  simpa only [conjugateForm, Complex.star_def] using continuous_star.comp hf

/-- Trivial-character Gamma0 invariance is preserved without changing
the level, scaling matrix, or point of the upper half plane. -/
theorem conjugateForm_invariant (N : ℕ) (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ w : ℍ, f (γ • w) = f w) :
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ w : ℍ, conjugateForm f (γ • w) = conjugateForm f w := by
  intro γ hγ w
  exact congrArg conj (hfΓ γ hγ w)

/-- Exact normalized-Haar identity. No integrability premise is needed:
the Bochner conjugation identity also respects its totalized zero value. -/
theorem circleFourierCoeff_conjugate (F : UnitAddCircle → ℂ) (n : ℤ) :
    _root_.fourierCoeff (fun x => conj (F x)) n =
      conj (_root_.fourierCoeff F (-n)) := by
  simp only [_root_.fourierCoeff, neg_neg, smul_eq_mul]
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    rw [map_mul, ← _root_.fourier_neg]

theorem oldSection_conjugate (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ w : ℍ, f (γ • w) = f w) (y : ℝ) (hy : 0 < y) :
    oldSection N hN (conjugateForm f) (conjugateForm_invariant N f hfΓ) y hy =
      fun x => conj (oldSection N hN f hfΓ y hy x) := by
  funext x
  induction x using QuotientAddGroup.induction_on with | _ r =>
    change oldTrace N hN (conjugateForm f) y hy r =
      conj (oldTrace N hN f y hy r)
    rfl

theorem newSection_conjugate (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ w : ℍ, f (γ • w) = f w) (y : ℝ) (hy : 0 < y) :
    newSection N hN (conjugateForm f) (conjugateForm_invariant N f hfΓ) y hy =
      fun x => conj (newSection N hN f hfΓ y hy x) := by
  funext x
  induction x using QuotientAddGroup.induction_on with | _ r =>
    change newTrace N hN (conjugateForm f) y hy r =
      conj (newTrace N hN f y hy r)
    rfl

/-- The old chart's negative frequency is not silently replaced by its
positive frequency: the form itself is conjugated. -/
theorem oldFourierCoeff_conjugate (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ w : ℍ, f (γ • w) = f w) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    oldFourierCoeff N hN (conjugateForm f)
        (conjugateForm_invariant N f hfΓ) y hy n =
      conj (oldFourierCoeff N hN f hfΓ y hy (-n)) := by
  rw [oldFourierCoeff, oldSection_conjugate]
  exact circleFourierCoeff_conjugate _ n

theorem newFourierCoeff_conjugate (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ w : ℍ, f (γ • w) = f w) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    newFourierCoeff N hN (conjugateForm f)
        (conjugateForm_invariant N f hfΓ) y hy n =
      conj (newFourierCoeff N hN f hfΓ y hy (-n)) := by
  rw [newFourierCoeff, newSection_conjugate]
  exact circleFourierCoeff_conjugate _ n

/-- Both original sign branches cancel the old/new chart phase. The
positive packet uses e(-n/N), and the negative packet uses e(+n/N). -/
theorem cuspPhase_cancels_actual_section_signed
    (negative : Bool) (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ w : ℍ, f (γ • w) = f w) (y : ℝ) (hy : 0 < y) (n : ℕ) :
    cuspPhase negative N n *
        oldFourierCoeff N hN f hfΓ y hy
          (if negative then -(n : ℤ) else (n : ℤ)) =
      newFourierCoeff N hN f hfΓ y hy
        (if negative then -(n : ℤ) else (n : ℤ)) := by
  cases negative
  · simpa only [Bool.false_eq_true, if_false] using
      cuspPhase_cancels_actual_section N hN f hfΓ y hy n
  · simp only [if_true]
    rw [oldFourierCoeff_phase, ← fourier_cuspShift,
      ← mul_assoc, ← _root_.fourier_add]
    simp only [add_neg_cancel, _root_.fourier_zero, one_mul]

/-- Exact pairing for the original primary row. Its sign, arithmetic
multiplicities, coprime deletion and actual occupied level are preserved. -/
theorem original_signed_row_native_term (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 z.val →
      ∀ w : ℍ, f (γ • w) = f w) (y : ℝ) (hy : 0 < y) (n : ℕ) :
    signedCoefficient k.2.2 (rowPacket D r k z) n *
        oldFourierCoeff z.val (levelCarrier_licensed D k z.property).1
          f hfΓ y hy (if k.2.2 then -(n : ℤ) else (n : ℤ)) =
      blockBeta D r k (decode k z.val n) *
        newFourierCoeff z.val (levelCarrier_licensed D k z.property).1
          f hfΓ y hy (if k.2.2 then -(n : ℤ) else (n : ℤ)) := by
  rw [rowCoefficient_eq, mul_assoc,
    cuspPhase_cancels_actual_section_signed]

/-- The full original n carrier is retained. This is an equality of
actual fixed-height Fourier functionals, with no spectral-state sum. -/
theorem original_signed_row_native_sum (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 z.val →
      ∀ w : ℍ, f (γ • w) = f w) (y : ℝ) (hy : 0 < y) :
    (∑ n ∈ nCarrier D k z.val,
      signedCoefficient k.2.2 (rowPacket D r k z) n *
        oldFourierCoeff z.val (levelCarrier_licensed D k z.property).1
          f hfΓ y hy (if k.2.2 then -(n : ℤ) else (n : ℤ))) =
      ∑ n ∈ nCarrier D k z.val,
        blockBeta D r k (decode k z.val n) *
          newFourierCoeff z.val (levelCarrier_licensed D k z.property).1
            f hfΓ y hy (if k.2.2 then -(n : ℤ) else (n : ℤ)) := by
  apply Finset.sum_congr rfl
  intro n hn
  exact original_signed_row_native_term D r k z f hfΓ y hy n

/-- On the actual negative row, positivity of the index is recovered
by conjugating BOTH the original beta and the actual form. No reality or
reflection property of a chosen spectral basis is assumed. -/
theorem original_negative_row_native_conjugate (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (hnegative : k.2.2 = true) (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 z.val →
      ∀ w : ℍ, f (γ • w) = f w) (y : ℝ) (hy : 0 < y) :
    (∑ n ∈ nCarrier D k z.val,
      signedCoefficient k.2.2 (rowPacket D r k z) n *
        oldFourierCoeff z.val (levelCarrier_licensed D k z.property).1
          f hfΓ y hy (-(n : ℤ))) =
      conj (∑ n ∈ nCarrier D k z.val,
        conj (blockBeta D r k (decode k z.val n)) *
          newFourierCoeff z.val (levelCarrier_licensed D k z.property).1
            (conjugateForm f) (conjugateForm_invariant z.val f hfΓ)
            y hy (n : ℤ)) := by
  have hsum := original_signed_row_native_sum D r k z f hfΓ y hy
  simp only [hnegative, if_true] at hsum ⊢
  rw [hsum, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul, Complex.conj_conj, newFourierCoeff_conjugate,
    Complex.conj_conj]

/-- Exact norm equality for that original finite-row functional. It
does not assert any large-sieve or automorphic spectral-energy bound. -/
theorem original_negative_row_native_norm (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (hnegative : k.2.2 = true) (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 z.val →
      ∀ w : ℍ, f (γ • w) = f w) (y : ℝ) (hy : 0 < y) :
    ‖∑ n ∈ nCarrier D k z.val,
      signedCoefficient k.2.2 (rowPacket D r k z) n *
        oldFourierCoeff z.val (levelCarrier_licensed D k z.property).1
          f hfΓ y hy (-(n : ℤ))‖ =
      ‖∑ n ∈ nCarrier D k z.val,
        conj (blockBeta D r k (decode k z.val n)) *
          newFourierCoeff z.val (levelCarrier_licensed D k z.property).1
            (conjugateForm f) (conjugateForm_invariant z.val f hfΓ)
            y hy (n : ℤ)‖ := by
  rw [original_negative_row_native_conjugate D r k z hnegative,
    Complex.norm_conj]

end

end ImbalancedChen.Part3.OriginalSignedNativeCuspFourier20261102
