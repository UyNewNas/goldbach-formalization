import ImbalancedChen.Part3ActualCuspFourierSection
import Mathlib.Algebra.Star.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! Reused signed/conjugate cusp-section proofs from the 2026-11-02 archive.
The original archive remains unchanged; the remaining packet assembly is staged separately. -/

namespace ImbalancedChen.Part3.OriginalSignedNativeCuspFourier20261102
noncomputable section
open MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate MatrixGroups UpperHalfPlane
open ActualCuspFourierSectionSourceOnly
open P3CuspTranslationFourierPhaseSourceOnly
open P3ActualLiteralPacketIntegralSourceOnly

/-- Conjugation is applied to the actual upper-half-plane function. -/
def conjugateForm (f : ℍ → ℂ) : ℍ → ℂ := fun w => conj (f w)

theorem conjugateForm_involutive (f : ℍ → ℂ) :
    conjugateForm (conjugateForm f) = f := by
  funext w
  simp only [conjugateForm, Complex.conj_conj]

theorem conjugateForm_continuous (f : ℍ → ℂ) (hf : Continuous f) :
    Continuous (conjugateForm f) := by
  exact Complex.continuous_conj.comp hf

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
    dsimp only
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

end
end ImbalancedChen.Part3.OriginalSignedNativeCuspFourier20261102
