import ImbalancedChen.Part3ActualHeckeCorrespondencePairing
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
A genuine bounded complex-linear operator on the original canonical
Gamma0 quotient L2 space. It is constructed from actual pullback adjoints,
then identified with the ORIGINAL physical normalized p+1 branch trace
using the proved actual correspondence pairing. No abstract-to-physical
operator identification, L2 trace bound, or selfadjointness is assumed.
-/

namespace ImbalancedChen.Part3.ActualBoundedPhysicalHecke20261026b
noncomputable section
open MeasureTheory
open ActualHeckeForgetL220261026b ActualHeckeSecondL220261026b
open ActualHeckeCorrespondencePairing20261026b ActualPrimeHeckeQuotientDescent20261026b
open Gamma0QuotientCellPushforward20261025a

variable (N p : ℕ) [NeZero N] [NeZero (N*p)]
  (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N)

def firstPullbackCLM : Lp ℂ 2 (carrierPushforward N) →L[ℂ] Lp ℂ 2 (carrierPushforward (N*p)) :=
  (rawPullbackLinear N p hp hpN).mkContinuous (Real.sqrt (p+1 : ℝ))
    (fun U => (rawPullback_norm N p hp hpN U).le)

def secondPullbackCLM : Lp ℂ 2 (carrierPushforward N) →L[ℂ] Lp ℂ 2 (carrierPushforward (N*p)) :=
  (rawSecondPullbackLinear N p hN hp hpN).mkContinuous (Real.sqrt (p+1 : ℝ))
    (fun V => (rawSecondPullback_norm N p hN hp hpN V).le)

theorem firstPullbackCLM_norm_le : ‖firstPullbackCLM N p hp hpN‖ ≤ Real.sqrt (p+1 : ℝ) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

theorem secondPullbackCLM_norm_le : ‖secondPullbackCLM N p hN hp hpN‖ ≤ Real.sqrt (p+1 : ℝ) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

/-- Genuine canonical quotient L2 Hecke operator with original p^-1/2
normalization; both projections and the averaging adjoint are actual. -/
def physicalHeckeOperator : Lp ℂ 2 (carrierPushforward N) →L[ℂ] Lp ℂ 2 (carrierPushforward N) :=
  (Real.sqrt (p : ℝ) : ℂ)⁻¹ •
    ((ContinuousLinearMap.adjoint (firstPullbackCLM N p hp hpN)).comp
      (secondPullbackCLM N p hN hp hpN))

/-- The bounded operator is the native L2 vector represented by the
original physical quotient trace, not merely an unnamed averaging map. -/
theorem physicalHeckeOperator_eq_physicalHeckeLp (V : Lp ℂ 2 (carrierPushforward N)) :
    physicalHeckeOperator N p hN hp hpN V = physicalHeckeLp N p hN hp hpN V := by
  have hs : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < p by exact_mod_cast hp.pos)).ne'
  apply ext_inner_left ℂ
  intro U
  change inner ℂ U ((Real.sqrt (p : ℝ) : ℂ)⁻¹ •
    ContinuousLinearMap.adjoint (firstPullbackCLM N p hp hpN)
      (secondPullbackCLM N p hN hp hpN V)) = _
  rw [inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
  change (Real.sqrt (p : ℝ) : ℂ)⁻¹ *
    inner ℂ (rawPullback N p hp hpN U) (rawSecondPullbackLinear N p hN hp hpN V) = _
  rw [rawPullback_inner_physicalHecke N p hN hp hpN U V]
  simp only [← mul_assoc, inv_mul_cancel₀ hs, one_mul]

theorem physicalHeckeOperator_coe (V : Lp ℂ 2 (carrierPushforward N)) :
    (physicalHeckeOperator N p hN hp hpN V : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      quotientHecke N p hp hpN V := by
  rw [physicalHeckeOperator_eq_physicalHeckeLp]
  exact physicalHeckeLp_coe N p hN hp hpN V

/-- The exact elementary operator norm bound (p+1)/sqrt(p), with all
finite-cover and physical normalization constants derived. -/
theorem physicalHeckeOperator_norm_le :
    ‖physicalHeckeOperator N p hN hp hpN‖ ≤ (p+1 : ℝ)/Real.sqrt (p : ℝ) := by
  have hs : 0 < Real.sqrt (p : ℝ) :=
    Real.sqrt_pos.mpr (show (0 : ℝ) < p by exact_mod_cast hp.pos)
  have hscalar : ‖(Real.sqrt (p : ℝ) : ℂ)⁻¹‖ = (Real.sqrt (p : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hfirst : ‖ContinuousLinearMap.adjoint (firstPullbackCLM N p hp hpN)‖ ≤ Real.sqrt (p+1 : ℝ) := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact firstPullbackCLM_norm_le N p hp hpN
  change ‖(Real.sqrt (p : ℝ) : ℂ)⁻¹ •
    ((ContinuousLinearMap.adjoint (firstPullbackCLM N p hp hpN)).comp
      (secondPullbackCLM N p hN hp hpN))‖ ≤ _
  rw [norm_smul, hscalar]
  calc
    _ ≤ (Real.sqrt (p : ℝ))⁻¹ *
        (‖ContinuousLinearMap.adjoint (firstPullbackCLM N p hp hpN)‖ *
          ‖secondPullbackCLM N p hN hp hpN‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (inv_nonneg.mpr hs.le)
    _ ≤ (Real.sqrt (p : ℝ))⁻¹ *
        (Real.sqrt (p+1 : ℝ) * Real.sqrt (p+1 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hfirst (secondPullbackCLM_norm_le N p hN hp hpN) (norm_nonneg _)
          (Real.sqrt_nonneg _)) (inv_nonneg.mpr hs.le)
    _ = _ := by rw [← pow_two, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ p+1)]; ring

theorem physicalHeckeOperator_apply_norm_le (V : Lp ℂ 2 (carrierPushforward N)) :
    ‖physicalHeckeOperator N p hN hp hpN V‖ ≤ ((p+1 : ℝ)/Real.sqrt (p : ℝ))*‖V‖ :=
  (physicalHeckeOperator N p hN hp hpN).le_of_opNorm_le
    (physicalHeckeOperator_norm_le N p hN hp hpN) V

end
end ImbalancedChen.Part3.ActualBoundedPhysicalHecke20261026b
