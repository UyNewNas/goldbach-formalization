import ImbalancedChen.P2RoundedFibreCore
import ImbalancedChen.P2LowerCanonicalRetainedTrace
import ImbalancedChen.P2CompiledCausalPrimeSourceLower
import ImbalancedChen.P2RoundedU6NativeJointLedger

/-!
# Actual ALL/ANY rounding loss and uniform physical-level inflation

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Negative coefficients are rounded OUTWARD, so the rounded support need not
be contained in the raw retained support. The correct preimage is an actual
raw modulus in the SAME complete logarithmic label fibre. Its existence is
proved from the literal compiler, not supplied as a support hypothesis.
A common rank bound then costs R*tau in exponent. A strict raw level reserve
pays this cost with a mesh fixed before N, and the genuine small beta factor
is included in the physical bound.

The actual density loss is confined to mixed fibres, containing both an
original retained and rejected complete history. No count of N-dependent
prime gaps is used to claim common-mesh asymptotic convergence. Full wall
cover and its uniform arithmetic mass, and the selected-plan raw level/rank
supplier, remain explicit implementation obligations.
-/

namespace ImbalancedChen.P2RoundedCausalFibreLossAndLevel

noncomputable section
open scoped Classical BigOperators
open P2LowerFiniteCellRounding P2LowerFiniteCellBetaCompiler
open P2LowerCapPlanIntegerRetention P2LowerCanonicalRetainedTrace

/-- The full signed paired ledger from the second batch inherits ONE
physical exponent. Rounded lower and native upper fibres may overlap and
cancel; no unit bound on their signed aggregate is required. The only lower
level premise concerns ORIGINAL accepted raw histories. -/
theorem rounded_joint_sigma_physical_level
    (D : P2RoundedU6NativeJointLedger.RoundedLowerData)
    {n N : ℕ} {eta : ℚ} (hN : 1 < N) (heta : 0 < eta)
    (E : ℕ × ℕ → Prop) (theta ell nu : ℝ) (R : ℕ)
    (hnative : (153 / 256 : ℝ) ≤ nu)
    (hgates : ∀ t ∈ P2RoundedU6NativeJointLedger.lowerRows N E,
      0 < D.mesh t ∧ D.L t = (N : ℝ) ^ ell ∧
      theta + ell + (R : ℝ) * D.mesh t ≤ nu)
    (hraw : ∀ t ∈ P2RoundedU6NativeJointLedger.lowerRows N E,
      ∀ r ∈ rawSupport (D.policy t) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (D.w t)
        (P5CausalRhoQuotientBridge.cutoff N),
        (((t.1 * t.2) * r : ℕ) : ℝ) ≤ (N : ℝ) ^ theta ∧
          r.primeFactorsList.length ≤ R)
    {q : ℕ} (hq : P2RoundedU6NativeJointLedger.sigma D n N eta E q ≠ 0) :
    (q : ℝ) ≤ (N : ℝ) ^ nu := by
  have hNR : 1 < (N : ℝ) := by exact_mod_cast hN
  by_cases hl : P2RoundedU6NativeJointLedger.lowerSigma D N E q = 0
  · have hu :
        P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E q ≠ 0 := by
      intro hu
      exact hq (by simp [P2RoundedU6NativeJointLedger.sigma, hl, hu])
    have hp :=
      P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma_nonzero_profile
        hN heta hu
    exact hp.2.2.2.2.le.trans
      (Real.rpow_le_rpow_of_exponent_le hNR.le hnative)
  · have hex : ∃ m ∈ (P2RoundedU6NativeJointLedger.lowerMarks D N E).filter
        (fun m => P2RoundedU6NativeJointLedger.lowerModulus m = q),
        P2RoundedU6NativeJointLedger.lowerRho D N m.1 m.2 ≠ 0 := by
      by_contra hn
      apply hl
      unfold P2RoundedU6NativeJointLedger.lowerSigma
      apply Finset.sum_eq_zero
      intro m hm
      by_contra hc
      exact hn ⟨m, hm, hc⟩
    obtain ⟨m, hm, hcoeff⟩ := hex
    obtain ⟨hmark, hmq⟩ := Finset.mem_filter.mp hm
    obtain ⟨ht, hd⟩ := Finset.mem_sigma.mp hmark
    obtain ⟨htau, hL, hnu⟩ := hgates m.1 ht
    have hrho : rho (D.policy m.1) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (D.w m.1)
        (P5CausalRhoQuotientBridge.cutoff N) (D.mesh m.1)
        ((N : ℝ) ^ ell) m.2 ≠ 0 := by
      simpa only [P2RoundedU6NativeJointLedger.lowerRho, hL] using hcoeff
    have hp := rounded_rho_full_level hNR (D.policy m.1)
      (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (m.1.1 * m.1.2) R
      (D.w m.1) (P5CausalRhoQuotientBridge.cutoff N) theta ell htau
      (hraw m.1 ht) hrho
    change (P2RoundedU6NativeJointLedger.lowerModulus m : ℝ) ≤ _ at hp
    rw [hmq] at hp
    exact hp.trans (Real.rpow_le_rpow_of_exponent_le hNR.le hnu)


end
end ImbalancedChen.P2RoundedCausalFibreLossAndLevel
