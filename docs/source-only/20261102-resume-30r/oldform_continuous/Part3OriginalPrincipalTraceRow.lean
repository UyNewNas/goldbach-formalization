import ImbalancedChen.Part3ActualPrincipalCuspOneRemoval
import ImbalancedChen.Part3OriginalSignedTraceInput

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, R22, 2026-11-02.

The original R21 traceBeta and COMPOSITE trace sign, paired with the
actual completed principal incoming Eisenstein cusp-one amplitude.
The finite row identity and its squared norm cost are proved here;
neither an arbitrary coefficient field nor a full spectral energy
hypothesis is introduced. This one incoming channel is not an
orthonormal character-pair fiber or a full continuous Plancherel norm.
The completed K amplitude is not renamed as ABL's raw rho or R.
-/

namespace ImbalancedChen.Part3.OriginalPrincipalTraceRow20261102r

noncomputable section

open scoped BigOperators
open ActualPrincipalOldformRemoval20261102r
open ActualPrincipalCuspOneRemoval20261102r
open OriginalSignedTraceInput20261102
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102
open CriticalEisensteinScattering20261025a
open NormalizedEisensteinPrimeAmplitude20261026b
open ComplexOrderKBridgeSourceOnly
open ImbalancedChen.P3ZActualPrimaryShortEndpoint (signedY)
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (e)

/-- The single sign fixed by the original residue, primary y block,
and Poisson sign. It is not merely the primary y-sign. -/
def principalTraceSign (D : OriginalData) (key : BlockKey) (negativeM : Bool) : ℤ :=
  if traceNegative D key negativeM then -1 else 1

theorem principalTraceSign_cases (D : OriginalData) (key : BlockKey)
    (negativeM : Bool) :
    principalTraceSign D key negativeM = 1 ∨
      principalTraceSign D key negativeM = -1 := by
  cases hs : traceNegative D key negativeM <;> simp [principalTraceSign, hs]

theorem traceIndex_eq_principalTraceSign (D : OriginalData) (key : BlockKey)
    (negativeM : Bool) (z n : ℕ) :
    traceIndex D key negativeM z n =
      principalTraceSign D key negativeM *
        (((D.block.atom.residue.natAbs * key.1) * n : ℕ) : ℤ) := by
  rw [traceIndex_eq_signedY]
  cases hs : traceNegative D key negativeM <;>
    simp [signedY, principalTraceSign, hs, Nat.mul_assoc]

theorem sourceCuspPhase_eq_e (N : ℕ) (j : ℤ) :
    sourceCuspPhase N j = e ((j : ℝ) / (N : ℝ)) := by
  unfold sourceCuspPhase e
  congr 1
  push_cast
  ring

theorem traceBeta_eq_principal_phase (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (key : BlockKey) (upper negativeM : Bool)
    (ell : D4 → ℤ) (z n : ℕ) :
    traceBeta D r key upper negativeM ell z n =
      modulatedBeta D r key upper ell z n *
        sourceCuspPhase z (-(principalTraceSign D key negativeM *
          (((D.block.atom.residue.natAbs * key.1) * n : ℕ) : ℤ))) := by
  simp only [traceBeta, sourceCuspPhase_eq_e, traceIndex_eq_principalTraceSign,
    Int.cast_neg]

/-- The amplitude in the following finite row is bound to the genuine
original cusp-one Fourier integral at the literal R21 trace index.
Its radial argument retains the multiplied frequency A*n. -/
theorem original_traceIndex_principalFourier
    (D : OriginalData) (key : BlockKey) (z : Row D key)
    (ha : D.block.atom.residue ≠ 0) (negativeM : Bool)
    {n : ℕ} (hn : n ∈ nCarrier D key z.val) (t y : ℝ) (hy : 0 < y) :
    principalCuspOneFourierCoeff z.val (levelCarrier_licensed D key z.property).1
        t y hy (traceIndex D key negativeM z.val n) =
      2 * (Real.sqrt y : ℂ) *
        principalCuspOneAmplitude z.val t (principalTraceSign D key negativeM)
          ((D.block.atom.residue.natAbs * key.1) * n) *
        complexOrderK (criticalParameter t - 1 / 2)
          (2 * Real.pi * (((D.block.atom.residue.natAbs * key.1) * n : ℕ) : ℝ) * y) := by
  have hsource := nCarrier_positive_coprime D key z.val hn
  have hA : 0 < D.block.atom.residue.natAbs * key.1 :=
    Nat.mul_pos (Int.natAbs_pos.mpr ha) hsource.1
  rw [traceIndex_eq_principalTraceSign]
  exact principalCuspOneFourierCoeff_eq_amplitude z.val
    (levelCarrier_licensed D key z.property).1 t y hy _
    (Nat.mul_pos hA hsource.2.1) _ (principalTraceSign_cases D key negativeM)

/-- Literal original trace coefficient, original finite n carrier,
and the explicit actual principal cusp-one amplitude. -/
def principalTraceRow (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (key : BlockKey) (z : Row D key) (upper negativeM : Bool)
    (ell : D4 → ℤ) (t : ℝ) : ℂ :=
  ∑ n ∈ nCarrier D key z.val,
    traceBeta D r key upper negativeM ell z.val n *
      principalCuspOneAmplitude z.val t (principalTraceSign D key negativeM)
        ((D.block.atom.residue.natAbs * key.1) * n)

/-- The actual residual row. The signed cusp phase is at n, and beta
keeps the original Q modes; no height, m, or modulus label is added. -/
def principalReducedTraceRow (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (key : BlockKey) (z : Row D key) (upper negativeM : Bool)
    (ell : D4 → ℤ) (t : ℝ) : ℂ :=
  ∑ n ∈ nCarrier D key z.val,
    modulatedBeta D r key upper ell z.val n *
      sourceCuspPhase z.val (-(principalTraceSign D key negativeM * (n : ℤ))) *
      principalCuspOneAmplitude z.val t (principalTraceSign D key negativeM) n

/-- A common multiplier is valid here because it was derived for this
explicit principal expression. No such uniformity is asserted for a
general oldclass, whose dilation multipliers may differ. -/
theorem original_principal_trace_row_removal
    (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (key : BlockKey)
    (z : Row D key) (upper negativeM : Bool) (ell : D4 → ℤ) (t : ℝ) :
    principalTraceRow D r key z upper negativeM ell t =
      normalizedDivisorAmplitude (D.block.atom.residue.natAbs * key.1)
        (criticalParameter t) *
          principalReducedTraceRow D r key z upper negativeM ell t := by
  unfold principalTraceRow principalReducedTraceRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [traceBeta_eq_principal_phase, mul_assoc,
    original_row_principal_cuspOne_phase_removal D key z hn t
      (principalTraceSign D key negativeM)]
  ring

/-- Exact divisor-squared cost for this ACTUAL finite incoming channel,
uniform in every real t including zero. It is not a cusp-summed or
character-pair Plancherel quadratic form. -/
theorem original_principal_trace_row_norm_sq
    (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (key : BlockKey)
    (z : Row D key) (upper negativeM : Bool) (ell : D4 → ℤ) (t : ℝ) :
    ‖principalTraceRow D r key z upper negativeM ell t‖ ^ 2 ≤
      ((D.block.atom.residue.natAbs * key.1).divisors.card : ℝ) ^ 2 *
        ‖principalReducedTraceRow D r key z upper negativeM ell t‖ ^ 2 := by
  rw [original_principal_trace_row_removal, norm_mul, mul_pow]
  have h := normalizedAmplitude_critical_norm_le_divisors
    (D.block.atom.residue.natAbs * key.1) t
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) h 2) (sq_nonneg _)

end

end ImbalancedChen.Part3.OriginalPrincipalTraceRow20261102r
