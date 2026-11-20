import ImbalancedChen.P3ActualEvenLowerRoughEulerUniform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
P3.6; frozen paper UyNewNas/chen-imbalanced-semiprimes@
9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §1 (PP), §3 (T), §4 (F).

A scalar transfer missing from the original U6 even-first-exit LOWER
source: its literal rough cutoff is N^(417/5000), with exponent
strictly between zero and one. For N >= 2, the existing Mertens
envelope in log(max 2 z) is therefore bounded by the SAME log N.
The absolute correction keeps the original integer LOWER rho,
strict s<L(t)<=A, the actual physical prefix b=t.1*t.2 and
the exact phi(b*q), without a new discrepancy premise.

This does NOT control the small Rosser level A by a power of N,
nor any signed offshift error, global rho_N, or full PP source.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualEvenLowerRoughEulerToTargetLog
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualEvenLowerRoughEulerUniform
open ImbalancedChen.P3ActualRawActiveLevelTotientCap

/-- The *production* U6 rough cutoff, not a chosen surrogate z. -/
theorem original_U6_rough_cutoff_le_N (N : ℕ) (hN : 2 ≤ N) :
    P5CausalRhoQuotientBridge.cutoff N ≤ (N : ℝ) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  change (N : ℝ) ^ (417 / 5000 : ℝ) ≤ (N : ℝ)
  exact Real.rpow_le_self_of_one_le hN1 (by norm_num)

/-- The Mertens envelope is now expressed in the original large
integer N, with one shared N >= 2 threshold. No bound on A is hidden. -/
theorem original_U6_rough_log_envelope_le_target
    (C : ℝ) (hC : 0 ≤ C) (N : ℕ) (hN : 2 ≤ N) :
    roughLogEnvelope C (P5CausalRhoQuotientBridge.cutoff N) ≤
      C * (1 + Real.log (N : ℝ)) := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmax :
      max (2 : ℝ) (P5CausalRhoQuotientBridge.cutoff N) ≤
        (N : ℝ) :=
    max_le hN2 (original_U6_rough_cutoff_le_N N hN)
  have hmax0 :
      0 < max (2 : ℝ) (P5CausalRhoQuotientBridge.cutoff N) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
      (le_max_left 2 _)
  have hlog :
      Real.log (max (2 : ℝ) (P5CausalRhoQuotientBridge.cutoff N)) ≤
        Real.log (N : ℝ) := Real.log_le_log hmax0 hmax
  unfold roughLogEnvelope
  exact mul_le_mul_of_nonneg_left (add_le_add_left hlog 1) hC

/-- Actual rough carrier, real endpoint z = cutoff(N), with C
chosen BEFORE N, the cap and w; the old Mertens dependence is reused. -/
theorem exists_original_U6_rough_euler_le_target_log :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N cap : ℕ) (w : ℝ), 2 ≤ N →
        roughEulerMass N cap w (P5CausalRhoQuotientBridge.cutoff N) ≤
          C * (1 + Real.log (N : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_original_rough_euler_le_log_envelope
  refine ⟨C, hC, ?_⟩
  intro N cap w hN
  exact (hbound N cap w (P5CausalRhoQuotientBridge.cutoff N)).trans
    (original_U6_rough_log_envelope_le_target C hC.le N hN)

/-- The original even first-exit LOWER INTEGER rho with the complete
physical b*q denominator. Only the scalar quotient-prime correction
is paid by the explicit log N envelope; no claim about (PP) itself.

The actual strict level L(t) <= A remains a premise; nothing claims
A <= N or that the full manuscript rho_N has been identified. -/
theorem exists_actual_U6_lower_quotient_correction_target_log :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N A : ℕ) (hN : 2 ≤ N)
        (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
        (policy : (ℕ × ℕ) → List ℕ → Bool)
        (w L : (ℕ × ℕ) → ℝ)
        (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N)
        (hLA : L t ≤ (A : ℝ)),
      let z := P5CausalRhoQuotientBridge.cutoff N
      let cap := Nat.ceil z
      let b := t.1 * t.2
      let Q := actualLowerSmallRoughModuli (policy t) N cap (w t) z
      let rho := actualEvenLowerIntegerRho (policy t) N cap (w t) z (L t)
      |∑ q ∈ Q, (rho q : ℝ) *
        (chenPrimeDivisorCount N q / (Nat.totient (b * q) : ℝ))| ≤
        (Nat.totient b : ℝ)⁻¹ *
          (logTotientCap A * (C * (1 + Real.log (N : ℝ))) *
            ((Nat.log 2 A : ℝ) + C * (1 + Real.log (N : ℝ)))) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_actual_U6_lower_quotient_correction_log_envelope
  refine ⟨C, hC, ?_⟩
  intro N A hN t ht policy w L hwz hLA
  have hstart := hbound N A t ht policy w L hwz hLA
  dsimp at hstart ⊢
  let z := P5CausalRhoQuotientBridge.cutoff N
  let M := roughLogEnvelope C z
  let U := C * (1 + Real.log (N : ℝ))
  let k : ℝ := (Nat.log 2 A : ℝ)
  have hMU : M ≤ U :=
    original_U6_rough_log_envelope_le_target C hC.le N hN
  have hm2 : (2 : ℝ) ≤ max 2 z := le_max_left _ _
  have hlogM : 0 ≤ Real.log (max (2 : ℝ) z) :=
    Real.log_nonneg (by linarith)
  have hM0 : 0 ≤ M :=
    mul_nonneg hC.le (by dsimp; linarith)
  have hU0 : 0 ≤ U := le_trans hM0 hMU
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hquad : M * (k + M) ≤ U * (k + U) := by
    calc
      M * (k + M) ≤ U * (k + M) :=
        mul_le_mul_of_nonneg_right hMU (add_nonneg hk hM0)
      _ ≤ U * (k + U) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hMU k) hU0
  calc
    _ ≤ (Nat.totient (t.1 * t.2) : ℝ)⁻¹ *
        (logTotientCap A * M * (k + M)) := hstart
    _ ≤ (Nat.totient (t.1 * t.2) : ℝ)⁻¹ *
        (logTotientCap A * U * (k + U)) := by
      apply mul_le_mul_of_nonneg_left
      · calc
          logTotientCap A * M * (k + M) =
              logTotientCap A * (M * (k + M)) := by ring
          _ ≤ logTotientCap A * (U * (k + U)) :=
            mul_le_mul_of_nonneg_left hquad (logTotientCap_nonneg A)
          _ = logTotientCap A * U * (k + U) := by ring
      · positivity

end
end ImbalancedChen.P3ActualEvenLowerRoughEulerToTargetLog
