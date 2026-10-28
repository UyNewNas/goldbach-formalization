import ImbalancedChen.P5ActualHBPostModulusLogCutoff

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Retained arithmetic-mode port for the ACTUAL occurrence chart. Its input
is the original local factorized arithmetic estimate for separated modes;
its measure is paid by actual Fourier L1, never by the cube volume H^m.
No medium, BV or one-/two-long arithmetic estimate is proved here.
-/
namespace ImbalancedChen.P5Z.ActualRetainedModeL1Port
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open ImbalancedChen.PrimeProducts
open AllRankCoordinateFourierIBP AllRankMixedOperatorBudget AllRankCauchyCubeTail
open AdmissibleAllRankIntegerGeometricFamily ActualEuclideanPhysicalFourier
open ActualAllRankOccurrenceFourierBridge ActualHBPostModulusLogCutoff

variable {kStar m : ℕ}

/-- Exact retained-cube separation. It is derived from the definition of
the actual truncation and the finite arithmetic integral theorem. -/
theorem retained_actual_integral (A : Family kStar) (T : ℕ)
    (k : Fin (kStar + 1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ H : ℝ)
    (s : Finset (Fin m → ℕ)) (β : (Fin m → ℕ) → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) :
    MellinInsertion20261028.exactDiscrepancy s Q rho completeProduct T
      (fun n => β n * truncatedPhysical m (actualEuclideanChart A T k owner U R κ₀) H
        (WithLp.toLp 2 (logOccurrence U n))) =
    ∫ ξ in (outsideCube m H)ᶜ, actualAmplitude A T k owner U R κ₀ ξ *
      MellinInsertion20261028.exactDiscrepancy s Q rho completeProduct T
        (fun n => β n * occurrenceMode U n ξ) := by
  let c : (Fin m → ℕ) → ℂ := fun n =>
    ∑ q ∈ Q, rho q * MellinInsertion20261028.residueKernel q T (completeProduct n)
  have hint (n : Fin m → ℕ) : Integrable (fun ξ : Fin m → ℝ =>
      actualAmplitude A T k owner U R κ₀ ξ * (β n * occurrenceMode U n ξ)) := by
    have h := (actual_integer_mode_integrable A T k owner U R κ₀ n).const_mul (β n)
    apply h.congr
    exact Filter.Eventually.of_forall (fun ξ => by rw [physicalPhase_occurrenceMode]; ring)
  have hrep (n : Fin m → ℕ) :
      β n * truncatedPhysical m (actualEuclideanChart A T k owner U R κ₀) H
        (WithLp.toLp 2 (logOccurrence U n)) =
      ∫ ξ in (outsideCube m H)ᶜ, actualAmplitude A T k owner U R κ₀ ξ *
        (β n * occurrenceMode U n ξ) := by
    unfold truncatedPhysical
    rw [← integral_smul, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [physicalPhase_occurrenceMode]
      simp only [actualAmplitude, smul_eq_mul]
      ring)
  change MellinInsertion20261028.functional s c _ = _
  simp_rw [hrep]
  rw [MellinInsertion20261028.functional_integral s c _
    (fun n hn => (hint n).integrableOn)]
  simp_rw [MellinInsertion20261028.functional_mul]
  rfl

/-- A uniform local arithmetic estimate for every retained separated
mode is the genuine open arithmetic port. The conclusion charges only
D/2^m and keeps the original signed count/exact-coprime-mean functional. -/
theorem retained_actual_l1_bound (A : Family kStar) (T : ℕ)
    (k : Fin (kStar + 1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ H : ℝ)
    (s : Finset (Fin m → ℕ)) (β : (Fin m → ℕ) → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hmode : ∀ ξ ∈ (outsideCube m H)ᶜ,
      ‖MellinInsertion20261028.exactDiscrepancy s Q rho completeProduct T
        (fun n => β n * occurrenceMode U n ξ)‖ ≤ E) :
    ‖MellinInsertion20261028.exactDiscrepancy s Q rho completeProduct T
      (fun n => β n * truncatedPhysical m (actualEuclideanChart A T k owner U R κ₀) H
        (WithLp.toLp 2 (logOccurrence U n)))‖ ≤
      (mixedD m (actualEuclideanChart A T k owner U R κ₀) / 2 ^ m) * E := by
  let amp := actualAmplitude A T k owner U R κ₀
  let mode := fun ξ n => β n * occurrenceMode U n ξ
  let c := fun n => ∑ q ∈ Q,
    rho q * MellinInsertion20261028.residueKernel q T (completeProduct n)
  have hAmp : Integrable amp := actualAmplitude_integrable A T k owner U R κ₀
  have hterms (n : Fin m → ℕ) : Integrable (fun ξ => amp ξ * mode ξ n) := by
    have h := (actual_integer_mode_integrable A T k owner U R κ₀ n).const_mul (β n)
    apply h.congr
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [physicalPhase_occurrenceMode]
      dsimp only [amp, mode]
      ring)
  have hInt : Integrable (fun ξ => amp ξ * MellinInsertion20261028.functional s c (mode ξ)) := by
    have hf := MellinInsertion20261028.functional_integrable s c
      (fun ξ n => amp ξ * mode ξ n) (fun n hn => hterms n)
    simpa only [MellinInsertion20261028.functional_mul] using hf
  rw [retained_actual_integral]
  calc
    ‖∫ ξ in (outsideCube m H)ᶜ, amp ξ *
        MellinInsertion20261028.functional s c (mode ξ)‖ ≤
      ∫ ξ in (outsideCube m H)ᶜ, ‖amp ξ * MellinInsertion20261028.functional s c (mode ξ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ξ in (outsideCube m H)ᶜ, ‖amp ξ‖ * E := by
      apply integral_mono_ae hInt.norm.integrableOn (hAmp.norm.mul_const E).integrableOn
      filter_upwards [ae_restrict_mem (measurableSet_outsideCube m H).compl] with ξ hξ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hmode ξ hξ) (norm_nonneg _)
    _ = (∫ ξ in (outsideCube m H)ᶜ, ‖amp ξ‖) * E := by rw [integral_mul_const]
    _ ≤ (∫ ξ : Fin m → ℝ, ‖amp ξ‖) * E :=
      mul_le_mul_of_nonneg_right
        (setIntegral_le_integral hAmp.norm (Filter.Eventually.of_forall (fun ξ => norm_nonneg _))) hE
    _ ≤ (mixedD m (actualEuclideanChart A T k owner U R κ₀) / 2 ^ m) * E :=
      mul_le_mul_of_nonneg_right (actualAmplitude_l1_le A T k owner U R κ₀) hE

end
end ImbalancedChen.P5Z.ActualRetainedModeL1Port
