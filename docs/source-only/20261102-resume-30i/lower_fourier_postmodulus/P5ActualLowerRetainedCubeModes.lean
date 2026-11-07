import ImbalancedChen.P5ActualLowerNormalizedPostModulusTail

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The retained expression is the genuine cube integral of separated modes
with the original count/coprime-mean kernel. No retained mode estimate is
asserted. Literal order-three roles, rough cutoff and scalar are exposed.
-/
namespace ImbalancedChen.P5Z.ActualLowerRetainedCubeModes
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open ActualLowerNormalizedBlockGeometry ActualLowerNormalizedPostModulusTail
open ActualLowerNormalizedHBSource ActualHBPostModulusLogCutoff
open ActualEuclideanPhysicalFourier AllRankCauchyCubeTail
open ActualAllRankOccurrenceFourierBridge OccurrenceEuclideanMixedIntegral
open HBRightClosedDyadicRoles PerGroupIntegerHBAtlasPushforward
open ActualRoughHeathBrownWords
open ExactOriginalSmoothDyadicPartition (R beforeHBCutoff)
open ImbalancedChen.PrimeProducts

variable {m : ℕ}

def amplitude (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ) (bs : Fin m → Block)
    (xi : Fin m → ℝ) : ℂ :=
  (frequencyScale^m)⁻¹ • physicalFourier m (blockChart kappa B N cj kappa0 bs) xi

theorem amplitude_integrable (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ)
    (bs : Fin m → Block) : Integrable (amplitude kappa B N cj kappa0 bs) := by
  exact (physicalFourier_integrable m _
    (euclideanLift_smooth m _ (chart_smooth kappa B N (singletonOwner m) (scales bs)
      (fun _ => R cj) kappa0))
    (euclideanLift_compact m _ (chart_compact kappa B N (singletonOwner m) (scales bs)
      (fun _ => R cj) kappa0))).const_smul _

/-- Retained-mode integration charges H's genuine Fourier L1 norm.
The estimate is independent of the cube volume and of every arithmetic
mode bound, which remains an open arithmetic obligation. -/
theorem exists_amplitude_l1_budget (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kappa : ℝ) N cj kappa0 m (bs : Fin m → Block),
      0 < N → m ≤ 6 →
      (∫ xi : Fin m → ℝ, ‖amplitude kappa B N cj kappa0 bs xi‖) ≤
        C * Real.log ((N : ℝ)+2)^(B*12) / 2^m := by
  obtain ⟨C, hC, hb⟩ := actual_fourier_l1_budget B
  refine ⟨C, hC, ?_⟩
  intro kappa N cj kappa0 m bs hN hm
  have hscale : 0 < (frequencyScale^m)⁻¹ := inv_pos.mpr (pow_pos frequencyScale_pos m)
  have hid : (∫ xi : Fin m → ℝ, ‖amplitude kappa B N cj kappa0 bs xi‖) =
      (∫ xi : Fin m → ℝ, ‖physicalFourier m (blockChart kappa B N cj kappa0 bs) xi‖) /
        frequencyScale^m := by
    simp only [amplitude, norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
    rw [integral_const_mul]
    ring
  rw [hid]
  exact hb kappa N m (singletonOwner m) (scales bs) (fun _ => R cj) kappa0
    (by exact_mod_cast hN) (scales_pos bs) (fun _ => ExactOriginalSmoothDyadicPartition.R_pos cj) hm

theorem amplitude_mode_integrable (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ)
    (bs : Fin m → Block) (n : Fin m → ℕ) :
    Integrable (fun xi => amplitude kappa B N cj kappa0 bs xi *
      occurrenceMode (scales bs) n xi) := by
  have hA := amplitude_integrable kappa B N cj kappa0 bs
  have hphase := physicalPhase_continuous m (WithLp.toLp 2 (logOccurrence (scales bs) n))
  apply hA.norm.mono'
  · simpa only [physicalPhase_occurrenceMode] using
      hA.aestronglyMeasurable.mul hphase.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun xi => by
      rw [norm_mul, ← physicalPhase_occurrenceMode, physicalPhase_norm, mul_one])

/-- The exact retained cube integral; every independent tensor mode
still carries the actual full modulus and the exact coprime mean. -/
theorem retainedAtom_eq_modes (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ)
    (bs : Fin m → Block) (Z : ℝ) (y : Fin m → ℝ) (rs : Fin m → Role)
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L H : ℝ) :
    retainedAtom kappa B N cj kappa0 bs Z y rs retainEven cap w z L H =
      ∫ xi in (outsideCube m H)ᶜ, amplitude kappa B N cj kappa0 bs xi *
        MellinInsertion20261028.exactDiscrepancy (rectangle bs)
          (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L)
          completeProduct N
          (fun n => hbSlots Z y rs n * occurrenceMode (scales bs) n xi) := by
  let c := fun n : Fin m → ℕ => ∑ q ∈ lowerQ retainEven N cap w z,
    lowerRho retainEven N cap w z L q *
      MellinInsertion20261028.residueKernel q N (completeProduct n)
  have hrep (n : Fin m → ℕ) :
      hbSlots Z y rs n * truncatedPhysical m (blockChart kappa B N cj kappa0 bs) H
          (WithLp.toLp 2 (logOccurrence (scales bs) n)) =
        ∫ xi in (outsideCube m H)ᶜ, amplitude kappa B N cj kappa0 bs xi *
          (hbSlots Z y rs n * occurrenceMode (scales bs) n xi) := by
    rw [truncatedPhysical, ← integral_smul, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun xi => by
      rw [physicalPhase_occurrenceMode]
      simp only [amplitude, smul_eq_mul]
      ring)
  have hint (n : Fin m → ℕ) :
      Integrable (fun xi => amplitude kappa B N cj kappa0 bs xi *
        (hbSlots Z y rs n * occurrenceMode (scales bs) n xi))
        (volume.restrict (outsideCube m H)ᶜ) := by
    have hi := ((amplitude_mode_integrable kappa B N cj kappa0 bs n).const_mul
      (hbSlots Z y rs n)).integrableOn
    apply hi.congr
    exact Filter.Eventually.of_forall (fun xi => by ring)
  change MellinInsertion20261028.functional (rectangle bs) c _ = _
  calc
    _ = MellinInsertion20261028.functional (rectangle bs) c (fun n =>
        ∫ xi in (outsideCube m H)ᶜ, amplitude kappa B N cj kappa0 bs xi *
          (hbSlots Z y rs n * occurrenceMode (scales bs) n xi)) := by
      unfold MellinInsertion20261028.functional
      apply Finset.sum_congr rfl
      intro n hn
      rw [hrep]
    _ = ∫ xi in (outsideCube m H)ᶜ,
        MellinInsertion20261028.functional (rectangle bs) c (fun n =>
          amplitude kappa B N cj kappa0 bs xi *
            (hbSlots Z y rs n * occurrenceMode (scales bs) n xi)) :=
      MellinInsertion20261028.functional_integral (rectangle bs) c _ (fun n hn => hint n)
    _ = _ := by
      simp_rw [MellinInsertion20261028.functional_mul]
      rfl

/-- The exact original order-three role list, retaining every repeated
Mobius and one slot and the one logarithmic slot. -/
def rowRoles (j : ℕ) : Fin (2*(j+1)) → Role :=
  fun a => (roles j).get ⟨a.val, by rw [roles_length]; exact a.isLt⟩

def literalRow (kappa : ℝ) (B N cj j : ℕ) (kappa0 : ℝ)
    (bs : Fin (2*(j+1)) → Block) (retainEven : List ℕ → Bool)
    (cap : ℕ) (w z L : ℝ) : ℂ :=
  SmoothChartHBDyadicPartition.scalar j *
    originalAtom kappa B N cj kappa0 bs (beforeHBCutoff 1 [cj])
      (fun _ => hbCutoff cj) (rowRoles j) retainEven cap w z L

def retainedLiteralRow (kappa : ℝ) (B N cj j : ℕ) (kappa0 : ℝ)
    (bs : Fin (2*(j+1)) → Block) (retainEven : List ℕ → Bool)
    (cap : ℕ) (w z L H : ℝ) : ℂ :=
  SmoothChartHBDyadicPartition.scalar j *
    retainedAtom kappa B N cj kappa0 bs (beforeHBCutoff 1 [cj])
      (fun _ => hbCutoff cj) (rowRoles j) retainEven cap w z L H

/-- Same signed HB scalar on both sides, not replaced by a marked-slot
restoring constant. Only the full-Q tail of this literal row is paid. -/
theorem exists_literal_row_tail (B : ℕ) (theta : ℝ) (htheta : theta < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kappa : ℝ) N cj j kappa0
      (bs : Fin (2*(j+1)) → Block) (retainEven : List ℕ → Bool)
      (cap D : ℕ) (w z L : ℝ) (accuracy : ℕ),
      kappa < 1 → 0 < N → j ∈ Finset.range 3 → Meets kappa B N cj kappa0 bs →
      1 ≤ D → (D : ℝ) ≤ (N : ℝ)^theta →
      lowerQ retainEven N cap w z ⊆ Finset.Icc 1 D →
      ‖literalRow kappa B N cj j kappa0 bs retainEven cap w z L -
        retainedLiteralRow kappa B N cj j kappa0 bs retainEven cap w z L
          (cutoff B N (2*(j+1)) accuracy)‖ ≤
        ‖SmoothChartHBDyadicPartition.scalar j‖ *
          (C * (N : ℝ) / CompleteProductTailDivisorBudgets.logScale (countingScale N)^(accuracy+3)) := by
  obtain ⟨C, hC, htail⟩ := exists_actual_lower_log_saving B theta htheta
  refine ⟨C, hC, ?_⟩
  intro kappa N cj j kappa0 bs retainEven cap D w z L accuracy
    hkappa hN hj hMeet hD hDtheta hQ
  have hm : 2*(j+1) ≤ 6 := by have := Finset.mem_range.mp hj; omega
  have ht := htail kappa N cj kappa0 (2*(j+1)) bs (beforeHBCutoff 1 [cj])
    (fun _ => hbCutoff cj) (rowRoles j) retainEven cap D w z L accuracy
    hkappa hN hm hMeet hD hDtheta hQ
  simpa only [literalRow, retainedLiteralRow, ← mul_sub, norm_mul] using
    mul_le_mul_of_nonneg_left ht (norm_nonneg (SmoothChartHBDyadicPartition.scalar j))

end
end ImbalancedChen.P5Z.ActualLowerRetainedCubeModes
