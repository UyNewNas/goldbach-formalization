import ImbalancedChen.Part3AmplitudeHardTailEnergyContraction
import ImbalancedChen.Part3ActualFullLeftCollisionEnergy

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Native raw eta=1 finite completed-left collision energy. The finite energy
is NOT bounded by full energy alone: their exact residual residue vector
is proved, its energy is bounded by TOTAL amplitude-tail L1 squared, and
the factor-two square inequality is applied before the frozen actual full
alias energy. The original inverse-z fibre and common scalar remain;
the full supplier proves its unit permutation or zero nonunit gate.
No arbitrary eta, f/u/v right coefficient, or final7/32 claim occurs.
-/

namespace ImbalancedChen.Part3.ActualCompletedLeftHardTail20261026b
noncomputable section
open Classical CommonSmoothCutoff OriginalSmoothPoissonTail
open OriginalSmoothPoissonTail.FiniteSource20261026b
open OriginalSmoothPoissonTail.FiniteOperator20261026b
open ActualCompletedPairYFibres20261026b ActualCompletedPairSharpL220261026b
open ActualCompletedLeftAlias20261026b HardCompletedSchwartz20261026b
open scoped BigOperators

def actualLeftTailResidue (q z : ℕ) [NeZero q] (K : Finset ℤ) (M N : ℝ) : ZMod q → ℂ :=
  residuePushforward (fun m : ℤ => ((m * inverseResidue q (z : ℤ) : ℤ) : ZMod q))
    (fun m => actualCommonScalar q z N * hardOmitted K (frequencyAmplitude M q) m)

/-- Exact native finite/full difference, with the actual inverse-z residue
gate. No positivity or energy inequality is used to identify the tail. -/
theorem actualFullLeft_sub_finite_raw (q z : ℕ) [NeZero q] {M : ℝ} (hM : 0 < M)
    (N : ℝ) (K : Finset ℤ) (u : ZMod q) :
    actualFullLeftCollision q z M N u - actualLeftCollision q z K (fun _ => 1) M N u =
      actualLeftTailResidue q z K M N u := by
  let f : ℤ → ℂ := fun m =>
    if ((m * inverseResidue q (z : ℤ) : ℤ) : ZMod q) = u then
      actualCommonScalar q z N * frequencyAmplitude M q m else 0
  let g : ℤ → ℂ := fun m => if m ∈ K then f m else 0
  have hf : Summable f := (actualFullLeftCollision_summable_norm q z hM N u).of_norm
  have hg : Summable g := by
    apply summable_of_ne_finset_zero (s := K)
    intro m hm
    exact if_neg hm
  have hgsum : (∑' m : ℤ, g m) = ∑ m ∈ K, f m := by
    calc
      _ = ∑ m ∈ K, g m := tsum_eq_sum (fun m hm => if_neg hm)
      _ = _ := Finset.sum_congr rfl (fun m hm => if_pos hm)
  rw [actualLeftCollision_raw_eq_sum]
  change (∑' m : ℤ, f m) - (∑ m ∈ K, f m) = _
  rw [← hgsum, ← hf.tsum_sub hg]
  unfold actualLeftTailResidue residuePushforward
  apply tsum_congr
  intro m
  by_cases hm : m ∈ K <;>
    by_cases hu : ((m * inverseResidue q (z : ℤ) : ℤ) : ZMod q) = u <;>
      simp only [f, g, hardOmitted, hm, hu, if_true, if_false, mul_zero, sub_self, sub_zero]

/-- Every residual residue is paid by the SAME total amplitude tail.
The scalar is bounded by one; there is no residue or completed-mode count. -/
theorem actualLeftTailResidue_energy_le (q z : ℕ) [NeZero q] {M : ℝ} (hM : 0 < M)
    (N : ℝ) (K : Finset ℤ) :
    energy q (actualLeftTailResidue q z K M N) ≤ (amplitudeTailL1 K M q) ^ 2 := by
  have hAmp := amplitude_summable_norm q hM
  have hTail : Summable (fun m : ℤ => ‖hardOmitted K (frequencyAmplitude M q) m‖) := by
    apply hAmp.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro m
    by_cases hm : m ∈ K <;> simp only [hardOmitted, hm, if_true, if_false, norm_zero,
      norm_nonneg, le_refl]
  let f : ℤ → ℂ := fun m => actualCommonScalar q z N * hardOmitted K (frequencyAmplitude M q) m
  have hpoint (m : ℤ) : ‖f m‖ ≤ ‖hardOmitted K (frequencyAmplitude M q) m‖ := by
    rw [f, norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (ImbalancedChen.Part3.ActualCompletedLeftHardTail20261026b.actualCommonScalar_norm_le_one q z N)
      (norm_nonneg (hardOmitted K (frequencyAmplitude M q) m))
  have hf : Summable (fun m => ‖f m‖) := hTail.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  have htotal : (∑' m : ℤ, ‖f m‖) ≤ amplitudeTailL1 K M q := hf.tsum_le_tsum hpoint hTail
  have henergy := residuePushforward_energy_le
    (fun m : ℤ => ((m * inverseResidue q (z : ℤ) : ℤ) : ZMod q)) f hf
  calc
    _ ≤ (∑' m : ℤ, ‖f m‖) ^ 2 := henergy
    _ ≤ _ := pow_le_pow_left₀ (tsum_nonneg (fun _ => norm_nonneg _)) htotal 2

/-- Cancellation-correct factor-two comparison for the actual RAW finite
left coefficient. The all-m alias energy is never used monotonically. -/
theorem actualFiniteLeft_energy_le_full_add_tail (q z : ℕ) [NeZero q] {M : ℝ} (hM : 0 < M)
    (N : ℝ) (K : Finset ℤ) :
    energy q (actualLeftCollision q z K (fun _ => 1) M N) ≤
      2 * energy q (actualFullLeftCollision q z M N) + 2 * (amplitudeTailL1 K M q) ^ 2 := by
  have hpoint (u : ZMod q) :
      ‖actualLeftCollision q z K (fun _ => 1) M N u‖ ^ 2 ≤
        2 * ‖actualFullLeftCollision q z M N u‖ ^ 2 +
          2 * ‖actualLeftTailResidue q z K M N u‖ ^ 2 := by
    have heq : actualFullLeftCollision q z M N u - actualLeftTailResidue q z K M N u =
        actualLeftCollision q z K (fun _ => 1) M N u := by
      rw [← actualFullLeft_sub_finite_raw q z hM N K u]
      ring
    have hn := norm_sub_le (actualFullLeftCollision q z M N u) (actualLeftTailResidue q z K M N u)
    rw [heq] at hn
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖actualFullLeftCollision q z M N u‖ - ‖actualLeftTailResidue q z K M N u‖)]
  calc
    _ ≤ ∑ u : ZMod q, (2 * ‖actualFullLeftCollision q z M N u‖ ^ 2 +
        2 * ‖actualLeftTailResidue q z K M N u‖ ^ 2) := Finset.sum_le_sum (fun u _ => hpoint u)
    _ = 2 * energy q (actualFullLeftCollision q z M N) +
        2 * energy q (actualLeftTailResidue q z K M N) := by
      simp only [energy, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add_left
      (mul_le_mul_of_nonneg_left (actualLeftTailResidue_energy_le q z hM N K) (by norm_num)) _

theorem actualFiniteLeft_energy_le_native_full (q z : ℕ) [NeZero q] {M : ℝ} (hM : 0 < M)
    (N : ℝ) (K : Finset ℤ) :
    energy q (actualLeftCollision q z K (fun _ => 1) M N) ≤
      18 * (M / (q : ℝ)) * (1 + M / (q : ℝ)) + 2 * (amplitudeTailL1 K M q) ^ 2 := by
  have h := actualFiniteLeft_energy_le_full_add_tail q z hM N K
  have hfull := actualFullLeftCollision_energy_le q z hM N
  nlinarith only [h, hfull]

/-- One common raw hard K, chosen before every original level/factor,
removes the phase8 artificial completed-mode/fibre factor from the finite
left energy. The only extra term is the square of the paid amplitude tail. -/
theorem actualFiniteLeft_common_hard_energy (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : ℝ, 0 < C → ∀ M : ℝ, 0 < M →
      ∀ Z : ℝ, 0 < Z → ∀ (q z : ℕ) [NeZero q], (q : ℝ) ≤ 10 * C → ∀ N : ℝ,
      energy q (actualLeftCollision q z (commonHardWindow C M Z) (fun _ => 1) M N) ≤
        18 * (M / (q : ℝ)) * (1 + M / (q : ℝ)) + 2 * (A / Z ^ (r - 1)) ^ 2 := by
  obtain ⟨A, hA, hamp⟩ := amplitude_hard_tail r hr
  refine ⟨A, hA, ?_⟩
  intro C hC M hM Z hZ q z inst hqC N
  letI : NeZero q := inst
  have htail := (hamp M hM q (NeZero.pos q) Z hZ (commonHardWindow C M Z)
    (zero_mem_commonHardWindow C M Z)
    (fun m hm => outside_commonHardWindow_frequency C M Z hC hM hZ q (NeZero.pos q) hqC m hm)).2
  have hsq := pow_le_pow_left₀ (tsum_nonneg (fun _ => norm_nonneg _)) htail 2
  have hbase := actualFiniteLeft_energy_le_native_full q z hM N (commonHardWindow C M Z)
  linarith

end
end ImbalancedChen.Part3.ActualCompletedLeftHardTail20261026b
