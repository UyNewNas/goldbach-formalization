import ImbalancedChen.Part3PhysicalCommonHardFrequencyWindow
import ImbalancedChen.Part3ActualAmplitudeResidueAlias

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Scalar Fourier-amplitude hard tail, with NO Kloosterman q factor, and an
infinite-to-finite residue pushforward L1-to-L2 contraction. The bound is
the SQUARE OF TOTAL outside-window amplitude L1 mass, not a sum of
per-residue global bounds (which would introduce an artificial q factor).
All actual scalar masks are kept and bounded by their proved unit norm.
-/

namespace ImbalancedChen.Part3.ActualCompletedLeftHardTail20261026b
noncomputable section
open Classical CommonSmoothCutoff OriginalSmoothPoissonTail
open OriginalSmoothPoissonTail.FiniteSource20261026b
open HardCompletedSchwartz20261026b
open ActualCompletedPairYFibres20261026b
open scoped BigOperators SchwartzMap FourierTransform

def residuePushforward {R : Type*} [Fintype R] (rho : ℤ → R) (f : ℤ → ℂ) (u : R) : ℂ :=
  ∑' m : ℤ, if rho m = u then f m else 0

/-- Arbitrary residue collisions are retained; no injectivity or unit
assumption is needed for this tail contraction. -/
theorem residuePushforward_energy_le {R : Type*} [Fintype R]
    (rho : ℤ → R) (f : ℤ → ℂ) (hf : Summable (fun m => ‖f m‖)) :
    (∑ u : R, ‖residuePushforward rho f u‖ ^ 2) ≤ (∑' m : ℤ, ‖f m‖) ^ 2 := by
  let b : R → ℝ := fun u => ∑' m : ℤ, if rho m = u then ‖f m‖ else 0
  have hs (u : R) : Summable (fun m : ℤ => if rho m = u then ‖f m‖ else 0) := by
    apply hf.of_nonneg_of_le (fun _ => by split_ifs <;> positivity)
    intro m
    split_ifs <;> simp only [le_refl, norm_nonneg]
  have hb (u : R) : 0 ≤ b u := tsum_nonneg (fun _ => by split_ifs <;> positivity)
  have hpoint (u : R) : ‖residuePushforward rho f u‖ ≤ b u := by
    have hnorm : Summable (fun m : ℤ => ‖if rho m = u then f m else 0‖) := by
      simpa only [apply_ite, norm_zero] using hs u
    simpa only [residuePushforward, apply_ite, norm_zero, b] using norm_tsum_le_tsum_norm hnorm
  have htotal : (∑ u : R, b u) = ∑' m : ℤ, ‖f m‖ := by
    calc
      _ = ∑' m : ℤ, ∑ u : R, if rho m = u then ‖f m‖ else 0 :=
        (Summable.tsum_finsetSum (fun u _ => hs u)).symm
      _ = _ := by apply tsum_congr; intro m; simp
  calc
    _ ≤ ∑ u : R, (b u) ^ 2 := Finset.sum_le_sum
      (fun u _ => pow_le_pow_left₀ (norm_nonneg _) (hpoint u) 2)
    _ ≤ (∑ u : R, b u) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun u _ => hb u)
    _ = _ := by rw [htotal]

theorem actualCommonScalar_norm_le_one (q z : ℕ) (N : ℝ) : ‖actualCommonScalar q z N‖ ≤ 1 := by
  unfold actualCommonScalar
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (scaledDyadicCutoff_nonneg N q)]
    exact scaledDyadicCutoff_le_one N q
  · simp

def amplitudeTailL1 (K : Finset ℤ) (M : ℝ) (q : ℕ) : ℝ :=
  ∑' m : ℤ, ‖hardOmitted K (frequencyAmplitude M q) m‖

/-- True scalar-amplitude hard tail. The constant precedes all M,q,Z,K;
unlike the completed-frequency estimate there is NO q on the right. -/
theorem amplitude_hard_tail (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ M : ℝ, 0 < M → ∀ q : ℕ, 0 < q →
      ∀ Z : ℝ, 0 < Z → ∀ K : Finset ℤ, 0 ∈ K →
      (∀ m : ℤ, m ∉ K → Z ≤ |(M / (q : ℝ)) * (m : ℝ)|) →
      Summable (fun m => ‖hardOmitted K (frequencyAmplitude M q) m‖) ∧
        amplitudeTailL1 K M q ≤ A / Z ^ (r - 1) := by
  obtain ⟨B, hB, hdecay⟩ := schwartz_norm_le_rapidDecay (𝓕 dyadicCutoffSchwartz) (r + 1)
  refine ⟨2 * B, by positivity, ?_⟩
  intro M hM q hq Z hZ K hK0 hsep
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let t := M / (q : ℝ)
  have ht : 0 < t := div_pos hM hqR
  obtain ⟨hDs, hDb⟩ := poissonNonzeroDecay_summable_tsum_le ht
  let E := B / Z ^ (r - 1)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpoint (m : ℤ) : ‖hardOmitted K (frequencyAmplitude M q) m‖ ≤
      E * poissonNonzeroDecay t m := by
    by_cases hmK : m ∈ K
    · simp only [hardOmitted, if_pos hmK, norm_zero]
      exact mul_nonneg hE (by unfold poissonNonzeroDecay; split_ifs <;> positivity)
    · have hm0 : m ≠ 0 := by intro h; subst m; exact hmK hK0
      let Q := 1 + |t * (m : ℝ)|
      have hQ : 0 < Q := by dsimp [Q]; positivity
      have hZQ : Z ≤ Q := by have h := hsep m hmK; dsimp [Q, t]; linarith
      have hratio : B / Q ^ (r - 1) ≤ B / Z ^ (r - 1) :=
        div_le_div_of_nonneg_left hB.le (pow_pos hZ _) (pow_le_pow_left₀ hZ.le hZQ _)
      simp only [hardOmitted, if_neg hmK, frequencyAmplitude, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht]
      calc
        _ ≤ t * (B / Q ^ (r + 1)) := mul_le_mul_of_nonneg_left (hdecay _) ht.le
        _ = (B / Q ^ (r - 1)) * (t / Q ^ 2) := by
          rw [show r + 1 = (r - 1) + 2 by omega, pow_add]
          field_simp [hQ.ne'] <;> ring
        _ ≤ (B / Z ^ (r - 1)) * (t / Q ^ 2) :=
          mul_le_mul_of_nonneg_right hratio (by positivity)
        _ = _ := by simp only [E, poissonNonzeroDecay, if_neg hm0, Q]
  have hmajor : Summable (fun m : ℤ => E * poissonNonzeroDecay t m) := hDs.mul_left E
  have hn : Summable (fun m => ‖hardOmitted K (frequencyAmplitude M q) m‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  refine ⟨hn, ?_⟩
  calc
    _ ≤ ∑' m : ℤ, E * poissonNonzeroDecay t m := hn.tsum_le_tsum hpoint hmajor
    _ = E * ∑' m : ℤ, poissonNonzeroDecay t m := tsum_mul_left
    _ ≤ E * 2 := mul_le_mul_of_nonneg_left hDb hE
    _ = _ := by dsimp [E]; ring

end
end ImbalancedChen.Part3.ActualCompletedLeftHardTail20261026b
