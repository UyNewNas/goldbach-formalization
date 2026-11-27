import ImbalancedChen.Part3PhysicalCompletedFrequencyDecay

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Hard finite-window tails of the ACTUAL completed frequency. The true
telescoping quadratic majorant is reused; no summability or truncation
estimate is assumed. The window contains zero, whose unchanged summand
is retained inside the finite sum. There is no smooth eta multiplier.
-/

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.HardCompletedSchwartz20261026b
noncomputable section
open Classical CommonSmoothCutoff
open scoped BigOperators SchwartzMap FourierTransform

def hardOmitted (K : Finset ℤ) (f : ℤ → ℂ) (m : ℤ) : ℂ :=
  if m ∈ K then 0 else f m

/-- The order r and its constant precede every physical scale, modulus,
residue and hard window. The estimate is absolute before later masses. -/
theorem frequency_hard_window_tail (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ M : ℝ, 0 < M → ∀ q : ℕ, 0 < q →
      ∀ Z : ℝ, 0 < Z → ∀ K : Finset ℤ, 0 ∈ K →
      (∀ m : ℤ, m ∉ K → Z ≤ |(M / (q : ℝ)) * (m : ℝ)|) →
      ∀ a y z : ℤ,
        Summable (fun m => ‖hardOmitted K (frequency M q a y z) m‖) ∧
        (∑' m : ℤ, ‖hardOmitted K (frequency M q a y z) m‖) ≤ A * (q : ℝ) / Z ^ (r - 1) ∧
        ‖(∑' m : ℤ, frequency M q a y z m) - ∑ m ∈ K, frequency M q a y z m‖ ≤
          A * (q : ℝ) / Z ^ (r - 1) := by
  obtain ⟨B, hB, hrapid⟩ := frequency_norm_rapidDecay (r + 1)
  refine ⟨2 * B, by positivity, ?_⟩
  intro M hM q hq Z hZ K hK0 hseparate a y z
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let t := M / (q : ℝ)
  have ht : 0 < t := div_pos hM hqR
  have hMt : M = (q : ℝ) * t := by dsimp [t]; field_simp [hqR.ne'] <;> ring
  obtain ⟨hDs, hDb⟩ := poissonNonzeroDecay_summable_tsum_le ht
  let E := B * (q : ℝ) / Z ^ (r - 1)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpoint (m : ℤ) : ‖hardOmitted K (frequency M q a y z) m‖ ≤
      E * poissonNonzeroDecay t m := by
    by_cases hmK : m ∈ K
    · simp only [hardOmitted, if_pos hmK, norm_zero]
      exact mul_nonneg hE (by
        unfold poissonNonzeroDecay
        split_ifs <;> positivity)
    · have hm0 : m ≠ 0 := by intro hm; subst m; exact hmK hK0
      let Q := 1 + |t * (m : ℝ)|
      have hQ : 0 < Q := by dsimp [Q]; positivity
      have hZQ : Z ≤ Q := by have h := hseparate m hmK; dsimp [Q, t]; linarith
      have hratio : B * (q : ℝ) / Q ^ (r - 1) ≤ B * (q : ℝ) / Z ^ (r - 1) :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hZ _)
          (pow_le_pow_left₀ hZ.le hZQ _)
      simp only [hardOmitted, if_neg hmK]
      calc
        _ ≤ B * M / Q ^ (r + 1) := hrapid M hM q hq a y z m
        _ = (B * (q : ℝ) / Q ^ (r - 1)) * (t / Q ^ 2) := by
          rw [show r + 1 = (r - 1) + 2 by omega, pow_add, hMt]
          field_simp [hQ.ne'] <;> ring
        _ ≤ (B * (q : ℝ) / Z ^ (r - 1)) * (t / Q ^ 2) :=
          mul_le_mul_of_nonneg_right hratio (by positivity)
        _ = _ := by simp only [E, poissonNonzeroDecay, if_neg hm0, Q]
  have hmajor : Summable (fun m : ℤ => E * poissonNonzeroDecay t m) := hDs.mul_left E
  have hnorm : Summable (fun m => ‖hardOmitted K (frequency M q a y z) m‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  have htail : (∑' m : ℤ, ‖hardOmitted K (frequency M q a y z) m‖) ≤
      (2 * B) * (q : ℝ) / Z ^ (r - 1) := by
    calc
      _ ≤ ∑' m : ℤ, E * poissonNonzeroDecay t m := hnorm.tsum_le_tsum hpoint hmajor
      _ = E * ∑' m : ℤ, poissonNonzeroDecay t m := tsum_mul_left
      _ ≤ E * 2 := mul_le_mul_of_nonneg_left hDb hE
      _ = _ := by dsimp [E]; ring
  have hf := frequency_summable M hM q hq a y z
  let inside : ℤ → ℂ := fun m => if m ∈ K then frequency M q a y z m else 0
  have hinside : Summable inside := by
    apply summable_of_ne_finset_zero (s := K)
    intro m hm
    exact if_neg hm
  have hinsum : (∑' m : ℤ, inside m) = ∑ m ∈ K, frequency M q a y z m := by
    calc
      _ = ∑ m ∈ K, inside m := tsum_eq_sum (fun m hm => if_neg hm)
      _ = _ := Finset.sum_congr rfl (fun m hm => if_pos hm)
  have hdiff : (fun m : ℤ => frequency M q a y z m - inside m) =
      hardOmitted K (frequency M q a y z) := by
    funext m
    by_cases hm : m ∈ K <;> simp only [inside, hardOmitted, hm, if_true, if_false, sub_self, sub_zero]
  refine ⟨hnorm, htail, ?_⟩
  rw [← hinsum, ← hf.tsum_sub hinside, hdiff]
  exact (norm_tsum_le_tsum_norm hnorm).trans htail

end
end ImbalancedChen.Part3.OriginalSmoothPoissonTail.HardCompletedSchwartz20261026b
