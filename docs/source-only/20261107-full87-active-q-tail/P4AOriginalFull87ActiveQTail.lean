import ImbalancedChen.P4AOriginalFull87SharpMeanPaymentLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.
An original signed full-q coefficient may vanish on the displayed
physical carrier. The PP support permission concerns ACTUAL nonzero
rho, not every displayed q. This packet keeps the exact high-q tail,
retains beta and occurrence coefficients, and does not claim a cutoff
or pay a reserve.
-/

namespace ImbalancedChen.P4AOriginalFull87ActiveQTail
noncomputable section
open scoped Classical BigOperators

def activeFullQ (P : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : Finset ℕ :=
  (actualSmallRoughModuli (P false) N cap w z).filter
    (fun q => actualSmallRoughRho (P false) N cap w z L q ≠ 0)

/-- Same actual signed rho, with zero entries removed exactly. -/
theorem signed_full_q_eq_active
    (P : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (F : ℕ → ℝ) :
    (∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
      actualSmallRoughRho (P false) N cap w z L q * F q) =
      ∑ q ∈ activeFullQ P N cap w z L,
        actualSmallRoughRho (P false) N cap w z L q * F q := by
  classical
  unfold activeFullQ
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : actualSmallRoughRho (P false) N cap w z L q ≠ 0
  · simp [h]
  · have hz : actualSmallRoughRho (P false) N cap w z L q = 0 := by
      by_contra hn
      exact h hn
    simp [h, hz]

/-- Exact cutoff without discarding any old high-q contribution. The
range has the original globally zero-extended physical coefficient. -/
theorem signed_full_q_cutoff_with_tail
    (P : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    (∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
      actualSmallRoughRho (P false) N cap w z L q * F q) =
      (∑ q ∈ Finset.range (X + 1),
        actualSmallRoughRho (P false) N cap w z L q * F q) +
      (∑ q ∈ (actualSmallRoughModuli (P false) N cap w z).filter
          (fun q => X < q),
        actualSmallRoughRho (P false) N cap w z L q * F q) := by
  classical
  let Q := actualSmallRoughModuli (P false) N cap w z
  let ρ := actualSmallRoughRho (P false) N cap w z L
  have hsplit :
      (∑ q ∈ Q, ρ q * F q) =
        (∑ q ∈ Q.filter (fun q => q ≤ X), ρ q * F q) +
        (∑ q ∈ Q.filter (fun q => X < q), ρ q * F q) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q ≤ X
    · simp [hq, not_lt.mpr hq]
    · have hgt : X < q := Nat.lt_of_not_ge hq
      simp [hq, hgt]
  have hlow :
      (∑ q ∈ Q.filter (fun q => q ≤ X), ρ q * F q) =
        ∑ q ∈ Finset.range (X + 1), ρ q * F q := by
    have hsubset : Q.filter (fun q => q ≤ X) ⊆ Finset.range (X + 1) := by
      intro q hq
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hq).2)
    apply Finset.sum_subset hsubset
    intro q hrange hnot
    have hnotQ : q ∉ Q := by
      intro hqQ
      have hle : q ≤ X := Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)
      exact hnot (Finset.mem_filter.mpr ⟨hqQ, hle⟩)
    have hz : ρ q = 0 := by
      change actualSmallRoughRho (P false) N cap w z L q = 0
      unfold actualSmallRoughRho
      apply smallRoughRho_eq_zero_of_not_mem
      simpa only [actualSmallRoughModuli] using hnotQ
    simp [hz]
  change (∑ q ∈ Q, ρ q * F q) =
    (∑ q ∈ Finset.range (X + 1), ρ q * F q) +
    (∑ q ∈ Q.filter (fun q => X < q), ρ q * F q)
  rw [hsplit, hlow]

/-- Literal unpaid high-q tail is one-bounded by the original rho. -/
theorem signed_full_q_tail_abs_le
    (P : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |∑ q ∈ (actualSmallRoughModuli (P false) N cap w z).filter
        (fun q => X < q),
      actualSmallRoughRho (P false) N cap w z L q * F q| ≤
      ∑ q ∈ (actualSmallRoughModuli (P false) N cap w z).filter
        (fun q => X < q), |F q| := by
  classical
  calc
    _ ≤ ∑ q ∈ (actualSmallRoughModuli (P false) N cap w z).filter
        (fun q => X < q),
        |actualSmallRoughRho (P false) N cap w z L q * F q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ (actualSmallRoughModuli (P false) N cap w z).filter
        (fun q => X < q), |F q| := by
      apply Finset.sum_le_sum
      intro q _
      rw [abs_mul]
      calc
        |actualSmallRoughRho (P false) N cap w z L q| * |F q| ≤
            1 * |F q| :=
          mul_le_mul_of_nonneg_right
            (actualSmallRoughRho_abs_le_one (P false) N cap w z L q)
            (abs_nonneg (F q))
        _ = |F q| := one_mul _

/-- Nonzero q above X has its ACTUAL small-beta / rough decomposition:
the rough factor must exceed X relative to the same strict beta level.
This does not assert a rough bound from the causal parent policy. -/
theorem active_high_q_has_large_rough_factor
    (P : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (X q : ℕ)
    (hX : X < q)
    (hq : actualSmallRoughRho (P false) N cap w z L q ≠ 0) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ b ∈ fixedRoughSupport (P false) N cap w z,
        q = a * b ∧ (a : ℝ) < L ∧
          fixedRoughCoefficient (P false) N cap w z b ≠ 0 ∧
          (X : ℝ) < L * (b : ℝ) := by
  obtain ⟨a, ha, b, hb, hprod, haL, hbne⟩ :=
    actualSmallRoughRho_ne_zero_factors (P false) N cap w z L hq
  refine ⟨a, ha, b, hb, hprod, haL, hbne, ?_⟩
  have hgap : (X : ℝ) < (q : ℝ) := by exact_mod_cast hX
  rw [hprod, Nat.cast_mul] at hgap
  exact hgap.trans_le
    (mul_le_mul_of_nonneg_right haL.le (Nat.cast_nonneg b))

/-- The exact remaining licence: establish the cutoff only on ACTUAL
nonzero q, not on the displayed zero-extended support. -/
theorem signed_full_q_eq_licensed_range_of_active_bound
    (P : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (hactive : ∀ q ∈ activeFullQ P N cap w z L, q ≤ X) :
    (∑ q ∈ actualSmallRoughModuli (P false) N cap w z,
      actualSmallRoughRho (P false) N cap w z L q * F q) =
      ∑ q ∈ Finset.range (X + 1),
        actualSmallRoughRho (P false) N cap w z L q * F q := by
  classical
  have htail :
      (∑ q ∈ (actualSmallRoughModuli (P false) N cap w z).filter
        (fun q => X < q),
        actualSmallRoughRho (P false) N cap w z L q * F q) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hQ, hgt⟩
    have hz : actualSmallRoughRho (P false) N cap w z L q = 0 := by
      by_contra hneq
      exact (Nat.not_le.mpr hgt)
        (hactive q (Finset.mem_filter.mpr ⟨hQ, hneq⟩))
    simp [hz]
  rw [signed_full_q_cutoff_with_tail P N cap w z L X F, htail, add_zero]

end
end ImbalancedChen.P4AOriginalFull87ActiveQTail
