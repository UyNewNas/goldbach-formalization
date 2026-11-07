import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24.
Pure finite reflection and harmonic estimates for the common-interval DFT
completion. This file proves no pointwise chord estimate for that DFT.
The final theorem consumes only explicit scalar coefficient norm bounds.
-/

namespace ImbalancedChen.Part3.IntervalHarmonicPairBoundSourceOnly
noncomputable section

open Classical
open scoped BigOperators

/-- Reflection of the complete nonzero residue representative interval. -/
theorem reciprocal_reflection_sum (N : ℕ) :
    (∑ r ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / ((N - r : ℕ) : ℝ)) =
      ∑ j ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / (j : ℝ) := by
  refine Finset.sum_bij' (fun r _hr => N - r) (fun j _hj => N - j)
    (fun r hr => ?_) (fun j hj => ?_) (fun r hr => ?_)
    (fun j hj => ?_) (fun _r _hr => rfl)
  · simp only [Finset.mem_Icc] at hr ⊢
    omega
  · simp only [Finset.mem_Icc] at hj ⊢
    omega
  · simp only [Finset.mem_Icc] at hr
    omega
  · simp only [Finset.mem_Icc] at hj
    omega

theorem reciprocal_min_le_pair (N r : ℕ) :
    (1 : ℝ) / ((min r (N - r) : ℕ) : ℝ) ≤
      (1 : ℝ) / (r : ℝ) + (1 : ℝ) / ((N - r : ℕ) : ℝ) := by
  by_cases h : r ≤ N - r
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (by positivity)
  · rw [min_eq_right (le_of_not_ge h)]
    exact le_add_of_nonneg_left (by positivity)

/-- Exact reflection gives the factor two; it does not discard an endpoint. -/
theorem reciprocal_min_sum_le_twice (N : ℕ) :
    (∑ r ∈ Finset.Icc 1 (N - 1),
      (1 : ℝ) / ((min r (N - r) : ℕ) : ℝ)) ≤
      2 * ∑ j ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / (j : ℝ) := by
  calc
    (∑ r ∈ Finset.Icc 1 (N - 1),
        (1 : ℝ) / ((min r (N - r) : ℕ) : ℝ)) ≤
        ∑ r ∈ Finset.Icc 1 (N - 1),
          ((1 : ℝ) / (r : ℝ) + (1 : ℝ) / ((N - r : ℕ) : ℝ)) := by
      exact Finset.sum_le_sum (fun r _hr => reciprocal_min_le_pair N r)
    _ = _ := by
      rw [Finset.sum_add_distrib, reciprocal_reflection_sum]
      ring

theorem real_reciprocal_sum_eq_harmonic (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, (1 : ℝ) / (j : ℝ)) = (harmonic n : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, one_div]

/-- Enlarge the final endpoint by one before applying the pinned harmonic bound. -/
theorem reciprocal_sum_le_one_add_log (N : ℕ) :
    (∑ j ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / (j : ℝ)) ≤ 1 + Real.log N := by
  calc
    (∑ j ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / (j : ℝ)) ≤
        ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        rcases Finset.mem_Icc.mp hj with ⟨hl, hu⟩
        exact Finset.mem_Icc.mpr ⟨hl, le_trans hu (Nat.sub_le N 1)⟩
      · intro j _hj _hj'
        positivity
    _ = (harmonic N : ℝ) := real_reciprocal_sum_eq_harmonic N
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N

theorem reciprocal_min_sum_le_log (N : ℕ) :
    (∑ r ∈ Finset.Icc 1 (N - 1),
      (1 : ℝ) / ((min r (N - r) : ℕ) : ℝ)) ≤
        2 * (1 + Real.log N) := by
  exact (reciprocal_min_sum_le_twice N).trans
    (mul_le_mul_of_nonneg_left (reciprocal_sum_le_one_add_log N) (by norm_num))

/-- The natural representatives of all nonzero cyclic residues, once each. -/
theorem sum_nonzero_zmod_reindex (N : ℕ) [NeZero N] (f : ℕ → ℝ) :
    (∑ r ∈ (Finset.univ : Finset (ZMod N)).erase 0, f r.val) =
      ∑ j ∈ Finset.Icc 1 (N - 1), f j := by
  refine Finset.sum_bij' (fun r _hr => r.val) (fun j _hj => (j : ZMod N))
    (fun r hr => ?_) (fun j hj => ?_) (fun r _hr => ?_)
    (fun j hj => ?_) (fun _r _hr => rfl)
  · have hr0 : r ≠ 0 := (Finset.mem_erase.mp hr).1
    have hv0 : r.val ≠ 0 := fun hz => hr0 ((ZMod.val_eq_zero r).mp hz)
    have hvN := ZMod.val_lt r
    apply Finset.mem_Icc.mpr
    omega
  · rcases Finset.mem_Icc.mp hj with ⟨hl, hu⟩
    have hjN : j < N := by omega
    apply Finset.mem_erase.mpr
    constructor
    · intro hz
      have hv := congrArg ZMod.val hz
      rw [ZMod.val_natCast_of_lt hjN, ZMod.val_zero] at hv
      omega
    · exact Finset.mem_univ _
  · exact ZMod.natCast_zmod_val r
  · exact ZMod.val_natCast_of_lt (by
      rcases Finset.mem_Icc.mp hj with ⟨hl, hu⟩
      omega)

theorem half_reciprocal_min_sum_le_log (N : ℕ) :
    (∑ r ∈ Finset.Icc 1 (N - 1),
      (1 : ℝ) / (2 * ((min r (N - r) : ℕ) : ℝ))) ≤ 1 + Real.log N := by
  calc
    (∑ r ∈ Finset.Icc 1 (N - 1),
        (1 : ℝ) / (2 * ((min r (N - r) : ℕ) : ℝ))) =
        (1 / 2 : ℝ) * ∑ r ∈ Finset.Icc 1 (N - 1),
          (1 : ℝ) / ((min r (N - r) : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      simp only [one_div, mul_inv_rev]
      ring
    _ ≤ (1 / 2 : ℝ) * (2 * (1 + Real.log N)) :=
      mul_le_mul_of_nonneg_left (reciprocal_min_sum_le_log N) (by norm_num)
    _ = 1 + Real.log N := by ring

/-- Pure coefficient consequence. The hypotheses are ordinary finite scalar
norm bounds; no spectral or packet estimate is assumed. -/
theorem cyclic_coefficient_l1_le_two_add_log (N : ℕ) [NeZero N]
    (hN : 2 ≤ N) (coeff : ZMod N → ℂ)
    (hzero : ‖coeff 0‖ ≤ 1)
    (hnonzero : ∀ r : ZMod N, r ≠ 0 →
      ‖coeff r‖ ≤ (1 : ℝ) / (2 * ((min r.val (N - r.val) : ℕ) : ℝ))) :
    (∑ r : ZMod N, ‖coeff r‖) ≤ 2 + Real.log N := by
  have htail : (∑ r ∈ (Finset.univ : Finset (ZMod N)).erase 0, ‖coeff r‖) ≤
      1 + Real.log N := by
    calc
      (∑ r ∈ (Finset.univ : Finset (ZMod N)).erase 0, ‖coeff r‖) =
          ∑ j ∈ Finset.Icc 1 (N - 1), ‖coeff (j : ZMod N)‖ := by
        simpa only [ZMod.natCast_zmod_val] using
          sum_nonzero_zmod_reindex N (fun j => ‖coeff (j : ZMod N)‖)
      _ ≤ ∑ j ∈ Finset.Icc 1 (N - 1),
          (1 : ℝ) / (2 * ((min j (N - j) : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        rcases Finset.mem_Icc.mp hj with ⟨hl, hu⟩
        have hjN : j < N := by omega
        have hj0 : (j : ZMod N) ≠ 0 := by
          intro hz
          have hv := congrArg ZMod.val hz
          rw [ZMod.val_natCast_of_lt hjN, ZMod.val_zero] at hv
          omega
        simpa only [ZMod.val_natCast_of_lt hjN] using hnonzero (j : ZMod N) hj0
      _ ≤ 1 + Real.log N := half_reciprocal_min_sum_le_log N
  calc
    (∑ r : ZMod N, ‖coeff r‖) =
        (∑ r ∈ (Finset.univ : Finset (ZMod N)).erase 0, ‖coeff r‖) + ‖coeff 0‖ :=
      (Finset.sum_erase_add (Finset.univ : Finset (ZMod N))
        (fun r => ‖coeff r‖) (Finset.mem_univ (0 : ZMod N))).symm
    _ ≤ (1 + Real.log N) + 1 := add_le_add htail hzero
    _ = 2 + Real.log N := by ring

end
end ImbalancedChen.Part3.IntervalHarmonicPairBoundSourceOnly
