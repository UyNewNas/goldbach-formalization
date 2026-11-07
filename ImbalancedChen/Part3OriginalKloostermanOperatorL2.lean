import ImbalancedChen.Part3FiniteUnitInverseL2

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The LITERAL original Kloosterman matrix on every positive modulus q,
including composite q and q=1. It is DFT o unit-inverse restriction o DFT.
Its all-vector squared L2 operator bound is q^2, not q^2*phi(q).
An explicit nonzero unit-frequency character attains equality, so the
L2 operator bound q is sharp. No spectral or long-modulus return follows.
-/

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.FiniteOperator20261026b
noncomputable section
open Classical Finset
open scoped BigOperators

/-- The original complete sum, with the positive-frequency convention. -/
def originalOperator (q : ℕ) [NeZero q] (b : ZMod q → ℂ) (a : ZMod q) : ℂ :=
  ∑ n : ZMod q, kloosterman q (a.val : ℤ) (n.val : ℤ) * b n

theorem originalOperator_eq_two_dfts (q : ℕ) [NeZero q]
    (b : ZMod q → ℂ) (a : ZMod q) :
    originalOperator q b a = dft q (unitInversePullback q (dft q b)) a := by
  unfold originalOperator
  simp_rw [Physical.kloosterman_eq_zmod]
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold dft unitInversePullback
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hunit : IsUnit u
  · simp only [if_pos hunit,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [AddChar.map_add_eq_mul]
    simp only [mul_comm] <;> ring
  · simp [hunit]

theorem originalOperator_energy_exact (q : ℕ) [NeZero q] (b : ZMod q → ℂ) :
    energy q (originalOperator q b) =
      (q : ℝ) * ∑ u : ZMod q, if IsUnit u then ‖dft q b u‖^2 else 0 := by
  have hT : originalOperator q b = dft q (unitInversePullback q (dft q b)) :=
    funext (originalOperator_eq_two_dfts q b)
  rw [hT,dft_energy,unitInversePullback_energy]

/-- The all-vector operator estimate saves phi(q) against the general
matrix/Frobenius bound. It assumes no structure or target bound for b. -/
theorem originalOperator_energy_le (q : ℕ) [NeZero q] (b : ZMod q → ℂ) :
    energy q (originalOperator q b) ≤ (q : ℝ)^2 * energy q b := by
  have hT : originalOperator q b = dft q (unitInversePullback q (dft q b)) :=
    funext (originalOperator_eq_two_dfts q b)
  rw [hT,dft_energy]
  calc
    _ ≤ (q : ℝ)*energy q (dft q b) :=
      mul_le_mul_of_nonneg_left (unitInversePullback_energy_le q (dft q b)) (Nat.cast_nonneg _)
    _ = (q : ℝ)^2*energy q b := by rw [dft_energy]; ring

def vectorNorm (q : ℕ) [NeZero q] (b : ZMod q → ℂ) : ℝ := Real.sqrt (energy q b)

/-- Each unnormalised DFT has exact L2 norm factor sqrt(q). -/
theorem vectorNorm_dft (q : ℕ) [NeZero q] (b : ZMod q → ℂ) :
    vectorNorm q (dft q b) = Real.sqrt (q : ℝ)*vectorNorm q b := by
  unfold vectorNorm
  rw [dft_energy,Real.sqrt_mul (Nat.cast_nonneg q)]

/-- Numerical operator norm at most q for the finite L2 norm defined above. -/
theorem originalOperator_vectorNorm_le (q : ℕ) [NeZero q] (b : ZMod q → ℂ) :
    vectorNorm q (originalOperator q b) ≤ (q : ℝ)*vectorNorm q b := by
  have h := Real.sqrt_le_sqrt (originalOperator_energy_le q b)
  simpa only [vectorNorm,Real.sqrt_mul (sq_nonneg (q : ℝ)),Real.sqrt_sq (Nat.cast_nonneg q)] using h

def unitMode (q : ℕ) [NeZero q] (n : ZMod q) : ℂ := ZMod.stdAddChar (-n)

theorem dft_unitMode (q : ℕ) [NeZero q] (u : ZMod q) :
    dft q (unitMode q) u = if u = 1 then (q : ℂ) else 0 := by
  unfold dft unitMode
  have hchar (n : ZMod q) : ZMod.stdAddChar (-n)*ZMod.stdAddChar (u*n) =
      ZMod.stdAddChar (n*(u-1)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hchar,ImbalancedChen.Part3.sum_stdAddChar_mul_eq]
  simp only [sub_eq_zero]

theorem unitMode_energy (q : ℕ) [NeZero q] : energy q (unitMode q) = (q : ℝ) := by
  simp [energy,unitMode,ZMod.stdAddChar_apply,Circle.norm_coe,ZMod.card]

theorem unitMode_energy_pos (q : ℕ) [NeZero q] : 0 < energy q (unitMode q) := by
  rw [unitMode_energy]
  exact_mod_cast NeZero.pos q

/-- A concrete NONZERO input attains q^2 in squared norm, at every q.
Its input energy is q>0, including q=1. -/
theorem unitMode_attains_operator_energy (q : ℕ) [NeZero q] :
    energy q (originalOperator q (unitMode q)) = (q : ℝ)^2*energy q (unitMode q) := by
  rw [originalOperator_energy_exact]
  have hgate : (∑ u : ZMod q, if IsUnit u then ‖dft q (unitMode q) u‖^2 else 0) =
      energy q (dft q (unitMode q)) := by
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hunit : IsUnit u
    · simp [hunit]
    · have hu1 : u ≠ 1 := by
        intro heq
        subst u
        exact hunit isUnit_one
      simp [hunit,dft_unitMode,hu1]
  rw [hgate,dft_energy]
  ring

theorem unitMode_attains_operator_vectorNorm (q : ℕ) [NeZero q] :
    vectorNorm q (originalOperator q (unitMode q)) = (q : ℝ)*vectorNorm q (unitMode q) := by
  unfold vectorNorm
  rw [unitMode_attains_operator_energy,Real.sqrt_mul (sq_nonneg (q : ℝ)),
    Real.sqrt_sq (Nat.cast_nonneg q)]

end
end ImbalancedChen.Part3.OriginalSmoothPoissonTail.FiniteOperator20261026b
