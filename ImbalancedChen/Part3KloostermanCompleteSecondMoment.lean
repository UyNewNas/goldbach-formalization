import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
import ImbalancedChen.Part3CenteredFourier
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED. Exact complete-residue second moment for the
literal `OriginalSmoothPoissonTail.kloosterman`. The sum is over all linear
frequencies modulo `c`; no individual-frequency estimate follows from it.
The identity includes `c = 1` and arbitrary composite positive moduli.
-/

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.CompleteSecondMomentSourceOnly

noncomputable section
open Classical Finset
open scoped BigOperators ComplexConjugate

private theorem star_char {c : ℕ} [NeZero c] (x : ZMod c) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hn : ‖ZMod.stdAddChar x‖ = 1 := by
    simpa only [ZMod.stdAddChar_apply] using Circle.norm_coe (ZMod.toCircle x)
  have hneg : ZMod.stdAddChar (-x) * ZMod.stdAddChar x = 1 := by
    rw [← ZMod.stdAddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hstar : star (ZMod.stdAddChar x) * ZMod.stdAddChar x = 1 := by
    rw [mul_comm]
    change ZMod.stdAddChar x * conj (ZMod.stdAddChar x) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn, one_pow,
      Complex.ofReal_one]
  exact (eq_inv_of_mul_eq_one_left hstar).trans
    (eq_inv_of_mul_eq_one_left hneg).symm

private theorem square_cast (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq]
  exact (Complex.mul_conj z).symm

/-- Unnormalised DFT Parseval on every residue, for an arbitrary complex
coefficient. The factor is exactly the cardinality of `ZMod c`. -/
theorem complete_additive_energy (c : ℕ) [NeZero c] (a : ZMod c → ℂ) :
    (∑ m : ZMod c,
      ‖∑ u : ZMod c, a u * ZMod.stdAddChar (m * u)‖ ^ 2) =
      (c : ℝ) * ∑ u : ZMod c, ‖a u‖ ^ 2 := by
  have hpoint (m : ZMod c) :
      ((‖∑ u : ZMod c, a u * ZMod.stdAddChar (m * u)‖ ^ 2 : ℝ) : ℂ) =
        ∑ u : ZMod c, ∑ v : ZMod c,
          a u * star (a v) * ZMod.stdAddChar (m * (u - v)) := by
    rw [square_cast, star_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro u _hu
    apply Finset.sum_congr rfl
    intro v _hv
    calc
      (a u * ZMod.stdAddChar (m * u)) *
          star (a v * ZMod.stdAddChar (m * v)) =
        a u * star (a v) *
          (ZMod.stdAddChar (m * u) *
            star (ZMod.stdAddChar (m * v))) := by
        rw [star_mul]
        ring
      _ = a u * star (a v) * ZMod.stdAddChar (m * (u - v)) := by
        rw [star_char, ← ZMod.stdAddChar.map_add_eq_mul]
        congr 1
        ring
  apply Complex.ofReal_injective
  calc
    (((∑ m : ZMod c,
        ‖∑ u : ZMod c, a u * ZMod.stdAddChar (m * u)‖ ^ 2) : ℝ) : ℂ) =
        ∑ m : ZMod c, ∑ u : ZMod c, ∑ v : ZMod c,
          a u * star (a v) * ZMod.stdAddChar (m * (u - v)) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      exact hpoint m
    _ = ∑ u : ZMod c, ∑ v : ZMod c,
          a u * star (a v) *
            (∑ m : ZMod c, ZMod.stdAddChar (m * (u - v))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Finset.mul_sum]
    _ = (c : ℂ) * ∑ u : ZMod c, a u * star (a u) := by
      simp_rw [ImbalancedChen.Part3.sum_stdAddChar_mul_eq]
      simp only [sub_eq_zero]
      simp [Finset.mul_sum, mul_assoc]
    _ = (((c : ℝ) * ∑ u : ZMod c, ‖a u‖ ^ 2 : ℝ) : ℂ) := by
      simp only [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro u _hu
      exact (square_cast (a u)).symm

/-- The literal original complete sum, sampled once per linear-frequency
residue. Its squared absolute values have total mass `c * phi(c)`. -/
theorem kloosterman_complete_second_moment (c : ℕ) [NeZero c] (n : ℤ) :
    (∑ m : ZMod c, ‖kloosterman c (m.val : ℤ) n‖ ^ 2) =
      (c : ℝ) * (Nat.totient c : ℝ) := by
  let a : ZMod c → ℂ := fun u =>
    if IsUnit u then ZMod.stdAddChar ((n : ZMod c) * u⁻¹) else 0
  have hK (m : ZMod c) :
      kloosterman c (m.val : ℤ) n =
        ∑ u : ZMod c, a u * ZMod.stdAddChar (m * u) := by
    rw [Physical.kloosterman_eq_zmod]
    apply Finset.sum_congr rfl
    intro u _hu
    by_cases hu : IsUnit u
    · simp only [a, if_pos hu, Int.cast_natCast, ZMod.natCast_zmod_val]
      rw [← ZMod.stdAddChar.map_add_eq_mul]
      congr 1
      ring
    · simp [a, hu]
  have hphase (u : ZMod c) :
      ‖a u‖ ^ 2 = if IsUnit u then (1 : ℝ) else 0 := by
    by_cases hu : IsUnit u
    · simp [a, hu, ZMod.stdAddChar_apply, Circle.norm_coe]
    · simp [a, hu]
  have hcountC :
      (∑ u : ZMod c, if IsUnit u then (1 : ℂ) else 0) =
        (Nat.totient c : ℂ) := by
    calc
      (∑ u : ZMod c, if IsUnit u then (1 : ℂ) else 0) =
          ∑ u : ZMod c, ∑ v : (ZMod c)ˣ,
            if u = (v : ZMod c) then (1 : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro u _hu
        exact (ImbalancedChen.Part3.sum_unitResidueIndicator c u).symm
      _ = ∑ v : (ZMod c)ˣ, (1 : ℂ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v _hv
        simp
      _ = (Nat.totient c : ℂ) := by
        simp [ZMod.card_units_eq_totient]
  have hcountR :
      (∑ u : ZMod c, if IsUnit u then (1 : ℝ) else 0) =
        (Nat.totient c : ℝ) := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum]
    have hterm (u : ZMod c) :
        (((if IsUnit u then (1 : ℝ) else 0) : ℝ) : ℂ) =
          if IsUnit u then (1 : ℂ) else 0 := by
      split_ifs <;> simp
    simp_rw [hterm]
    simpa only [Complex.ofReal_natCast] using hcountC
  calc
    (∑ m : ZMod c, ‖kloosterman c (m.val : ℤ) n‖ ^ 2) =
        ∑ m : ZMod c,
          ‖∑ u : ZMod c, a u * ZMod.stdAddChar (m * u)‖ ^ 2 := by
      simp_rw [hK]
    _ = (c : ℝ) * ∑ u : ZMod c, ‖a u‖ ^ 2 :=
      complete_additive_energy c a
    _ = (c : ℝ) * (Nat.totient c : ℝ) := by
      simp_rw [hphase]
      rw [hcountR]

end
end ImbalancedChen.Part3.OriginalSmoothPoissonTail.CompleteSecondMomentSourceOnly
