import ImbalancedChen.Part3RoughAuxiliarySW
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.RingTheory.RootsOfUnity.Complex

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Finite orthogonality, at the original progression modulus. The principal
-- term is the actual coefficient mass coprime to k*q, including all rough
-- exclusions and all weights. No equidistribution estimate is assumed.

namespace ImbalancedChen.Part3.RoughAPPrincipalCancellation20261027
noncomputable section
open Classical Finset
open scoped BigOperators

def twist (S : Finset ℕ) (α : ℕ → ℂ) (k : ℕ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ S, if n.Coprime k then α n * χ n else 0

theorem twist_principal (S : Finset ℕ) (α : ℕ → ℂ) (k q : ℕ) :
    twist S α k (1 : DirichletCharacter ℂ q) =
      ∑ n ∈ S, if n.Coprime (k*q) then α n else 0 := by
  unfold twist
  apply sum_congr rfl
  intro n _
  by_cases hk : n.Coprime k
  · by_cases hq : n.Coprime q
    · rw [if_pos hk, MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hq),
        mul_one, if_pos (hk.mul_right hq)]
    · have hnu : ¬IsUnit (n : ZMod q) :=
        fun h => hq ((ZMod.isUnit_iff_coprime n q).mp h)
      have hnot : ¬n.Coprime (k*q) :=
        fun h => hq (Nat.coprime_mul_iff_right.mp h).2
      rw [if_pos hk, MulChar.map_nonunit _ hnu, mul_zero, if_neg hnot]
  · have hnot : ¬n.Coprime (k*q) :=
      fun h => hk (Nat.coprime_mul_iff_right.mp h).1
    rw [if_neg hk, if_neg hnot]

-- This instance is constructed from the primary complex primitive-root
-- theorem, following the pinned multiplicative-character API.
private theorem kernel {q : ℕ} (hq : 0 < q) {b : ℕ} (hb : b.Coprime q) (n : ℕ) :
    (∑ χ : DirichletCharacter ℂ q, χ ((b : ZMod q)⁻¹) * χ n) =
      if Nat.ModEq q n b then (q.totient : ℂ) else 0 := by
  let : NeZero q := ⟨hq.ne'⟩
  have hexp : Monoid.exponent (ZMod q)ˣ ≠ 0 := Monoid.exponent_ne_zero.mpr
    (Monoid.ExponentExists.of_finite (G := (ZMod q)ˣ))
  let : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) := by
    let : NeZero (Monoid.exponent (ZMod q)ˣ) := ⟨hexp⟩
    refine { prim := ?_, cyc := ?_ }
    · exact ⟨Complex.exp (2 * Real.pi * Complex.I /
        (Monoid.exponent (ZMod q)ˣ : ℂ)),
        Complex.isPrimitiveRoot_exp (Monoid.exponent (ZMod q)ˣ) hexp⟩
    · infer_instance
  simpa only [ZMod.natCast_eq_natCast_iff, Nat.ModEq.comm] using
    (DirichletCharacter.sum_char_inv_mul_char_eq ℂ
      ((ZMod.isUnit_iff_coprime b q).mpr hb) (n : ZMod q))

theorem progression_expansion (S : Finset ℕ) (α : ℕ → ℂ) (k : ℕ)
    {q b : ℕ} (hq : 0 < q) (hb : b.Coprime q) :
    (∑ χ : DirichletCharacter ℂ q, χ ((b : ZMod q)⁻¹) * twist S α k χ) =
      (q.totient : ℂ) *
        ∑ n ∈ S, if Nat.ModEq q n b ∧ n.Coprime k then α n else 0 := by
  unfold twist
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro n _
  by_cases hk : n.Coprime k
  · simp only [if_pos hk, and_true]
    calc
      _ = α n * ∑ χ : DirichletCharacter ℂ q,
          χ ((b : ZMod q)⁻¹) * χ n := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro χ _
        ring
      _ = _ := by
        rw [kernel hq hb n]
        split_ifs <;> ring
  · simp only [if_neg hk, and_false, if_false, mul_zero, sum_const_zero]

-- Exact cancellation: no principal asymptotic, density surrogate, or
-- unrestricted coefficient mass replaces the original coprime mean.
theorem auxiliarySWError_eq_nonprincipal (S : Finset ℕ) (α : ℕ → ℂ) (k : ℕ)
    {q b : ℕ} (hq : 0 < q) (hb : b.Coprime q) :
    auxiliarySWError S α k q b =
      (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
        χ ((b : ZMod q)⁻¹) * twist S α k χ) / (q.totient : ℂ) := by
  have hphi : (q.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.totient_pos.mpr hq).ne'
  have hbunit : IsUnit (b : ZMod q) := (ZMod.isUnit_iff_coprime b q).mpr hb
  have hbinv : IsUnit ((b : ZMod q)⁻¹) := by
    rw [← hbunit.unit_spec, ZMod.inv_coe_unit]
    exact (hbunit.unit⁻¹).isUnit
  have he := Finset.sum_erase_add (Finset.univ : Finset (DirichletCharacter ℂ q))
    (fun χ => χ ((b : ZMod q)⁻¹) * twist S α k χ) (Finset.mem_univ 1)
  rw [progression_expansion S α k hq hb,
    MulChar.one_apply hbinv, one_mul, twist_principal] at he
  unfold auxiliarySWError
  apply (eq_div_iff hphi).mpr
  calc
    _ = (q.totient : ℂ) *
        (∑ n ∈ S, if Nat.ModEq q n b ∧ n.Coprime k then α n else 0) -
        (∑ n ∈ S, if n.Coprime (k*q) then α n else 0) := by field_simp; ring
    _ = _ := (eq_sub_of_add_eq he).symm

theorem auxiliarySWError_norm_le_nonprincipal (S : Finset ℕ) (α : ℕ → ℂ) (k : ℕ)
    {q b : ℕ} (hq : 0 < q) (hb : b.Coprime q) :
    ‖auxiliarySWError S α k q b‖ ≤
      (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖twist S α k χ‖) / (q.totient : ℝ) := by
  rw [auxiliarySWError_eq_nonprincipal S α k hq hb, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro χ _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (χ.norm_le_one ((b : ZMod q)⁻¹))
    (norm_nonneg _)).trans_eq (one_mul _)

-- The literal two rough families, with an arbitrary fixed complex weight.
-- In particular the weight may be a smooth profile times a Mellin phase.
def roughCoefficient (useMu : Bool) (z : ℝ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  (if useMu then roughMoebiusSlot z n else roughOneSlot z n) * w n

theorem rough_principal_exact (S : Finset ℕ) (useMu : Bool) (z : ℝ)
    (w : ℕ → ℂ) (k q : ℕ) :
    twist S (roughCoefficient useMu z w) k (1 : DirichletCharacter ℂ q) =
      ∑ n ∈ S, if n.Coprime (k*q) then
        (if useMu then roughMoebiusSlot z n else roughOneSlot z n) * w n else 0 :=
  twist_principal S (roughCoefficient useMu z w) k q

theorem rough_auxiliarySWError_eq_nonprincipal (S : Finset ℕ) (useMu : Bool)
    (z : ℝ) (w : ℕ → ℂ) (k : ℕ) {q b : ℕ}
    (hq : 0 < q) (hb : b.Coprime q) :
    auxiliarySWError S (roughCoefficient useMu z w) k q b =
      (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
        χ ((b : ZMod q)⁻¹) * twist S (roughCoefficient useMu z w) k χ) /
        (q.totient : ℂ) :=
  auxiliarySWError_eq_nonprincipal S (roughCoefficient useMu z w) k hq hb

end
end ImbalancedChen.Part3.RoughAPPrincipalCancellation20261027
