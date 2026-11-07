import ImbalancedChen.Part3SignedIntervalResidueOccupancy
import ImbalancedChen.Part3OriginalSeparableKloostermanPacket

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

The actual packetRightCoefficient is the COMPLEX SIGNED pushforward
y |-> a*y mod q. Its residue collision energy is bounded by the sharp
interval occupancy times its genuine INTEGER-y coefficient energy.
Arbitrary complex coefficients, zero/nonunit a, y=0 and empty carriers
are included. A second API needs interval support only where beta!=0.

No coefficient-norm target, factorable beta, unit multiplier, spectral
bound, 576 incidence estimate, or actual physical support is assumed.
The original source owner supplies its physical output support separately.
-/

namespace ImbalancedChen.Part3.SignedResiduePushforwardEnergy20261026b

noncomputable section
open Classical Finset
open scoped BigOperators
open SignedIntervalResidueOccupancy20261026b
open OriginalSmoothPoissonTail.FiniteOperator20261026b

def collisionFactor (q : ℕ) (a L U : ℤ) : ℝ :=
  1 + ((U : ℝ) - L) * (q.gcd a.natAbs : ℝ) / q

theorem collisionFactor_nonneg (q : ℕ) (a L U : ℤ) (hLU : L ≤ U) :
    0 ≤ collisionFactor q a L U := by
  have hspan : (0 : ℝ) ≤ (U : ℝ) - L := by exact_mod_cast (sub_nonneg.mpr hLU)
  have hterm := div_nonneg (mul_nonneg hspan (Nat.cast_nonneg (q.gcd a.natAbs))) (Nat.cast_nonneg q)
  unfold collisionFactor
  linarith

/-- Literal equality, with every signed summand still INSIDE its fibre. -/
theorem packetRightCoefficient_eq_fibre_sum (q : ℕ) [NeZero q] (S : Finset ℤ)
    (beta : ℤ → ℂ) (a : ℤ) (v : ZMod q) :
    packetRightCoefficient q S beta a v = ∑ y ∈ residueFibre S q a v, beta y := by
  simp only [packetRightCoefficient, residueFibre, Finset.sum_filter]

theorem packetRightCoefficient_fibre_norm_sq_le (q : ℕ) [NeZero q] (S : Finset ℤ)
    (beta : ℤ → ℂ) (a : ℤ) (v : ZMod q) :
    ‖packetRightCoefficient q S beta a v‖ ^ 2 ≤
      ((residueFibre S q a v).card : ℝ) * ∑ y ∈ residueFibre S q a v, ‖beta y‖ ^ 2 := by
  rw [packetRightCoefficient_eq_fibre_sum]
  have h := ImbalancedChen.Part3.complex_finset_cauchy_norm_sq (residueFibre S q a v)
    (fun _ => (1 : ℂ)) beta
  simpa only [one_mul, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using h

/-- The complete residue fibres partition integer-y energy exactly, even
when a=0 and all y collide, or when some residue fibres are incompatible. -/
theorem sum_fibre_integer_energy (q : ℕ) [NeZero q] (S : Finset ℤ)
    (beta : ℤ → ℂ) (a : ℤ) :
    (∑ v : ZMod q, ∑ y ∈ residueFibre S q a v, ‖beta y‖ ^ 2) =
      ∑ y ∈ S, ‖beta y‖ ^ 2 := by
  simp only [residueFibre, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _hy
  simp

theorem packetRight_energy_le_integer_energy (q : ℕ) [NeZero q] (S : Finset ℤ)
    (beta : ℤ → ℂ) (a L U : ℤ) (hLU : L ≤ U)
    (hS : ∀ y ∈ S, L ≤ y ∧ y ≤ U) :
    energy q (packetRightCoefficient q S beta a) ≤
      collisionFactor q a L U * ∑ y ∈ S, ‖beta y‖ ^ 2 := by
  have hpoint (v : ZMod q) : ‖packetRightCoefficient q S beta a v‖ ^ 2 ≤
      collisionFactor q a L U * ∑ y ∈ residueFibre S q a v, ‖beta y‖ ^ 2 := by
    calc
      _ ≤ ((residueFibre S q a v).card : ℝ) *
          ∑ y ∈ residueFibre S q a v, ‖beta y‖ ^ 2 :=
        packetRightCoefficient_fibre_norm_sq_le q S beta a v
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (residueFibre_card_le S q (NeZero.pos q) a L U hLU hS v)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  change (∑ v : ZMod q, ‖packetRightCoefficient q S beta a v‖ ^ 2) ≤ _
  calc
    _ ≤ ∑ v : ZMod q, collisionFactor q a L U *
        ∑ y ∈ residueFibre S q a v, ‖beta y‖ ^ 2 := Finset.sum_le_sum (fun v _ => hpoint v)
    _ = collisionFactor q a L U * (∑ v : ZMod q, ∑ y ∈ residueFibre S q a v, ‖beta y‖ ^ 2) :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [sum_fibre_integer_energy]

/-- Zero weights outside the physical interval do not create occupancy
fees. The original signed pushforward itself is exactly unchanged. -/
theorem packetRightCoefficient_filter_nonzero (q : ℕ) [NeZero q] (S : Finset ℤ)
    (beta : ℤ → ℂ) (a : ℤ) :
    packetRightCoefficient q S beta a =
      packetRightCoefficient q (S.filter (fun y => beta y ≠ 0)) beta a := by
  funext v
  simp only [packetRightCoefficient, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hb : beta y = 0 <;> simp [hb]

theorem packetRight_energy_le_of_weight_support (q : ℕ) [NeZero q] (S : Finset ℤ)
    (beta : ℤ → ℂ) (a L U : ℤ) (hLU : L ≤ U)
    (hS : ∀ y ∈ S, beta y ≠ 0 → L ≤ y ∧ y ≤ U) :
    energy q (packetRightCoefficient q S beta a) ≤
      collisionFactor q a L U * ∑ y ∈ S, ‖beta y‖ ^ 2 := by
  rw [packetRightCoefficient_filter_nonzero]
  have h := packetRight_energy_le_integer_energy q (S.filter (fun y => beta y ≠ 0)) beta a L U hLU
    (fun y hy => hS y (mem_filter.mp hy).1 (mem_filter.mp hy).2)
  have hs : (∑ y ∈ S.filter (fun y => beta y ≠ 0), ‖beta y‖ ^ 2) = ∑ y ∈ S, ‖beta y‖ ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro y hy hnot
    have hz : beta y = 0 := by
      by_contra hn
      exact hnot (mem_filter.mpr ⟨hy, hn⟩)
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  rwa [hs] at h

end
end ImbalancedChen.Part3.SignedResiduePushforwardEnergy20261026b
