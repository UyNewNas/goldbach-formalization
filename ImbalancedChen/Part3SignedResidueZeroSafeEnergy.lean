import ImbalancedChen.Part3SignedResiduePushforwardEnergy
import ImbalancedChen.Part3ActualClosedTCountLicense

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

Exact zero-y separation for the SAME complex signed residue pushforward.
True y=0 and nonzero y divisible by q/gcd(q,|a|) can share residue zero.
Their cross terms are retained in an exact pointwise identity and paid
by a visible factor TWO in the energy bound. No orthogonality is asserted.

The nonzero-y coefficient energy is the actual integer-y energy on S\{0};
the true zero coefficient is beta(0) only when 0 belongs to the original S.
Empty S, a=0, composite q and q=1 are included. No 576 count, old zero-piece
payment, physical support theorem or spectral license is re-proved here.
-/

namespace ImbalancedChen.Part3.SignedResidueZeroSafeEnergy20261026b

noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalSmoothPoissonTail.FiniteOperator20261026b
open SignedResiduePushforwardEnergy20261026b

def zeroCoefficient (S : Finset ℤ) (beta : ℤ → ℂ) : ℂ := if (0 : ℤ) ∈ S then beta 0 else 0

/-- This identity retains the cross term at residue ZERO. -/
theorem packetRightCoefficient_zero_split (q : ℕ) [NeZero q] (S : Finset ℤ)
    (beta : ℤ → ℂ) (a : ℤ) (v : ZMod q) :
    packetRightCoefficient q S beta a v =
      packetRightCoefficient q (S.erase 0) beta a v +
        if v = 0 then zeroCoefficient S beta else 0 := by
  by_cases h0 : (0 : ℤ) ∈ S
  · have h := (Finset.sum_erase_add S
        (fun y : ℤ => if ((a * y : ℤ) : ZMod q) = v then beta y else 0) h0).symm
    simpa only [packetRightCoefficient, zeroCoefficient, if_pos h0,
      mul_zero, Int.cast_zero, eq_comm] using h
  · simp only [packetRightCoefficient, Finset.erase_eq_of_notMem h0,
      zeroCoefficient, if_neg h0, ite_self, add_zero]

theorem delta_zero_energy (q : ℕ) [NeZero q] (z : ℂ) :
    energy q (fun v : ZMod q => if v = 0 then z else 0) = ‖z‖ ^ 2 := by
  simp [energy]

theorem packetRight_energy_zero_split_le (q : ℕ) [NeZero q] (S : Finset ℤ)
    (beta : ℤ → ℂ) (a : ℤ) :
    energy q (packetRightCoefficient q S beta a) ≤
      2 * energy q (packetRightCoefficient q (S.erase 0) beta a) + 2 * ‖zeroCoefficient S beta‖ ^ 2 := by
  change (∑ v : ZMod q, ‖packetRightCoefficient q S beta a v‖ ^ 2) ≤ _
  have hd : (∑ v : ZMod q, ‖if v = 0 then zeroCoefficient S beta else 0‖ ^ 2) =
      ‖zeroCoefficient S beta‖ ^ 2 := by simp
  calc
    _ ≤ ∑ v : ZMod q,
        (2 * ‖packetRightCoefficient q (S.erase 0) beta a v‖ ^ 2 +
          2 * ‖if v = 0 then zeroCoefficient S beta else 0‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro v _hv
      rw [packetRightCoefficient_zero_split]
      exact ActualClosedTCountLicenseSourceOnly.complex_two_piece_sq _ _
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hd]
      rfl

/-- Native consumers can apply their EXISTING nonzero-y integer energy
estimate to the first term, keeping their independent true zero payment.
Only nonzero weights at nonzero y need to lie in the signed interval. -/
theorem packetRight_energy_le_nonzero_integer_energy_add_zero
    (q : ℕ) [NeZero q] (S : Finset ℤ) (beta : ℤ → ℂ) (a L U : ℤ)
    (hLU : L ≤ U)
    (hS : ∀ y ∈ S, y ≠ 0 → beta y ≠ 0 → L ≤ y ∧ y ≤ U) :
    energy q (packetRightCoefficient q S beta a) ≤
      2 * collisionFactor q a L U * (∑ y ∈ S.erase 0, ‖beta y‖ ^ 2) +
        2 * ‖zeroCoefficient S beta‖ ^ 2 := by
  have hnz := packetRight_energy_le_of_weight_support q (S.erase 0) beta a L U hLU
    (fun y hy hb => hS y (mem_erase.mp hy).2 (mem_erase.mp hy).1 hb)
  calc
    _ ≤ 2 * energy q (packetRightCoefficient q (S.erase 0) beta a) +
        2 * ‖zeroCoefficient S beta‖ ^ 2 := packetRight_energy_zero_split_le q S beta a
    _ ≤ _ := by nlinarith

end
end ImbalancedChen.Part3.SignedResidueZeroSafeEnergy20261026b
