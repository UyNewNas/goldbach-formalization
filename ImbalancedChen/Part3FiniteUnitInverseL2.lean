import ImbalancedChen.Part3KloostermanCompleteSecondMoment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
Finite L2 primitives for EVERY positive composite modulus, including 1.
The DFT is unnormalised and has squared norm factor q. Inversion is only
permuted on ACTUAL units; no inverse permutation of all composite residues
is asserted. Its extension by zero is a genuine contraction.
-/

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.FiniteOperator20261026b
noncomputable section
open Classical Finset
open scoped BigOperators

def energy (q : ℕ) [NeZero q] (b : ZMod q → ℂ) : ℝ := ∑ n : ZMod q, ‖b n‖^2
def dft (q : ℕ) [NeZero q] (b : ZMod q → ℂ) (a : ZMod q) : ℂ :=
  ∑ n : ZMod q, b n * ZMod.stdAddChar (a*n)
def unitInversePullback (q : ℕ) [NeZero q] (b : ZMod q → ℂ) (u : ZMod q) : ℂ :=
  if IsUnit u then b u⁻¹ else 0

theorem dft_energy (q : ℕ) [NeZero q] (b : ZMod q → ℂ) :
    energy q (dft q b) = (q : ℝ)*energy q b :=
  CompleteSecondMomentSourceOnly.complete_additive_energy q b

theorem sum_unitGate_eq_units (q : ℕ) [NeZero q]
    {A : Type*} [AddCommMonoid A] (f : ZMod q → A) :
    (∑ u : ZMod q, if IsUnit u then f u else 0) = ∑ u : (ZMod q)ˣ, f u := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun u _ => (u : ZMod q))
  · intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,u.isUnit⟩
  · intro u hu v hv heq
    exact Units.ext heq
  · intro u hu
    obtain ⟨v,rfl⟩ := (Finset.mem_filter.mp hu).2
    exact ⟨v,Finset.mem_univ _,rfl⟩
  · intro u hu
    rfl

/-- Exact permutation on the unit subspace, with no claim about inverses
of nonunits in ZMod q. -/
theorem unitInversePullback_energy (q : ℕ) [NeZero q] (b : ZMod q → ℂ) :
    energy q (unitInversePullback q b) =
      ∑ u : ZMod q, if IsUnit u then ‖b u‖^2 else 0 := by
  unfold energy unitInversePullback
  have hpoint (u : ZMod q) : ‖if IsUnit u then b u⁻¹ else 0‖^2 =
      if IsUnit u then ‖b u⁻¹‖^2 else 0 := by split_ifs <;> simp
  simp_rw [hpoint]
  rw [sum_unitGate_eq_units,sum_unitGate_eq_units]
  apply Finset.sum_bij (fun u _ => u⁻¹)
  · intro u hu
    exact Finset.mem_univ _
  · intro u hu v hv heq
    exact inv_injective heq
  · intro u hu
    exact ⟨u⁻¹,Finset.mem_univ _,inv_inv u⟩
  · intro u hu
    rw [ZMod.inv_coe_unit]

theorem unitInversePullback_energy_le (q : ℕ) [NeZero q] (b : ZMod q → ℂ) :
    energy q (unitInversePullback q b) ≤ energy q b := by
  rw [unitInversePullback_energy]
  apply Finset.sum_le_sum
  intro u hu
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

end
end ImbalancedChen.Part3.OriginalSmoothPoissonTail.FiniteOperator20261026b
