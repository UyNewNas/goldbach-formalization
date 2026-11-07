import ImbalancedChen.Part3ActualCommonIntervalCompletionL1
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Group.Action.Units
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
Exact finite residue algebra needed by ORIGINAL physical Hecke products.
Mixed-radix digits a+p*b enumerate range(p*q) by the actual Fin-product
equivalence. For positive coprime p,q, multiplication by p permutes ZMod q
using its ACTUAL coprime unit; literal integer translations of an original
period-one function pay the difference between p*b and its chosen residue.
No double-coset commutativity, operator identity or residue-permutation
premise is assumed. No continuity or spectral hypothesis is needed.
-/

namespace ImbalancedChen.Part3.PeriodicHeckeFiniteReindex20261026b
noncomputable section
open scoped BigOperators
open ActualCommonIntervalCompletionL1SourceOnly

/-- Actual mixed-radix enumeration, including either radix equal to zero. -/
theorem finite_radix_sum (p q : ℕ) (F : ℕ → ℂ) :
    (∑ a ∈ Finset.range p, ∑ b ∈ Finset.range q,F (a+p*b)) =
      ∑ r ∈ Finset.range (p*q),F r := by
  calc
    _ = ∑ a : Fin p, ∑ b : Fin q,F (a.val+p*b.val) := by
      simp_rw [Fin.sum_univ_eq_sum_range]
    _ = ∑ b : Fin q, ∑ a : Fin p,F (a.val+p*b.val) := Finset.sum_comm
    _ = ∑ t : Fin q × Fin p,F (t.2.val+p*t.1.val) := by rw [Fintype.sum_prod_type]
    _ = ∑ r : Fin (q*p),F r.val :=
      (finProdFinEquiv : Fin q × Fin p ≃ Fin (q*p)).sum_comp (fun r => F r.val)
    _ = ∑ r ∈ Finset.range (q*p),F r := Fin.sum_univ_eq_sum_range F (q*p)
    _ = _ := by rw [Nat.mul_comm q p]

/-- Original period one absorbs the ACTUAL quotient in Euclidean division. -/
theorem periodic_div_nat_mod (f : ℝ → ℂ) (hf : Function.Periodic f 1)
    (q : ℕ) (hq : 0 < q) (r : ℕ) (x : ℝ) :
    f ((x+(r : ℝ))/(q : ℝ)) = f ((x+((r%q : ℕ) : ℝ))/(q : ℝ)) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hdiv : (r : ℝ)=((r%q : ℕ) : ℝ)+(q : ℝ)*((r/q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div r q).symm
  have harg : (x+(r : ℝ))/(q : ℝ) =
      (x+((r%q : ℕ) : ℝ))/(q : ℝ)+((r/q : ℕ) : ℝ) := by
    rw [hdiv]
    field_simp [hqR] <;> ring
  rw [harg]
  simpa only [mul_one] using (hf.nat_mul (r/q)) ((x+((r%q : ℕ) : ℝ))/(q : ℝ))

/-- The actual coprime ZMod unit supplies the residue permutation; no
permutation of chosen representatives occurs among the hypotheses. -/
theorem periodic_coprime_residue_sum (p q : ℕ) (hq : 0 < q) (hpq : Nat.Coprime p q)
    (f : ℝ → ℂ) (hf : Function.Periodic f 1) (x : ℝ) :
    (∑ b ∈ Finset.range q,f ((x+(p*b : ℕ))/(q : ℝ))) =
      ∑ b ∈ Finset.range q,f ((x+(b : ℝ))/(q : ℝ)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hres (b : ZMod q) : ((p : ZMod q)*b).val=(p*b.val)%q := by
    have hc : ((p*b.val : ℕ) : ZMod q)=(p : ZMod q)*b := by simp
    rw [← hc,ZMod.val_natCast]
  have hpoint (b : ZMod q) : f ((x+(p*b.val : ℕ))/(q : ℝ)) =
      f ((x+((((p : ZMod q)*b).val : ℕ) : ℝ))/(q : ℝ)) := by
    rw [hres]
    exact periodic_div_nat_mod f hf q hq (p*b.val) x
  calc
    _ = ∑ b : ZMod q,f ((x+(p*b.val : ℕ))/(q : ℝ)) :=
      (sum_zmod_val_reindex q (fun b => f ((x+(p*b : ℕ))/(q : ℝ)))).symm
    _ = ∑ b : ZMod q,f ((x+((((p : ZMod q)*b).val : ℕ) : ℝ))/(q : ℝ)) :=
      Finset.sum_congr rfl (fun b hb => hpoint b)
    _ = ∑ b : ZMod q,f ((x+(b.val : ℝ))/(q : ℝ)) := by
      have h := (MulAction.toPerm (ZMod.unitOfCoprime p hpq)).sum_comp
        (fun b : ZMod q => f ((x+(b.val : ℝ))/(q : ℝ)))
      change (∑ b : ZMod q,f ((x+((((ZMod.unitOfCoprime p hpq : ZMod q)*b).val : ℕ) : ℝ))/(q : ℝ))) =
        ∑ b : ZMod q,f ((x+(b.val : ℝ))/(q : ℝ)) at h
      simpa only [ZMod.coe_unitOfCoprime] using h
    _ = _ := sum_zmod_val_reindex q (fun b => f ((x+(b : ℝ))/(q : ℝ)))

end
end ImbalancedChen.Part3.PeriodicHeckeFiniteReindex20261026b

