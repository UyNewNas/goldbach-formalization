import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

Sharp signed CLOSED-interval occupancy for y |-> a*y mod q, with arbitrary
integer a and positive q. The spacing is q/gcd(q,|a|), not q. No inverse
of a is used. Empty and incompatible fibres, a=0, q=1 and y=0 remain.
The result is finite incidence only; it proves no spectral or physical
support estimate and repeats no signed-difference multiplicity theorem.
-/

namespace ImbalancedChen.Part3.SignedIntervalResidueOccupancy20261026b

noncomputable section
open scoped Classical
open Finset

def residuePeriod (q : ℕ) (a : ℤ) : ℕ := q / q.gcd a.natAbs

def residueFibre (S : Finset ℤ) (q : ℕ) (a : ℤ) (v : ZMod q) : Finset ℤ :=
  S.filter (fun y => ((a * y : ℤ) : ZMod q) = v)

theorem residuePeriod_pos (q : ℕ) (hq : 0 < q) (a : ℤ) : 0 < residuePeriod q a :=
  Nat.div_gcd_pos_of_pos_left a.natAbs hq

theorem residuePeriod_mul_gcd (q : ℕ) (a : ℤ) :
    residuePeriod q a * q.gcd a.natAbs = q :=
  Nat.div_mul_cancel (Nat.gcd_dvd_left q a.natAbs)

/-- Primary signed cancellation requires only the positive modulus.
It therefore includes both nonunits and the zero multiplier. -/
theorem equal_residues_force_period (q : ℕ) (hq : 0 < q) (a y z : ℤ)
    (h : ((a * y : ℤ) : ZMod q) = ((a * z : ℤ) : ZMod q)) :
    Int.ModEq (residuePeriod q a : ℤ) y z := by
  have hm := (ZMod.intCast_eq_intCast_iff (a * y) (a * z) q).mp h
  have hc := Int.ModEq.cancel_left_div_gcd (by exact_mod_cast hq) hm
  simpa only [residuePeriod, Int.natCast_ediv, Int.gcd, Int.natAbs_natCast] using hc

/-- The minimum occupied point is the origin of the progression. This
keeps the sharp closed-interval cost 1+(U-L)/period, without an endpoint
rounding surcharge. No residue representative or solvability is assumed. -/
theorem signed_progression_card_le (S : Finset ℤ) (L U period : ℤ)
    (hLU : L ≤ U) (hp : 0 < period)
    (hS : ∀ y ∈ S, L ≤ y ∧ y ≤ U)
    (hmod : ∀ y ∈ S, ∀ z ∈ S, Int.ModEq period y z) :
    (S.card : ℝ) ≤ 1 + ((U : ℝ) - L) / period := by
  by_cases hne : S.Nonempty
  · let y0 := S.min' hne
    have hy0 : y0 ∈ S := Finset.min'_mem S hne
    have hmin (y : ℤ) (hy : y ∈ S) : y0 ≤ y := Finset.min'_le S y hy
    let M := (U - L) / period
    have hM0 : 0 ≤ M := Int.ediv_nonneg (sub_nonneg.mpr hLU) hp.le
    have hcard : S.card ≤ (Icc (0 : ℤ) M).card := by
      apply Finset.card_le_card_of_injOn (fun y : ℤ => (y - y0) / period)
      · intro y hy
        exact mem_Icc.mpr ⟨Int.ediv_nonneg (sub_nonneg.mpr (hmin y hy)) hp.le,
          Int.ediv_le_ediv hp (by linarith [(hS y hy).2, (hS y0 hy0).1])⟩
      · intro y hy z hz heq
        have hydiv := Int.ediv_mul_cancel_of_dvd (hmod y0 hy0 y hy).dvd
        have hzdiv := Int.ediv_mul_cancel_of_dvd (hmod y0 hy0 z hz).dvd
        have hh := congrArg (fun n : ℤ => n * period) heq
        rw [hydiv, hzdiv] at hh
        omega
    have hcount : ((Icc (0 : ℤ) M).card : ℤ) = M + 1 := by
      simpa only [sub_zero] using (Int.card_Icc_of_le (by omega : (0 : ℤ) ≤ M + 1))
    have hcountR : ((Icc (0 : ℤ) M).card : ℝ) = (M : ℝ) + 1 := by exact_mod_cast hcount
    have hpR : (0 : ℝ) < period := by exact_mod_cast hp
    have hM : (M : ℝ) ≤ ((U : ℝ) - L) / period := by
      apply (le_div_iff₀ hpR).mpr
      have hm := Int.ediv_mul_le (U - L) hp.ne'
      exact_mod_cast hm
    calc
      (S.card : ℝ) ≤ ((Icc (0 : ℤ) M).card : ℝ) := by exact_mod_cast hcard
      _ = (M : ℝ) + 1 := hcountR
      _ ≤ _ := by linarith
  · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hz]
    have hdiff : (0 : ℝ) ≤ (U : ℝ) - L := by exact_mod_cast (sub_nonneg.mpr hLU)
    have hpR : (0 : ℝ) ≤ period := by exact_mod_cast hp.le
    have hratio := div_nonneg hdiff hpR
    simpa only [card_empty, Nat.cast_zero] using (show (0 : ℝ) ≤ 1 + ((U : ℝ) - L) / period by linarith)

theorem residueFibre_card_le (S : Finset ℤ) (q : ℕ) (hq : 0 < q) (a : ℤ)
    (L U : ℤ) (hLU : L ≤ U) (hS : ∀ y ∈ S, L ≤ y ∧ y ≤ U) (v : ZMod q) :
    ((residueFibre S q a v).card : ℝ) ≤
      1 + ((U : ℝ) - L) * (q.gcd a.natAbs : ℝ) / q := by
  have hp := residuePeriod_pos q hq a
  have hbound := signed_progression_card_le (residueFibre S q a v) L U
    (residuePeriod q a) hLU (by exact_mod_cast hp)
    (fun y hy => hS y (mem_filter.mp hy).1) (by
      intro y hy z hz
      exact equal_residues_force_period q hq a y z
        ((mem_filter.mp hy).2.trans (mem_filter.mp hz).2.symm))
  have hg : (0 : ℝ) < q.gcd a.natAbs := by exact_mod_cast Nat.gcd_pos_of_pos_left a.natAbs hq
  have hprod : (residuePeriod q a : ℝ) * (q.gcd a.natAbs : ℝ) = q := by
    exact_mod_cast residuePeriod_mul_gcd q a
  have hratio : ((U : ℝ) - L) / (residuePeriod q a : ℝ) =
      ((U : ℝ) - L) * (q.gcd a.natAbs : ℝ) / q := by
    rw [← hprod]
    field_simp [hg.ne', (show (residuePeriod q a : ℝ) ≠ 0 by exact_mod_cast hp.ne')]
  simpa only [Int.cast_natCast, hratio] using hbound

/-- Incompatible residues have EMPTY fibres, rather than an invented
representative obtained by dividing a nonunit. -/
theorem residueFibre_empty_of_not_gcd_dvd (S : Finset ℤ) (q : ℕ) [NeZero q] (a : ℤ) (v : ZMod q)
    (hv : ¬ (q.gcd a.natAbs : ℤ) ∣ (v.val : ℤ)) : residueFibre S q a v = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro y hy
  have he : ((a * y : ℤ) : ZMod q) = ((v.val : ℕ) : ZMod q) := by
    simpa only [ZMod.natCast_zmod_val] using (mem_filter.mp hy).2
  have hm := (ZMod.intCast_eq_intCast_iff (a * y) (v.val : ℤ) q).mp he
  have hqdiv : (q.gcd a.natAbs : ℤ) ∣ (q : ℤ) := by
    simpa only [Int.gcd, Int.natAbs_natCast] using Int.gcd_dvd_left (q : ℤ) a
  have hadiv : (q.gcd a.natAbs : ℤ) ∣ a := by
    simpa only [Int.gcd, Int.natAbs_natCast] using Int.gcd_dvd_right (q : ℤ) a
  have hd := dvd_add (hqdiv.trans hm.dvd) (dvd_mul_of_dvd_left hadiv y)
  exact hv (by simpa only [sub_add_cancel] using hd)

theorem residueFibre_zero_multiplier (S : Finset ℤ) (q : ℕ) (v : ZMod q) :
    residueFibre S q 0 v = if v = 0 then S else ∅ := by
  ext y
  by_cases hv : v = 0 <;> simp [residueFibre, hv]

end
end ImbalancedChen.Part3.SignedIntervalResidueOccupancy20261026b
