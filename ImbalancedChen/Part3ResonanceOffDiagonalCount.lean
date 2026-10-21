import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

/-!
# Finite ordered off-diagonal congruence count on the original dyadic interval

The interval is the inclusive natural-number interval from `ceil U` to
`floor (2 * U)`, exactly the original `factorCarrier U`. The modulus is any
positive natural number. Both orders of a pair are counted, and equal labels
are excluded before counting positive differences. This exclusion makes the
quotient interval start at one and removes any additive rounding term.

This leaf proves only a finite arithmetic count. It has no resonance,
Fourier-envelope, root-operator, or spectral estimate among its hypotheses.
-/

namespace ImbalancedChen.Part3.ResonanceOffDiagonalCount

noncomputable section

open Classical Finset

private theorem increasing_count_le (S : Finset ℕ) (U : ℝ)
    (hS : ∀ n ∈ S, U ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * U)
    (m : ℕ) (hm : 0 < m) :
    ((S ×ˢ S).filter (fun z => z.1 < z.2 ∧ Nat.ModEq m z.1 z.2)).card ≤
      S.card * Nat.floor (U / (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    _ ≤ (S ×ˢ Icc 1 (Nat.floor (U / (m : ℝ)))).card := by
      apply card_le_card_of_injOn
        (fun z : ℕ × ℕ => (z.1, (z.2 - z.1) / m))
      · intro z hz
        obtain ⟨hzS, hzlt, hzmod⟩ := mem_filter.mp hz
        obtain ⟨hz1, hz2⟩ := mem_product.mp hzS
        have hdvd : m ∣ z.2 - z.1 :=
          (Nat.modEq_iff_dvd' hzlt.le).mp hzmod
        have hdiffpos : 0 < z.2 - z.1 := Nat.sub_pos_of_lt hzlt
        have hqpos : 0 < (z.2 - z.1) / m :=
          Nat.div_pos (Nat.le_of_dvd hdiffpos hdvd) hm
        have hqmul : (((z.2 - z.1) / m : ℕ) : ℝ) * m =
            ((z.2 - z.1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.div_mul_cancel hdvd
        have hdiffadd : ((z.2 - z.1 : ℕ) : ℝ) + z.1 = z.2 := by
          exact_mod_cast Nat.sub_add_cancel hzlt.le
        have hdiffbound : ((z.2 - z.1 : ℕ) : ℝ) ≤ U := by
          have hlo := (hS z.1 hz1).1
          have hhi := (hS z.2 hz2).2
          linarith
        have hqupper : (((z.2 - z.1) / m : ℕ) : ℝ) ≤ U / (m : ℝ) := by
          apply (le_div_iff₀ hmR).mpr
          rw [hqmul]
          exact hdiffbound
        exact mem_product.mpr ⟨hz1, mem_Icc.mpr
          ⟨Nat.succ_le_iff.mpr hqpos, Nat.le_floor hqupper⟩⟩
      · intro z hz w hw he
        obtain ⟨_, hzlt, hzmod⟩ := mem_filter.mp hz
        obtain ⟨_, hwlt, hwmod⟩ := mem_filter.mp hw
        have hfirst : z.1 = w.1 := congrArg Prod.fst he
        have hquot : (z.2 - z.1) / m = (w.2 - w.1) / m :=
          congrArg Prod.snd he
        have hzdvd : m ∣ z.2 - z.1 :=
          (Nat.modEq_iff_dvd' hzlt.le).mp hzmod
        have hwdvd : m ∣ w.2 - w.1 :=
          (Nat.modEq_iff_dvd' hwlt.le).mp hwmod
        have hdiff : z.2 - z.1 = w.2 - w.1 := by
          calc
            _ = ((z.2 - z.1) / m) * m := (Nat.div_mul_cancel hzdvd).symm
            _ = ((w.2 - w.1) / m) * m := by rw [hquot]
            _ = _ := Nat.div_mul_cancel hwdvd
        apply Prod.ext hfirst
        omega
    _ = _ := by
      simp only [card_product, Nat.card_Icc, Nat.add_sub_cancel]

private theorem finite_count_le (S : Finset ℕ) (U : ℝ) (hU : 1 ≤ U)
    (hS : ∀ n ∈ S, U ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * U)
    (m : ℕ) (hm : 0 < m) :
    (((S ×ˢ S).filter (fun z => z.1 ≠ z.2 ∧ Nat.ModEq m z.1 z.2)).card : ℝ) ≤
      4 * U ^ 2 / (m : ℝ) := by
  let A := (S ×ˢ S).filter (fun z => z.1 < z.2 ∧ Nat.ModEq m z.1 z.2)
  let B := (S ×ˢ S).filter (fun z => z.2 < z.1 ∧ Nat.ModEq m z.1 z.2)
  have hAB : B.card ≤ A.card := by
    apply card_le_card_of_injOn (fun z : ℕ × ℕ => (z.2, z.1))
    · intro z hz
      obtain ⟨hzS, hzlt, hzmod⟩ := mem_filter.mp hz
      obtain ⟨hz1, hz2⟩ := mem_product.mp hzS
      exact mem_filter.mpr
        ⟨mem_product.mpr ⟨hz2, hz1⟩, hzlt, hzmod.symm⟩
    · intro z _ w _ he
      exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
  have hsplit :
      (S ×ˢ S).filter (fun z => z.1 ≠ z.2 ∧ Nat.ModEq m z.1 z.2) = A ∪ B := by
    ext z
    simp only [A, B, mem_filter, mem_union]
    constructor
    · rintro ⟨hz, hne, hmod⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hz, hlt, hmod⟩
      · exact Or.inr ⟨hz, hgt, hmod⟩
    · rintro (h | h)
      · exact ⟨h.1, ne_of_lt h.2.1, h.2.2⟩
      · exact ⟨h.1, (ne_of_lt h.2.1).symm, h.2.2⟩
  have hA : A.card ≤ S.card * Nat.floor (U / (m : ℝ)) :=
    increasing_count_le S U hS m hm
  have hcount :
      ((S ×ˢ S).filter (fun z => z.1 ≠ z.2 ∧ Nat.ModEq m z.1 z.2)).card ≤
        2 * S.card * Nat.floor (U / (m : ℝ)) := by
    rw [hsplit]
    calc
      _ ≤ A.card + B.card := card_union_le A B
      _ ≤ S.card * Nat.floor (U / (m : ℝ)) +
          S.card * Nat.floor (U / (m : ℝ)) :=
        Nat.add_le_add hA (hAB.trans hA)
      _ = _ := by ring
  have hprefix : S ⊆ Ioc 0 (Nat.floor (2 * U)) := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := hS n hn
    have hnOne : 1 ≤ n := by exact_mod_cast hU.trans hlo
    exact mem_Ioc.mpr ⟨by omega, Nat.le_floor hhi⟩
  have hcard : (S.card : ℝ) ≤ 2 * U := by
    have hc := card_le_card hprefix
    simp only [Nat.card_Ioc, Nat.sub_zero] at hc
    exact (show (S.card : ℝ) ≤ (Nat.floor (2 * U) : ℝ) by
      exact_mod_cast hc).trans (Nat.floor_le (by linarith))
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfloor : (Nat.floor (U / (m : ℝ)) : ℝ) ≤ U / (m : ℝ) :=
    Nat.floor_le (div_nonneg (by linarith) hmR.le)
  calc
    _ ≤ 2 * (S.card : ℝ) * (Nat.floor (U / (m : ℝ)) : ℝ) := by
      exact_mod_cast hcount
    _ ≤ (2 * (2 * U)) * (U / (m : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcard (by norm_num)) hfloor
        (Nat.cast_nonneg _) (by linarith)
    _ = _ := by ring

/-- Inclusive original dyadic carrier; ordered pairs; the diagonal is excluded.
There is no additive `+1`, including when `m > U` and the carrier is empty of
off-diagonal congruent pairs. The endpoint condition `1 ≤ U` is the original
scale condition and includes the case `U = 1`.
-/
theorem dyadic_ordered_offDiagonal_modEq_count_le (U : ℝ) (hU : 1 ≤ U)
    (m : ℕ) (hm : 0 < m) :
    (((Icc (Nat.ceil U) (Nat.floor (2 * U)) ×ˢ
        Icc (Nat.ceil U) (Nat.floor (2 * U))).filter
      (fun z => z.1 ≠ z.2 ∧ Nat.ModEq m z.1 z.2)).card : ℝ) ≤
        4 * U ^ 2 / (m : ℝ) := by
  apply finite_count_le (Icc (Nat.ceil U) (Nat.floor (2 * U))) U hU
    (m := m) (hm := hm)
  intro n hn
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp hn
  exact ⟨(Nat.le_ceil U).trans (by exact_mod_cast hlo),
    (show (n : ℝ) ≤ (Nat.floor (2 * U) : ℝ) by exact_mod_cast hhi).trans
      (Nat.floor_le (by linarith))⟩

end

end ImbalancedChen.Part3.ResonanceOffDiagonalCount
