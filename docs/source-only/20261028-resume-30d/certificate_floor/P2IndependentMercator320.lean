import ImbalancedChen.P2GuardedReciprocalRounding
import Mathlib.Analysis.Calculus.MeanValue

/-!
SOURCE ONLY; uncompiled.  The original independent producer uses decimal
scale 10^80, 320 alternating terms, and the next positive term after its
even partial sum.  This file proves that exact remainder and propagates it
through the original directed decimal operations.  No log enclosure,
numerical replay, or final proxy-sum bound is a premise.
-/

namespace ImbalancedChen.P2IndependentMercator320

noncomputable section

open Set
open scoped BigOperators
open Certificates.P2DirectedLogRounding

def powerTerm (y : ℝ) (n : ℕ) : ℝ := y ^ (n + 1) / ((n : ℝ) + 1)
def evenPartial (y : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (powerTerm y (2 * i) - powerTerm y (2 * i + 1))
def evenDerivative (y : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (y ^ (2 * i) - y ^ (2 * i + 1))

theorem powerTerm_hasDerivAt (x : ℝ) (n : ℕ) :
    HasDerivAt (fun y => powerTerm y n) (x ^ n) x := by
  have hd := (hasDerivAt_pow (n + 1) x).div_const ((n : ℝ) + 1)
  convert hd using 1 <;> simp only [powerTerm, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    <;> field_simp [show (n : ℝ) + 1 ≠ 0 by positivity] <;> ring

theorem evenPartial_hasDerivAt (x : ℝ) (n : ℕ) :
    HasDerivAt (fun y => evenPartial y n) (evenDerivative x n) x :=
  HasDerivAt.sum (fun i _hi => (powerTerm_hasDerivAt x (2 * i)).sub
    (powerTerm_hasDerivAt x (2 * i + 1)))

theorem evenDerivative_geometric (x : ℝ) (n : ℕ) :
    evenDerivative x n * (1 + x) = 1 - x ^ (2 * n) := by
  induction n with
  | zero => simp [evenDerivative]
  | succ n ih =>
    have hp : x ^ (2 * (n + 1)) = x ^ (2 * n) * x ^ 2 := by
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
    calc
      evenDerivative x (n + 1) * (1 + x) =
          evenDerivative x n * (1 + x) + x ^ (2 * n) * (1 - x ^ 2) := by
        simp only [evenDerivative, Finset.sum_range_succ, pow_succ]
        ring
      _ = 1 - x ^ (2 * (n + 1)) := by rw [ih, hp]; ring

private theorem nonneg_from_zero {f f' : ℝ → ℝ} (hzero : f 0 = 0)
    (hd : ∀ x, 0 ≤ x → HasDerivAt f (f' x) x)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => hpos y (interior_subset hy))
  simpa only [hzero] using hm (show (0 : ℝ) ∈ Ici 0 by simp) hx hx

/-- The even partial sum is below log(1+y), and its NEXT TERM bounds the
error.  The derivative identity proves the sign; an absolute/geometric
remainder without the 1/(2n+1) factor is not substituted. -/
theorem even_mercator_next_term {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    evenPartial y n ≤ Real.log (1 + y) ∧
      Real.log (1 + y) ≤ evenPartial y n + powerTerm y (2 * n) := by
  let F : ℝ → ℝ := fun x => Real.log (1 + x) - evenPartial x n
  let G : ℝ → ℝ := fun x => powerTerm x (2 * n) - F x
  have hF (x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt F (x ^ (2 * n) / (1 + x)) x := by
    have hden : 1 + x ≠ 0 := by linarith
    have hd := (((hasDerivAt_id' x).const_add 1).log hden).sub
      (evenPartial_hasDerivAt x n)
    convert hd using 1
    field_simp [hden]
    nlinarith [evenDerivative_geometric x n]
  have hG (x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt G (x ^ (2 * n + 1) / (1 + x)) x := by
    have hd := (powerTerm_hasDerivAt x (2 * n)).sub (hF x hx)
    convert hd using 1
    have hden : 1 + x ≠ 0 := by linarith
    field_simp [hden]
    rw [pow_succ]
    ring
  have hF0 : F 0 = 0 := by simp [F, evenPartial, powerTerm]
  have hG0 : G 0 = 0 := by simp [G, hF0, powerTerm]
  have hFlo := nonneg_from_zero hF0 hF
    (fun x hx => div_nonneg (pow_nonneg hx _) (by linarith)) hy
  have hGlo := nonneg_from_zero hG0 hG
    (fun x hx => div_nonneg (pow_nonneg hx _) (by linarith)) hy
  dsimp [F, G] at hFlo hGlo
  constructor <;> linarith

def scale : ℚ := 10 ^ 80
def decimalRound (a : Enclosure) : Enclosure :=
  ⟨(⌊a.lower * scale⌋ : ℚ) / scale, (⌈a.upper * scale⌉ : ℚ) / scale⟩
def point (q : ℚ) : Enclosure := decimalRound (Enclosure.point q)
def mul (a b : Enclosure) : Enclosure := decimalRound (a.mul b)
def divNat (a : Enclosure) (n : ℕ) : Enclosure :=
  decimalRound ⟨a.lower / n, a.upper / n⟩
def divide (a b : Enclosure) : Enclosure := decimalRound (a.divisionBounds b)

theorem scale_pos : 0 < scale := by norm_num [scale]

theorem decimalRound_contains {a : Enclosure} {x : ℝ} (ha : a.Contains x) :
    (decimalRound a).Contains x := by
  have hl : (⌊a.lower * scale⌋ : ℚ) / scale ≤ a.lower :=
    (div_le_iff₀ scale_pos).mpr (Int.floor_le _)
  have hh : a.upper ≤ (⌈a.upper * scale⌉ : ℚ) / scale :=
    (le_div_iff₀ scale_pos).mpr (Int.le_ceil _)
  exact ⟨(by exact_mod_cast hl).trans ha.1, ha.2.trans (by exact_mod_cast hh)⟩

theorem point_contains (q : ℚ) : (point q).Contains q :=
  decimalRound_contains (Enclosure.point_contains q)

theorem mul_contains {a b : Enclosure} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (mul a b).Contains (x * y) := decimalRound_contains (Enclosure.mul_contains ha hb)

theorem divide_contains {a b : Enclosure} {x y : ℝ}
    (ha : a.Contains x) (hb : b.Contains y) (hc : b.reciprocalCheck = true) :
    (divide a b).Contains (x / y) :=
  decimalRound_contains (Enclosure.divisionBounds_contains ha hb hc)

theorem divNat_contains {a : Enclosure} {x : ℝ} (ha : a.Contains x) {n : ℕ} (hn : 0 < n) :
    (divNat a n).Contains (x / n) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  apply decimalRound_contains
  exact ⟨by simpa only [Enclosure.Contains, Rat.cast_div, Rat.cast_natCast] using
      div_le_div_of_nonneg_right ha.1 hnR.le,
    by simpa only [Rat.cast_div, Rat.cast_natCast] using div_le_div_of_nonneg_right ha.2 hnR.le⟩

def alternatingPartial (y : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => alternatingPartial y n + if n % 2 = 0 then powerTerm y n else -powerTerm y n

theorem alternating_even_eq (y : ℝ) (n : ℕ) : alternatingPartial y (2 * n) = evenPartial y n := by
  induction n with
  | zero => simp [alternatingPartial, evenPartial]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      alternatingPartial, alternatingPartial]
    simp only [show (2 * n + 1) % 2 ≠ 0 by omega, if_false,
      show (2 * n) % 2 = 0 by omega, if_true, ih]
    simp only [evenPartial, Finset.sum_range_succ]
    ring

def loop (q : ℚ) : ℕ → Enclosure × Enclosure
  | 0 => (point 1, point 0)
  | n + 1 =>
      let prev := loop q n
      let p := mul prev.1 (point (q - 1))
      let term := divNat p (n + 1)
      (p, prev.2.add (if n % 2 = 0 then term else term.neg))

theorem loop_contains (q : ℚ) (n : ℕ) :
    (loop q n).1.Contains (((q : ℝ) - 1) ^ n) ∧
      (loop q n).2.Contains (alternatingPartial ((q : ℝ) - 1) n) := by
  induction n with
  | zero => simpa only [loop, pow_zero, alternatingPartial, Rat.cast_one, Rat.cast_zero] using
      And.intro (point_contains 1) (point_contains 0)
  | succ n ih =>
    have hp := mul_contains ih.1 (point_contains (q - 1))
    have ht := divNat_contains hp (Nat.succ_pos n)
    have ht' : (divNat (mul (loop q n).1 (point (q - 1))) (n + 1)).Contains
        (powerTerm ((q : ℝ) - 1) n) := by
      simpa only [powerTerm, pow_succ, Rat.cast_sub, Rat.cast_one, Nat.cast_add, Nat.cast_one] using ht
    constructor
    · simpa only [loop, pow_succ, Rat.cast_sub, Rat.cast_one] using hp
    · by_cases hpar : n % 2 = 0
      · simpa only [loop, alternatingPartial, if_pos hpar] using Enclosure.add_contains ih.2 ht'
      · simpa only [loop, alternatingPartial, if_neg hpar] using
          Enclosure.add_contains ih.2 (Enclosure.neg_contains ht')

def mercator (q : ℚ) : Enclosure :=
  let s := loop q 320
  let tail := divNat (mul s.1 (point (q - 1))) 321
  ⟨s.2.lower, s.2.upper + tail.upper⟩

theorem mercator_contains {q : ℚ} (hq : 1 ≤ q) (_hsmall : q ≤ 3 / 2) :
    (mercator q).Contains (Real.log (q : ℝ)) := by
  let y : ℝ := (q : ℝ) - 1
  have hy : 0 ≤ y := by dsimp [y]; exact_mod_cast sub_nonneg.mpr hq
  have hs := (loop_contains q 320).2
  have hp := (loop_contains q 320).1
  have ht := divNat_contains (mul_contains hp (point_contains (q - 1))) (by norm_num : 0 < 321)
  have he : alternatingPartial y 320 = evenPartial y 160 := alternating_even_eq y 160
  have hb := even_mercator_next_term hy 160
  have htail : (divNat (mul (loop q 320).1 (point (q - 1))) 321).Contains
      (powerTerm y 320) := by
    simpa only [powerTerm, pow_succ, Rat.cast_sub, Rat.cast_one, y] using ht
  change ((mercator q).lower : ℝ) ≤ Real.log (q : ℝ) ∧
    Real.log (q : ℝ) ≤ ((mercator q).upper : ℝ)
  dsimp only [mercator]
  have hlog : Real.log (1 + y) = Real.log (q : ℝ) := by dsimp [y]; congr 1; ring
  rw [hlog] at hb
  change (loop q 320).2.Contains (alternatingPartial y 320) at hs
  rw [he] at hs
  exact ⟨hs.1.trans hb.1, hb.2.trans (by
    simpa only [Rat.cast_add] using add_le_add hs.2 htail.2)⟩

end

end ImbalancedChen.P2IndependentMercator320
