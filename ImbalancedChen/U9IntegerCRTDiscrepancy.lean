import ImbalancedChen.U9OrdinaryRowFiniteSelbergUpper

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact ordinary interval CRT counts have endpoint discrepancy at most one.
Comparing an extra coprime divisor condition to its 1/e dilution costs at
most two, with both endpoints retained and reversed intervals empty.
-/

namespace ImbalancedChen.U9SemiprimeSwitch
noncomputable section
open Classical
open scoped BigOperators

def divisorAPCount (A B d a t : ℕ) : ℝ :=
  (((Finset.Ico A B).filter (fun r => Nat.ModEq d r a ∧ t ∣ r)).card : ℝ)

private theorem intervalAP_discrepancy (A B M a : ℕ) (hAB : A ≤ B) (hM : 0 < M) :
    |(((Finset.Ico A B).filter (fun r => Nat.ModEq M r a)).card : ℝ) -
      ((B : ℝ) - (A : ℝ)) / (M : ℝ)| ≤ 1 := by
  let x := ((A : ℚ) - (a : ℚ)) / (M : ℚ)
  let y := ((B : ℚ) - (a : ℚ)) / (M : ℚ)
  have hxy : x ≤ y := div_le_div_of_nonneg_right
    (sub_le_sub_right (by exact_mod_cast hAB) (a : ℚ)) (Nat.cast_nonneg M)
  have hc := Nat.Ico_filter_modEq_card A B hM a
  rw [max_eq_left (sub_nonneg.mpr (Int.ceil_mono hxy))] at hc
  have hcQ : (((Finset.Ico A B).filter (fun r => Nat.ModEq M r a)).card : ℚ) =
      (Int.ceil y : ℚ) - (Int.ceil x : ℚ) := by exact_mod_cast hc
  have hxlo := Int.le_ceil x
  have hxhi := Int.ceil_lt_add_one x
  have hylo := Int.le_ceil y
  have hyhi := Int.ceil_lt_add_one y
  have hlen : y - x = ((B : ℚ) - (A : ℚ)) / (M : ℚ) := by dsimp [x, y]; ring
  have hbound : |(((Finset.Ico A B).filter (fun r => Nat.ModEq M r a)).card : ℚ) -
      ((B : ℚ) - (A : ℚ)) / (M : ℚ)| ≤ 1 := by
    rw [hcQ, ← hlen, abs_le]
    constructor <;> linarith
  exact_mod_cast hbound

/-- CRT is constructed at the true product modulus, not supplied as a
progression-count hypothesis. -/
theorem divisorAPCount_discrepancy (A B d a t : ℕ)
    (hAB : A ≤ B) (hd : 0 < d) (ht : 0 < t) (hcop : Nat.Coprime d t) :
    |divisorAPCount A B d a t - ((B : ℝ) - (A : ℝ)) / ((d : ℝ) * (t : ℝ))| ≤ 1 := by
  let b := Nat.chineseRemainder hcop a 0
  have hset : (Finset.Ico A B).filter (fun r => Nat.ModEq d r a ∧ t ∣ r) =
      (Finset.Ico A B).filter (fun r => Nat.ModEq (d * t) r b.val) := by
    ext r
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hr, hAP, htdiv⟩
      exact ⟨hr, Nat.chineseRemainder_modEq_unique hcop hAP
        (Nat.modEq_zero_iff_dvd.mpr htdiv)⟩
    · rintro ⟨hr, hmod⟩
      exact ⟨hr, (hmod.of_mul_right t).trans b.prop.1,
        Nat.modEq_zero_iff_dvd.mp ((hmod.of_mul_left d).trans b.prop.2)⟩
  have h := intervalAP_discrepancy A B (d * t) b.val hAB (mul_pos hd ht)
  simpa only [divisorAPCount, hset, Nat.cast_mul] using h

/-- A divisor sharing a factor with the AP modulus is impossible when the
target residue is primitive. This exact zero is available before Mobius. -/
theorem divisorAPCount_eq_zero_of_incompatible (A B d a t : ℕ)
    (ha : Nat.Coprime a d) (htd : ¬Nat.Coprime t d) : divisorAPCount A B d a t = 0 := by
  have hset : (Finset.Ico A B).filter (fun r => Nat.ModEq d r a ∧ t ∣ r) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨_, hAP, ht⟩ := Finset.mem_filter.mp hr
    have hrd : Nat.Coprime r d := by
      change Nat.gcd r d = 1
      rw [hAP.gcd_eq, ha.gcd_eq_one]
    exact htd (hrd.of_dvd_left ht)
  simp only [divisorAPCount, hset, Finset.card_empty, Nat.cast_zero]

/-- The exact cancellation needed after expanding the original centre
mask. No main term is approximated or assumed. -/
theorem divisorAPCount_dilution_le_two (A B d a c e : ℕ)
    (hd : 0 < d) (hc : 0 < c) (he : 0 < e)
    (hdc : Nat.Coprime d c) (hedc : Nat.Coprime e (d * c)) :
    |divisorAPCount A B d a (c * e) - divisorAPCount A B d a c / (e : ℝ)| ≤ 2 := by
  by_cases hAB : A ≤ B
  · have heD := (Nat.coprime_mul_iff_right.mp hedc).1
    have hdce : Nat.Coprime d (c * e) :=
      Nat.coprime_mul_iff_right.mpr ⟨hdc, heD.symm⟩
    have hce := divisorAPCount_discrepancy A B d a (c * e) hAB hd (mul_pos hc he) hdce
    have hc0 := divisorAPCount_discrepancy A B d a c hAB hd hc hdc
    have heR : (0 : ℝ) < e := by exact_mod_cast he
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast (show 1 ≤ e by omega)
    have hmain : ((B : ℝ) - A) / ((d : ℝ) * ((c * e : ℕ) : ℝ)) =
        (((B : ℝ) - A) / ((d : ℝ) * (c : ℝ))) / (e : ℝ) := by
      push_cast
      rw [div_div]
      congr 1
      ring
    calc
      _ = |(divisorAPCount A B d a (c * e) -
          ((B : ℝ) - A) / ((d : ℝ) * ((c * e : ℕ) : ℝ))) -
          (divisorAPCount A B d a c - ((B : ℝ) - A) / ((d : ℝ) * (c : ℝ))) / (e : ℝ)| := by
        rw [hmain]
        congr 1
        ring
      _ ≤ |divisorAPCount A B d a (c * e) -
          ((B : ℝ) - A) / ((d : ℝ) * ((c * e : ℕ) : ℝ))| +
          |(divisorAPCount A B d a c - ((B : ℝ) - A) / ((d : ℝ) * (c : ℝ))) / (e : ℝ)| := abs_sub _ _
      _ ≤ 1 + 1 / (e : ℝ) := by
        rw [abs_div, abs_of_pos heR]
        exact add_le_add hce (div_le_div_of_nonneg_right hc0 heR.le)
      _ ≤ 2 := by have h := (div_le_one heR).mpr he1; linarith
  · have hempty : Finset.Ico A B = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    simp [divisorAPCount, hempty]

end
end ImbalancedChen.U9SemiprimeSwitch
