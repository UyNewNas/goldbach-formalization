import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
import ImbalancedChen.Part3CenteredFourier

/-!
Source-only, 2026-10-25. UNCOMPILED / NOT_ROOT_ACCEPTED.

A finite bijection parametrizes the p-multiple residues modulo p*d.
Their exact character sum is obtained by cancelling p in the phase.
Subtracting that sum from complete character orthogonality evaluates the
literal Ramanujan sum at every positive prime-power exponent.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.PrimePowerRamanujanSourceOnly

open scoped BigOperators

/-- Multiplication of least representatives embeds the d residues as the
p-multiple representatives modulo p*d. -/
def multipleResidue (p d : ℕ) (j : ZMod d) : ZMod (p * d) :=
  (p * j.val : ℕ)

theorem multipleResidue_val (p d : ℕ) [NeZero p] [NeZero d] (j : ZMod d) :
    (multipleResidue p d j).val = p * j.val := by
  change ((p * j.val : ℕ) : ZMod (p * d)).val = p * j.val
  apply ZMod.val_natCast_of_lt
  exact Nat.mul_lt_mul_of_pos_left j.val_lt (Nat.pos_of_ne_zero (NeZero.ne p))

abbrev MultipleResidue (p d : ℕ) := {u : ZMod (p * d) // p ∣ u.val}

def multipleResidueMap (p d : ℕ) [NeZero p] [NeZero d] (j : ZMod d) :
    MultipleResidue p d :=
  ⟨multipleResidue p d j, by
    rw [multipleResidue_val]
    exact dvd_mul_right p j.val⟩

/-- Injectivity follows from equality of the actual least representatives
and cancellation of the nonzero natural number p. -/
theorem multipleResidueMap_injective (p d : ℕ) [NeZero p] [NeZero d] :
    Function.Injective (multipleResidueMap p d) := by
  intro j k hjk
  have hv := congrArg (fun u : MultipleResidue p d => u.1.val) hjk
  change (multipleResidue p d j).val = (multipleResidue p d k).val at hv
  rw [multipleResidue_val, multipleResidue_val] at hv
  apply ZMod.val_injective d
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne p)) hv

/-- Every p-divisible least representative has a quotient below d. -/
theorem multipleResidueMap_surjective (p d : ℕ) [NeZero p] [NeZero d] :
    Function.Surjective (multipleResidueMap p d) := by
  intro u
  obtain ⟨j, hj⟩ := u.2
  have hjlt : j < d := by
    have hv := u.1.val_lt
    rw [hj] at hv
    by_contra hnot
    have hle : d ≤ j := Nat.le_of_not_gt hnot
    exact (not_le_of_gt hv) (Nat.mul_le_mul_left p hle)
  refine ⟨(j : ZMod d), ?_⟩
  apply Subtype.ext
  apply ZMod.val_injective (p * d)
  change (multipleResidue p d (j : ZMod d)).val = u.1.val
  rw [multipleResidue_val, ZMod.val_natCast_of_lt hjlt, hj]

/-- Exact finite parametrization of the p-multiple residues. -/
def multipleResidueEquiv (p d : ℕ) [NeZero p] [NeZero d] :
    ZMod d ≃ MultipleResidue p d :=
  Equiv.ofBijective (multipleResidueMap p d)
    ⟨multipleResidueMap_injective p d, multipleResidueMap_surjective p d⟩

/-- The standard positive additive character respects cancellation of a
common nonzero natural factor in numerator and modulus. -/
theorem stdAddChar_cancel_modulus (p d : ℕ) [NeZero p] [NeZero d] (A : ℤ) :
    ZMod.stdAddChar (((p : ℤ) * A : ℤ) : ZMod (p * d)) =
      ZMod.stdAddChar (A : ZMod d) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp [hp0, hd0] <;> ring

/-- Pointwise phase transport for the actual p-multiple representative. -/
theorem multipleResidue_phase (p d : ℕ) [NeZero p] [NeZero d]
    (n : ℤ) (j : ZMod d) :
    ZMod.stdAddChar ((n : ZMod (p * d)) * multipleResidue p d j) =
      ZMod.stdAddChar ((n : ZMod d) * j) := by
  have hphase := stdAddChar_cancel_modulus p d (n * (j.val : ℤ))
  have hleft : (((p : ℤ) * (n * (j.val : ℤ)) : ℤ) : ZMod (p * d)) =
      (n : ZMod (p * d)) * multipleResidue p d j := by
    simp only [multipleResidue, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    ring
  have hright : ((n * (j.val : ℤ) : ℤ) : ZMod d) = (n : ZMod d) * j := by
    simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [hleft, hright] at hphase
  exact hphase

/-- The finite parametrization is additive as a map into the ambient
residue ring. This follows from the injective standard additive characters
and the proved cancellation of its positive phase. -/
theorem multipleResidue_add (p d : ℕ) [NeZero p] [NeZero d] (j k : ZMod d) :
    multipleResidue p d (j + k) = multipleResidue p d j + multipleResidue p d k := by
  have hphase (u : ZMod d) :
      ZMod.stdAddChar (multipleResidue p d u) = ZMod.stdAddChar u := by
    simpa only [Int.cast_one, one_mul] using multipleResidue_phase p d 1 u
  apply ZMod.injective_stdAddChar
  simp only [AddChar.map_add_eq_mul, hphase]
/-- Exact character sum over the genuine p-multiple residue subset. -/
theorem sum_multipleResidue_phase (p d : ℕ) [NeZero p] [NeZero d] (n : ℤ) :
    (∑ u : MultipleResidue p d,
      ZMod.stdAddChar ((n : ZMod (p * d)) * u.1)) =
      if (d : ℤ) ∣ n then (d : ℂ) else 0 := by
  calc
    _ = ∑ j : ZMod d,
        ZMod.stdAddChar ((n : ZMod (p * d)) * multipleResidue p d j) := by
      exact ((multipleResidueEquiv p d).sum_comp
        (fun u : MultipleResidue p d =>
          ZMod.stdAddChar ((n : ZMod (p * d)) * u.1))).symm
    _ = ∑ j : ZMod d, ZMod.stdAddChar ((n : ZMod d) * j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact multipleResidue_phase p d n j
    _ = _ := by
      simpa only [mul_comm, ZMod.intCast_zmod_eq_zero_iff_dvd] using
        ImbalancedChen.Part3.sum_stdAddChar_mul_eq d (n : ZMod d)

/-- The same exact p-multiple sum, with the gate written inside the
complete residue sum so it can be subtracted from the unit-gated sum. -/
theorem sum_multipleResidue_filter (p d : ℕ) [NeZero p] [NeZero d] (n : ℤ) :
    (∑ u : ZMod (p * d), if p ∣ u.val then
      ZMod.stdAddChar ((n : ZMod (p * d)) * u) else 0) =
      if (d : ℤ) ∣ n then (d : ℂ) else 0 := by
  have hsum : (∑ u : MultipleResidue p d,
      ZMod.stdAddChar ((n : ZMod (p * d)) * u.1)) =
      ∑ u ∈ (Finset.univ : Finset (ZMod (p * d))).filter (fun u => p ∣ u.val),
        ZMod.stdAddChar ((n : ZMod (p * d)) * u) := by
    apply Finset.sum_bij (fun u _ => u.1)
    · intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2⟩
    · intro u hu v hv huv
      exact Subtype.ext huv
    · intro u hu
      exact ⟨⟨u, (Finset.mem_filter.mp hu).2⟩, Finset.mem_univ _, rfl⟩
    · intro u hu
      rfl
  rw [Finset.sum_filter] at hsum
  rw [← hsum]
  exact sum_multipleResidue_phase p d n

/-- Units and p-multiples partition all residues modulo p^(k+1).
Thus the literal Ramanujan sum is the difference of two fully evaluated
complete character sums. -/
theorem primePower_ramanujan_add_multiple (p : ℕ) (hp : p.Prime)
    (k : ℕ) (n : ℤ) :
    kloosterman (p * p ^ k) n 0 +
      (if ((p ^ k : ℕ) : ℤ) ∣ n then ((p ^ k : ℕ) : ℂ) else 0) =
      if ((p * p ^ k : ℕ) : ℤ) ∣ n then ((p * p ^ k : ℕ) : ℂ) else 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  let f : ZMod (p * p ^ k) → ℂ := fun u =>
    ZMod.stdAddChar ((n : ZMod (p * p ^ k)) * u)
  have hgate (u : ZMod (p * p ^ k)) : IsUnit u ↔ ¬ p ∣ u.val := by
    have hh := ZMod.isUnit_natCast_iff_not_dvd_pow
      (a := u.val) hp (Nat.succ_pos k)
    simpa only [pow_succ', ZMod.natCast_zmod_val] using hh
  have hterm (u : ZMod (p * p ^ k)) :
      f u = (if IsUnit u then f u else 0) + (if p ∣ u.val then f u else 0) := by
    by_cases hu : p ∣ u.val
    · simp only [hgate u, hu, not_true_eq_false, if_false, if_true, zero_add]
    · simp only [hgate u, hu, not_false_eq_true, if_true, if_false, add_zero]
  have hsplit : (∑ u : ZMod (p * p ^ k), f u) =
      (∑ u : ZMod (p * p ^ k), if IsUnit u then f u else 0) +
        ∑ u : ZMod (p * p ^ k), if p ∣ u.val then f u else 0 := by
    calc
      _ = ∑ u : ZMod (p * p ^ k),
          ((if IsUnit u then f u else 0) + (if p ∣ u.val then f u else 0)) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hterm u
      _ = _ := Finset.sum_add_distrib
  have hmultiple := sum_multipleResidue_filter p (p ^ k) n
  have horth := ImbalancedChen.Part3.sum_stdAddChar_mul_eq
    (p * p ^ k) (n : ZMod (p * p ^ k))
  have hunit : kloosterman (p * p ^ k) n 0 =
      ∑ u : ZMod (p * p ^ k), if IsUnit u then f u else 0 := by
    rw [Physical.kloosterman_eq_zmod]
    simp only [Int.cast_zero, zero_mul, add_zero, f]
  rw [hunit, ← hmultiple, ← hsplit]
  simpa only [f, mul_comm, ZMod.intCast_zmod_eq_zero_iff_dvd] using horth

/-- Exact Ramanujan evaluation at every positive prime-power exponent.
The first branch is Euler's totient p^k*(p-1); the next branch is -p^k. -/
theorem primePower_ramanujan_exact (p : ℕ) (hp : p.Prime)
    (k : ℕ) (n : ℤ) :
    kloosterman (p ^ (k + 1)) n 0 =
      if ((p ^ (k + 1) : ℕ) : ℤ) ∣ n then
        ((p ^ k : ℕ) : ℂ) * ((p : ℂ) - 1)
      else if ((p ^ k : ℕ) : ℤ) ∣ n then -((p ^ k : ℕ) : ℂ) else 0 := by
  have hsum := primePower_ramanujan_add_multiple p hp k n
  simp only [← pow_succ'] at hsum
  by_cases hfull : ((p ^ (k + 1) : ℕ) : ℤ) ∣ n
  · have hlower : ((p ^ k : ℕ) : ℤ) ∣ n := by
      obtain ⟨a, ha⟩ := hfull
      refine ⟨(p : ℤ) * a, ?_⟩
      rw [ha]
      push_cast
      rw [pow_succ']
      ring
    rw [if_pos hfull, if_pos hlower] at hsum
    rw [if_pos hfull]
    push_cast at hsum ⊢
    rw [pow_succ'] at hsum
    linear_combination hsum
  · rw [if_neg hfull] at hsum
    rw [if_neg hfull]
    by_cases hlower : ((p ^ k : ℕ) : ℤ) ∣ n
    · rw [if_pos hlower] at hsum ⊢
      linear_combination hsum
    · rw [if_neg hlower] at hsum ⊢
      simpa only [add_zero] using hsum

end ImbalancedChen.Part3.OriginalSmoothPoissonTail.PrimePowerRamanujanSourceOnly


