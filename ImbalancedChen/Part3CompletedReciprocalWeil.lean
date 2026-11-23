import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryCompleteWeil
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryArithmeticPoisson

/-!
# The completed reciprocal sum in the medium distribution argument

The nonzero-frequency estimate uses the unconditional complete Weil bound.
The zero frequency is retained explicitly, as required by equation (17) of
`distribution-medium-completion-20261010.txt`.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Finset MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators SchwartzMap FourierTransform

private def decayOnMultiples (t : ℝ) (d : ℕ) (m : ℤ) : ℝ :=
  if (d : ℤ) ∣ m then poissonNonzeroDecay t m else 0

private theorem poissonNonzeroDecay_nonneg {t : ℝ} (ht : 0 < t) (m : ℤ) :
    0 ≤ poissonNonzeroDecay t m := by
  unfold poissonNonzeroDecay
  split_ifs <;> positivity

private theorem decayOnMultiples_nonneg {t : ℝ} (ht : 0 < t) (d : ℕ) (m : ℤ) :
    0 ≤ decayOnMultiples t d m := by
  unfold decayOnMultiples
  split_ifs
  · exact poissonNonzeroDecay_nonneg ht m
  · exact le_rfl

private theorem decayOnMultiples_summable {t : ℝ} (ht : 0 < t) (d : ℕ) :
    Summable (decayOnMultiples t d) := by
  apply (poissonNonzeroDecay_summable_tsum_le ht).1.of_nonneg_of_le
    (decayOnMultiples_nonneg ht d)
  intro m
  unfold decayOnMultiples
  split_ifs
  · exact le_rfl
  · exact poissonNonzeroDecay_nonneg ht m

/-- The factor `1/d` holds at every mesh, since the zero Fourier term has
already been excluded. -/
private theorem weighted_decayOnMultiples_tsum_le {t : ℝ} (ht : 0 < t)
    {d : ℕ} (hd : 0 < d) :
    (∑' m : ℤ, (d : ℝ) * decayOnMultiples t d m) ≤ 2 := by
  have hdInt : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  let f : ℤ → ℝ := fun m => (d : ℝ) * decayOnMultiples t d m
  have hsupport : Function.support f ⊆ Set.range (fun k : ℤ => (d : ℤ) * k) := by
    intro m hm
    by_contra h
    have hn : ¬ (d : ℤ) ∣ m := by
      rintro ⟨k, hk⟩
      exact h ⟨k, hk.symm⟩
    exact hm (by simp [f, decayOnMultiples, hn])
  have hinj : Function.Injective (fun k : ℤ => (d : ℤ) * k) := fun _ _ h =>
    mul_left_cancel₀ hdInt h
  have hscale (k : ℤ) : f ((d : ℤ) * k) = poissonNonzeroDecay (t * d) k := by
    by_cases hk : k = 0
    · simp [f, hk, decayOnMultiples, poissonNonzeroDecay]
    · simp only [f, decayOnMultiples, dvd_mul_right, if_true, poissonNonzeroDecay,
        mul_ne_zero hdInt hk, if_false, hk, Int.cast_mul, Int.cast_natCast]
      rw [← mul_assoc, ← mul_div_assoc, mul_comm (d : ℝ) t]
  change (∑' m : ℤ, f m) ≤ 2
  rw [← hinj.tsum_eq hsupport]
  simpa only [Function.comp_def, hscale] using
    (poissonNonzeroDecay_summable_tsum_le (show 0 < t * d by positivity)).2

private theorem norm_completeKloosterman_le_divisor_weight
    (q : ℕ) [NeZero q] (m a : ℤ) :
    ‖completeKloosterman q (m : ZMod q) a‖ ≤
      (q.divisors.card : ℝ) * Real.sqrt q *
        ∑ d ∈ q.divisors, (if (d : ℤ) ∣ m then (d : ℝ) else 0) := by
  classical
  let g := q.gcd (m.natAbs.gcd a.natAbs)
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (NeZero.pos q)
  have hgq : g ∈ q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, NeZero.ne q⟩
  have hgm : (g : ℤ) ∣ m := by
    rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast]
    exact (Nat.gcd_dvd_right q _).trans (Nat.gcd_dvd_left m.natAbs a.natAbs)
  have hg : Real.sqrt (g : ℝ) ≤ (g : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hgpos))
  have hsingle : (g : ℝ) ≤
      ∑ d ∈ q.divisors, (if (d : ℤ) ∣ m then (d : ℝ) else 0) := by
    simpa only [if_pos hgm] using
      (Finset.single_le_sum (f := fun d : ℕ => if (d : ℤ) ∣ m then (d : ℝ) else 0)
        (fun d _ => by split_ifs <;> positivity) hgq)
  calc
    _ ≤ (q.divisors.card : ℝ) * Real.sqrt (g : ℝ) * Real.sqrt q :=
      completeKloosterman_weil q m a
    _ = (q.divisors.card : ℝ) * Real.sqrt q * Real.sqrt (g : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hg.trans hsingle) (by positivity)

/-- For any profile with explicit Fourier decay, the nonzero terms of the
completed series cost `2 C τ(q)^2 √q`, uniformly in the inverse phase and mesh. -/
theorem completedReciprocal_nonzero_norm_le (q : ℕ) [NeZero q] (a : ℤ)
    (t : ℝ) (ht : 0 < t) (F : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ x : ℝ, ‖F x‖ ≤ C / (1 + |x|) ^ 2) :
    Summable (fun m : ℤ => ‖if m = 0 then 0 else
      t • F (t * (m : ℝ)) * completeKloosterman q (m : ZMod q) a‖) ∧
    ‖∑' m : ℤ, if m = 0 then 0 else
      t • F (t * (m : ℝ)) * completeKloosterman q (m : ZMod q) a‖ ≤
      2 * C * (q.divisors.card : ℝ) ^ 2 * Real.sqrt q := by
  classical
  let B : ℝ := C * (q.divisors.card : ℝ) * Real.sqrt q
  let f : ℤ → ℂ := fun m => if m = 0 then 0 else
    t • F (t * (m : ℝ)) * completeKloosterman q (m : ZMod q) a
  let g : ℕ → ℤ → ℝ := fun d m => (d : ℝ) * decayOnMultiples t d m
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hgd (d : ℕ) : Summable (g d) := (decayOnMultiples_summable ht d).mul_left _
  have hsum : Summable (fun m => ∑ d ∈ q.divisors, g d m) :=
    summable_sum (fun d _ => hgd d)
  have hpoint (m : ℤ) : ‖f m‖ ≤ B * ∑ d ∈ q.divisors, g d m := by
    by_cases hm : m = 0
    · simp [f, g, hm, decayOnMultiples, poissonNonzeroDecay]
    · have hg (d : ℕ) : g d m = (if (d : ℤ) ∣ m then (d : ℝ) else 0) *
          (t / (1 + |t * (m : ℝ)|) ^ 2) := by
        by_cases hd : (d : ℤ) ∣ m <;> simp [g, decayOnMultiples, poissonNonzeroDecay, hm, hd]
      simp only [f, if_neg hm, norm_mul, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      calc
        _ ≤ (t * (C / (1 + |t * (m : ℝ)|) ^ 2)) *
            ((q.divisors.card : ℝ) * Real.sqrt q *
              ∑ d ∈ q.divisors, (if (d : ℤ) ∣ m then (d : ℝ) else 0)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hdecay _) ht.le)
            (norm_completeKloosterman_le_divisor_weight q m a) (norm_nonneg _) (by positivity)
        _ = _ := by simp_rw [hg, ← Finset.sum_mul]; dsimp [B]; ring
  have hf : Summable (fun m => ‖f m‖) :=
    (hsum.mul_left B).of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  refine ⟨hf, (norm_tsum_le_tsum_norm hf).trans ?_⟩
  calc
    _ ≤ ∑' m : ℤ, B * ∑ d ∈ q.divisors, g d m := hf.tsum_le_tsum hpoint (hsum.mul_left _)
    _ = B * ∑ d ∈ q.divisors, ∑' m : ℤ, g d m := by
      rw [tsum_mul_left, Summable.tsum_finsetSum (fun d _ => hgd d)]
    _ ≤ B * ∑ _d ∈ q.divisors, (2 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact sum_le_sum (fun d hd => weighted_decayOnMultiples_tsum_le ht
        (Nat.pos_of_mem_divisors hd))
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; dsimp [B]; ring

/-- The pinned phase is the manuscript's signed additive character on the
inverse of the residue, with the same unit condition. -/
theorem reciprocalPhase_nat_eq_fourier (q : ℕ) [NeZero q] (a : ℤ) (n : ℕ) :
    reciprocalPhase q a (n : ZMod q) =
      if Nat.Coprime n q then
        fourier 1 (((a : ℝ) * (((n : ZMod q)⁻¹).val : ℝ) / (q : ℝ)) : UnitAddCircle)
      else 0 := by
  simp only [reciprocalPhase, ZMod.isUnit_iff_coprime]
  split_ifs
  · have he : (a : ZMod q) * (n : ZMod q)⁻¹ =
        ((a * ((((n : ZMod q)⁻¹).val : ℕ) : ℤ) : ℤ) : ZMod q) := by
      simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [he, ZMod.stdAddChar_coe, fourier_coe_apply]
    push_cast
    congr 1
    ring
  · rfl

/-- The original finite smooth sum with the reciprocal phase modulo `q`. -/
def dyadicReciprocalSum (q : ℕ) [NeZero q] (a : ℤ) (N : ℝ) : ℂ :=
  ∑ n ∈ dyadicCutoffNatSupport N,
    (scaledDyadicCutoff N n : ℂ) * reciprocalPhase q a (n : ZMod q)

private theorem sum_reciprocal_by_residue (q : ℕ) [NeZero q] (a : ℤ) (N : ℝ) :
    dyadicReciprocalSum q a N = ∑ u : ZMod q, reciprocalPhase q a u *
      ∑ n ∈ dyadicCutoffNatSupport N, if Int.ModEq q (n : ℤ) (u.val : ℤ)
        then (scaledDyadicCutoff N n : ℂ) else 0 := by
  have hclass (n : ℕ) (u : ZMod q) :
      Int.ModEq q (n : ℤ) (u.val : ℤ) ↔ (n : ZMod q) = u := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
      (ZMod.intCast_eq_intCast_iff (n : ℤ) (u.val : ℤ) q).symm
  symm
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold dyadicReciprocalSum
  apply Finset.sum_congr rfl
  intro n hn
  simp_rw [hclass]
  rw [Finset.sum_eq_single (n : ZMod q)]
  · simp only [if_true]
    exact mul_comm _ _
  · intro u hu hne
    simp [Ne.symm hne]
  · simp

private theorem fourier_at_residue (q : ℕ) [NeZero q] (m : ℤ) (u : ZMod q) :
    fourier m (((u.val : ℝ) / (q : ℝ)) : UnitAddCircle) =
      ZMod.stdAddChar ((m : ZMod q) * u) := by
  have hu : ((m * (u.val : ℤ) : ℤ) : ZMod q) = (m : ZMod q) * u := by
    simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← hu, ZMod.stdAddChar_coe, fourier_coe_apply]
  push_cast
  congr 1
  ring

/-- The exact Poisson identity, with the zero Kloosterman term separated
before the frequency bound is applied. -/
theorem dyadicReciprocalSum_sub_zero_eq_tsum (q : ℕ) [NeZero q] (a : ℤ)
    {N : ℝ} (hN : 0 < N) :
    dyadicReciprocalSum q a N -
        ((N / (q : ℝ)) • (𝓕 dyadicCutoffSchwartz) 0) * completeKloosterman q 0 a =
      ∑' m : ℤ, if m = 0 then 0 else
        ((N / (q : ℝ)) • (𝓕 dyadicCutoffSchwartz) ((N / (q : ℝ)) * (m : ℝ))) *
          completeKloosterman q (m : ZMod q) a := by
  classical
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  let t : ℝ := N / q
  have ht : 0 < t := div_pos hN hq
  let F := 𝓕 dyadicCutoffSchwartz
  let R : ZMod q → ℤ → ℂ := fun u m =>
    reciprocalPhase q a u * dyadicCutoffPoissonRemainder t ((u.val : ℝ) / q) m
  have hrow (u : ZMod q) :
      reciprocalPhase q a u *
        ((∑ n ∈ dyadicCutoffNatSupport N, if Int.ModEq q (n : ℤ) (u.val : ℤ)
          then (scaledDyadicCutoff N n : ℂ) else 0) - t • F 0) =
        ∑' m : ℤ, R u m := by
    rw [scaledDyadicCutoff_progression_eq_tsum hN (NeZero.pos q)]
    have hpoisson := scaledDyadicCutoff_poisson_mainTerm hN hq (u.val : ℝ)
    rw [Int.cast_natCast, hpoisson]
    exact tsum_mul_left.symm
  have hs (u : ZMod q) : Summable (R u) := by
    obtain ⟨C, _, hbound⟩ := dyadicCutoffPoissonRemainder_uniform
    exact ((hbound t ht ((u.val : ℝ) / q)).1.of_norm).mul_left _
  calc
    _ = ∑ u : ZMod q, reciprocalPhase q a u *
        ((∑ n ∈ dyadicCutoffNatSupport N, if Int.ModEq q (n : ℤ) (u.val : ℤ)
          then (scaledDyadicCutoff N n : ℂ) else 0) - t • F 0) := by
      have hzero : (t • F 0) * completeKloosterman q 0 a =
          ∑ u : ZMod q, reciprocalPhase q a u * (t • F 0) := by
        simp only [completeKloosterman, zero_mul, AddChar.map_zero_eq_one, one_mul]
        rw [mul_comm (t • F 0), Finset.sum_mul]
      rw [sum_reciprocal_by_residue, hzero]
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ = ∑ u : ZMod q, ∑' m : ℤ, R u m := Finset.sum_congr rfl (fun u _ => hrow u)
    _ = ∑' m : ℤ, ∑ u : ZMod q, R u m :=
      (Summable.tsum_finsetSum (fun u _ => hs u)).symm
    _ = _ := by
      apply tsum_congr
      intro m
      by_cases hm : m = 0
      · simp [hm, R, dyadicCutoffPoissonRemainder]
      · simp only [if_neg hm, R, dyadicCutoffPoissonRemainder, fourier_at_residue,
          completeKloosterman, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        change reciprocalPhase q a u *
            ((t • F (t * (m : ℝ))) * ZMod.stdAddChar ((m : ZMod q) * u)) =
          (t • F (t * (m : ℝ))) *
            (ZMod.stdAddChar ((m : ZMod q) * u) * reciprocalPhase q a u)
        ac_rfl

/-- The nonzero term in the physical smooth inverse-phase sum has the
uniform `τ(q)^2 √q` bound. The complete zero term stays on the left. -/
theorem dyadicReciprocalSum_sub_zero_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (a : ℤ) (N : ℝ), 0 < N →
      ‖dyadicReciprocalSum q a N -
        ((N / (q : ℝ)) • (𝓕 dyadicCutoffSchwartz) 0) * completeKloosterman q 0 a‖ ≤
        C * (q.divisors.card : ℝ) ^ 2 * Real.sqrt q := by
  obtain ⟨C, hC, hdecay⟩ := schwartz_norm_le_rapidDecay (𝓕 dyadicCutoffSchwartz) 2
  refine ⟨2 * C, by positivity, ?_⟩
  intro q hq a N hN
  rw [dyadicReciprocalSum_sub_zero_eq_tsum q a hN]
  exact (completedReciprocal_nonzero_norm_le q a (N / (q : ℝ))
    (div_pos hN (by exact_mod_cast NeZero.pos q)) _ C hC.le hdecay).2

private theorem zeroLeft_prime_power_norm_le_gcd (p k : ℕ) [Fact p.Prime]
    (a : ℤ) : ‖completeKloosterman (p ^ k) ((0 : ℤ) : ZMod (p ^ k)) a‖ ≤
      ((p ^ k).gcd a.natAbs : ℝ) := by
  have hp : p.Prime := Fact.out
  induction k generalizing a with
  | zero =>
      rw [localGlobal_completeKloosterman_congr_modulus _ _ (pow_zero p),
        localGlobal_completeKloosterman_one]
      simp
  | succ k ih =>
      by_cases hdiv : (p : ℤ) ∣ a
      · obtain ⟨b, rfl⟩ := hdiv
        have hdescent := localGlobal_prime_power_descent_norm p k 0 b
        simp only [mul_zero] at hdescent
        have hg := localGlobal_gcd_scale p (p ^ k) 0 b
        simp only [mul_zero, Int.natAbs_zero, Nat.gcd_zero_left] at hg
        have hgp : (p ^ (k + 1)).gcd ((p : ℤ) * b).natAbs =
            p * (p ^ k).gcd b.natAbs := by rw [pow_succ', hg]
        rw [hgp, Nat.cast_mul]
        exact hdescent.trans (mul_le_mul_of_nonneg_left (ih b) (Nat.cast_nonneg p))
      · cases k with
        | zero =>
            rw [localGlobal_completeKloosterman_congr_modulus _ _ (pow_one p)]
            simpa only [Int.cast_zero, completeKloosterman_prime_zero_left p a hdiv,
              norm_neg, norm_one, zero_add, pow_one] using
              (show (1 : ℝ) ≤ (p.gcd a.natAbs : ℝ) by
                exact_mod_cast Nat.gcd_pos_of_pos_left a.natAbs hp.pos)
        | succ k =>
            rw [localGlobal_completeKloosterman_congr_modulus _ _
              (pow_succ' p (k + 1)),
              completeKloosterman_prime_power_vanish_left p k 0 a (dvd_zero _) hdiv,
              norm_zero]
            exact Nat.cast_nonneg _

/-- The zero Poisson frequency is a Ramanujan sum. Its gcd bound follows
from the exact prime-power descent and the coprime CRT identity. -/
theorem completeKloosterman_zero_left_norm_le_gcd (q : ℕ) [NeZero q] (a : ℤ) :
    ‖completeKloosterman q 0 a‖ ≤ (q.gcd a.natAbs : ℝ) := by
  have hall : ∀ (q : ℕ) (_ : NeZero q) (a : ℤ),
      ‖completeKloosterman q ((0 : ℤ) : ZMod q) a‖ ≤ (q.gcd a.natAbs : ℝ) := by
    refine Nat.recOnPrimeCoprime ?_ ?_ ?_
    · intro hq
      exact False.elim (hq.out rfl)
    · intro p k hp _ a
      let : Fact p.Prime := ⟨hp⟩
      exact zeroLeft_prime_power_norm_le_gcd p k a
    · intro m n hm hn hmn hmBound hnBound _ a
      let : NeZero m := ⟨by omega⟩
      let : NeZero n := ⟨by omega⟩
      have htwist := localGlobal_bezout_coprime m n hmn
      have hleft := hmBound inferInstance (a * m.gcdB n)
      have hright := hnBound inferInstance (a * m.gcdA n)
      have hleftGcd := localGlobal_gcd_twist m _ 0 a htwist.1
      have hrightGcd := localGlobal_gcd_twist n _ 0 a htwist.2
      simp only [zero_mul, Int.natAbs_zero, Nat.gcd_zero_left] at hleftGcd hrightGcd
      rw [hleftGcd] at hleft
      rw [hrightGcd] at hright
      rw [completeKloosterman_crt m n hmn,
        localGlobal_gcd_coprime_mul m n a.natAbs hmn, Nat.cast_mul]
      simp only [zero_mul, norm_mul]
      exact mul_le_mul hleft hright (norm_nonneg _) (Nat.cast_nonneg _)
  simpa only [Int.cast_zero] using hall q inferInstance a

/-- The nonzero Fourier contribution to one primitive mass has an
absolute bound of `2 C τ(q)` for every positive mesh. -/
theorem completedRamanujan_nonzero_norm_le (q : ℕ) [NeZero q]
    (t : ℝ) (ht : 0 < t) (F : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ x : ℝ, ‖F x‖ ≤ C / (1 + |x|) ^ 2) :
    ‖∑' m : ℤ, if m = 0 then 0 else
      (t • F (t * (m : ℝ))) * completeKloosterman q 0 m‖ ≤
      2 * C * (q.divisors.card : ℝ) := by
  classical
  let f (m : ℤ) := if m = 0 then 0 else (t • F (t * (m : ℝ))) * completeKloosterman q 0 m
  let g (d : ℕ) (m : ℤ) := (d : ℝ) * decayOnMultiples t d m
  have hgd (d : ℕ) : Summable (g d) := (decayOnMultiples_summable ht d).mul_left _
  have hsum : Summable (fun m => ∑ d ∈ q.divisors, g d m) := summable_sum (fun d _ => hgd d)
  have hpoint (m : ℤ) : ‖f m‖ ≤ C * ∑ d ∈ q.divisors, g d m := by
    by_cases hm : m = 0
    · simp [f, g, hm, decayOnMultiples, poissonNonzeroDecay]
    · let d := q.gcd m.natAbs
      have hd : d ∈ q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, NeZero.ne q⟩
      have hdm : (d : ℤ) ∣ m := by
        rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast]
        exact Nat.gcd_dvd_right _ _
      have hsingle : g d m ≤ ∑ i ∈ q.divisors, g i m :=
        single_le_sum (fun i _ => mul_nonneg (Nat.cast_nonneg i) (decayOnMultiples_nonneg ht i _)) hd
      calc
        ‖f m‖ ≤ (t * (C / (1 + |t * (m : ℝ)|) ^ 2)) * (d : ℝ) := by
          simp only [f, if_neg hm, norm_mul, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hdecay _) ht.le)
            (completeKloosterman_zero_left_norm_le_gcd q m) (norm_nonneg _) (by positivity)
        _ = C * g d m := by
          simp only [g, decayOnMultiples, hdm, if_true, poissonNonzeroDecay, hm, if_false]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsingle hC
  have hf := (hsum.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  refine (norm_tsum_le_tsum_norm hf).trans ((hf.tsum_le_tsum hpoint (hsum.mul_left _)).trans ?_)
  calc
    _ = C * ∑ d ∈ q.divisors, ∑' m : ℤ, g d m := by
      rw [tsum_mul_left, Summable.tsum_finsetSum (fun d _ => hgd d)]
    _ ≤ C * ∑ _d ∈ q.divisors, (2 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact sum_le_sum (fun d hd => weighted_decayOnMultiples_tsum_le ht (Nat.pos_of_mem_divisors hd))
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

/-- Equation (17) for the fixed physical dyadic cutoff. There are no
restrictions on the phase or on the relative sizes of `N` and `q`. -/
theorem dyadicReciprocalSum_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (a : ℤ) (N : ℝ), 0 < N →
      ‖dyadicReciprocalSum q a N‖ ≤ C *
        ((q.divisors.card : ℝ) ^ 2 * Real.sqrt q +
          (N / (q : ℝ)) * (q.gcd a.natAbs : ℝ)) := by
  obtain ⟨C, hC, hnonzero⟩ := dyadicReciprocalSum_sub_zero_norm_le
  let F := 𝓕 dyadicCutoffSchwartz
  let C' := max C ‖F 0‖
  refine ⟨C', hC.trans_le (le_max_left _ _), ?_⟩
  intro q hq a N hN
  let t : ℝ := N / q
  have ht : 0 ≤ t := div_nonneg hN.le (Nat.cast_nonneg _)
  let z : ℂ := (t • F 0) * completeKloosterman q 0 a
  have hzero : ‖z‖ ≤ ‖F 0‖ * (t * (q.gcd a.natAbs : ℝ)) := by
    simp only [z, norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    calc
      _ ≤ (t * ‖F 0‖) * (q.gcd a.natAbs : ℝ) :=
        mul_le_mul_of_nonneg_left (completeKloosterman_zero_left_norm_le_gcd q a)
          (mul_nonneg ht (norm_nonneg _))
      _ = _ := by ring
  calc
    ‖dyadicReciprocalSum q a N‖ = ‖(dyadicReciprocalSum q a N - z) + z‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖dyadicReciprocalSum q a N - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ C * ((q.divisors.card : ℝ) ^ 2 * Real.sqrt q) +
        ‖F 0‖ * (t * (q.gcd a.natAbs : ℝ)) := by
      apply add_le_add _ hzero
      simpa only [mul_assoc] using hnonzero q a N hN
    _ ≤ C' * ((q.divisors.card : ℝ) ^ 2 * Real.sqrt q) +
        C' * (t * (q.gcd a.natAbs : ℝ)) := by
      exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg ht (Nat.cast_nonneg _)))
    _ = _ := (mul_add _ _ _).symm

end

end ImbalancedChen.Part3
