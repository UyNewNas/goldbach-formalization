import ImbalancedChen.Part3BrunBudget
import ImbalancedChen.Part3LongSlotBrunTransfer
import ImbalancedChen.Part3RoughAuxiliarySWNormalization
import AnalyticNumberTheory.Mertens.PartialSummation

/-!
# The chart-rough one-long error with arbitrary log accuracy

This is the sharp, unweighted long-interval instance of the Brun comparison.
The short and modulus weights can be complex. Their total masses and the
modulus mass weighted by the reciprocal totient are stated explicitly.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Filter Finset AnalyticNumberTheory.Mertens
open scoped BigOperators

private theorem exists_eventually_prime_harmonic_le_logLog :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ P : Finset ℕ,
      P ⊆ primesUpTo ⌊x⌋₊ → (∑ p ∈ P, (p : ℝ)⁻¹) ≤ C * Real.log (Real.log x) := by
  obtain ⟨C, hC, hmertens⟩ := mertensSecond_eventually
  refine ⟨1 + |mertensSecondConstant| + C, by positivity, ?_⟩
  filter_upwards [hmertens, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with x hM hlog hloglog
  intro P hP
  have hsmall : C / Real.log x ≤ C := div_le_self hC.le hlog
  have hc : mertensSecondConstant ≤ |mertensSecondConstant| := le_abs_self _
  have htop := (abs_le.mp hM).2
  have hsubset : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ primeReciprocalSum ⌊x⌋₊ := by
    simp only [primeReciprocalSum, one_div]
    apply Finset.sum_le_sum_of_subset_of_nonneg hP
    intro p _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg p)
  change 1 ≤ Real.log (Real.log x) at hloglog
  calc
    _ ≤ primeReciprocalSum ⌊x⌋₊ := hsubset
    _ ≤ Real.log (Real.log x) + |mertensSecondConstant| + C := by linarith
    _ ≤ _ := by
      nlinarith only [mul_le_mul_of_nonneg_left hloglog (abs_nonneg mertensSecondConstant),
        mul_le_mul_of_nonneg_left hloglog hC.le]

/-- The rough long integer interval has an error smaller than any fixed
logarithmic accuracy. The first mass bound pays the actual modulus support
with a power reserve. The second pays the exact primitive main term. -/
theorem eventually_longSlot_brunRough_logAccuracy
    (θ : ℝ) (hθ : θ < 1) (A K : ℕ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ S Q P : Finset ℕ, ∀ α ρ : ℕ → ℂ, ∀ L U a z : ℕ,
      1 ≤ z → (z : ℝ) ≤ x ^ (2 / (Real.log (Real.log x)) ^ 3) →
      (∀ p ∈ P, p.Prime ∧ p ≤ z) → (∀ q ∈ Q, 0 < q) → (∀ q ∈ Q, a.Coprime q) →
      (∑ m ∈ S, ‖α m‖) * (∑ q ∈ Q, ‖ρ q‖) ≤ x ^ θ →
      (∑ m ∈ S, ‖α m‖) * (U : ℝ) * (∑ q ∈ Q, ‖ρ q‖ / q.totient) ≤ C * x * Real.log x ^ K →
      ‖part3LongSlotWeightedSignedError S Q α ρ L U a (fun n => (brunRoughIndicator P n : ℝ))‖ ≤
        ε * x / Real.log x ^ A := by
  let δ := (1 - θ) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hgap : 0 < 1 - (θ + δ) := by dsimp [δ]; linarith
  obtain ⟨Cw, _hCw, hW⟩ := exists_eventually_prime_harmonic_le_logLog
  filter_upwards [hW, eventually_brun_support_le_rpow δ hδ,
    eventually_brun_factorial_logAccuracy ((A + K + 1 : ℕ) : ℝ) Cw,
    eventually_const_mul_log_rpow_le_rpow (8 / ε) A (1 - (θ + δ)) hgap,
    Real.tendsto_log_atTop.eventually_ge_atTop (4 * C / ε),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 2,
    eventually_gt_atTop (1 : ℝ)] with x hW hZ hfact hpow hpay hloglog hx
  intro S Q P α ρ L U a z hz hzx hP hq ha hprod hmean
  let h := brunRank x
  let M := ∑ m ∈ S, ‖α m‖
  let W := ∑ p ∈ P, (p : ℝ)⁻¹
  let G := W ^ (h + 1) / (h + 1).factorial
  have hlog := Real.log_pos hx
  have hxpos := zero_lt_one.trans hx
  have hL : 2 ≤ Real.log (Real.log x) := hloglog
  have hexp : 2 / (Real.log (Real.log x)) ^ 3 ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hpow3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL 3
    linarith
  have hzx' : (z : ℝ) ≤ x := hzx.trans
    ((Real.rpow_le_rpow_of_exponent_le hx.le hexp).trans_eq (Real.rpow_one x))
  have hWP : W ≤ Cw * Real.log (Real.log x) := by
    apply hW
    intro p hp
    obtain ⟨hprime, hpz⟩ := hP p hp
    exact mem_primesUpTo.mpr ⟨hprime, hpz.trans ((Nat.le_floor_iff hxpos.le).mpr hzx')⟩
  have hG : G ≤ 1 / Real.log x ^ (A + K + 1) := by
    have h := hfact W (sum_nonneg fun _ _ => by positivity) hWP
    rw [Real.rpow_neg hlog.le, Real.rpow_natCast, ← one_div] at h
    exact h
  have hG0 : 0 ≤ G := by dsimp [G, W]; positivity
  have hZ' : (z : ℝ) ^ (h + 1) ≤ x ^ δ := by
    simpa only [Nat.cast_pow] using hZ z hzx
  have hz1 : (1 : ℝ) ≤ z := Nat.one_le_cast.mpr hz
  have hZ0 : (z : ℝ) ^ h ≤ x ^ δ := (pow_le_pow_right₀ hz1 (Nat.le_succ h)).trans hZ'
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbase := part3LongSlotBrunRoughSignedError_norm_le_of_prime_cap S Q P α ρ L U a z h
    hz hP (brunRank_even x) hq ha
  have he : ‖part3LongSlotWeightedSignedError S Q α ρ L U a (fun n => (brunRoughIndicator P n : ℝ))‖ ≤
      4 * x ^ (θ + δ) + 2 * (C * x * Real.log x ^ K) * G := by
    calc
      _ ≤ M * ∑ q ∈ Q, ‖ρ q‖ * (4 * x ^ δ + 2 * ((U : ℝ) / q.totient * G)) := by
        refine hbase.trans (mul_le_mul_of_nonneg_left (sum_le_sum ?_) hM)
        intro q _
        exact mul_le_mul_of_nonneg_left (by linarith only [hZ0, hZ']) (norm_nonneg _)
      _ = 4 * x ^ δ * (M * ∑ q ∈ Q, ‖ρ q‖) +
          2 * (M * (U : ℝ) * ∑ q ∈ Q, ‖ρ q‖ / q.totient) * G := by
        have hs : (∑ q ∈ Q, ‖ρ q‖ * (4 * x ^ δ + 2 * ((U : ℝ) / q.totient * G))) =
            (4 * x ^ δ) * (∑ q ∈ Q, ‖ρ q‖) +
              (2 * (U : ℝ) * G) * ∑ q ∈ Q, ‖ρ q‖ / q.totient := by
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun q _ => by ring
        rw [hs]
        ring
      _ ≤ 4 * x ^ δ * x ^ θ + 2 * (C * x * Real.log x ^ K) * G := by
        exact add_le_add (mul_le_mul_of_nonneg_left hprod (by positivity))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmean (by norm_num)) hG0)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hxpos, add_comm δ θ]
  have hpower : 4 * x ^ (θ + δ) ≤ (ε / 2) * x / Real.log x ^ A := by
    apply (le_div_iff₀ (pow_pos hlog _)).mpr
    rw [Real.rpow_natCast] at hpow
    calc
      _ = ((8 / ε) * Real.log x ^ A) * ((ε / 2) * x ^ (θ + δ)) := by
        field_simp
        ring
      _ ≤ x ^ (1 - (θ + δ)) * ((ε / 2) * x ^ (θ + δ)) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (ε / 2) * x := by
        rw [mul_left_comm, ← Real.rpow_add hxpos, sub_add_cancel, Real.rpow_one]
  have hmain : 2 * (C * x * Real.log x ^ K) * G ≤ (ε / 2) * x / Real.log x ^ A := by
    have hCpay : 4 * C ≤ ε * Real.log x := by
      simpa only [mul_comm] using (div_le_iff₀ hε).mp hpay
    calc
      _ ≤ 2 * (C * x * Real.log x ^ K) * (1 / Real.log x ^ (A + K + 1)) :=
        mul_le_mul_of_nonneg_left hG (by positivity)
      _ = ((2 * C) / Real.log x) * (x / Real.log x ^ A) := by
        rw [pow_succ, pow_add]
        field_simp
      _ ≤ (ε / 2) * (x / Real.log x ^ A) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact (div_le_iff₀ hlog).mpr (by nlinarith only [hCpay])
      _ = _ := by ring
  exact he.trans ((add_le_add hpower hmain).trans_eq (by ring))

/-- With all primes up to the cutoff, the indicator is the literal rough
coefficient used in the medium and prime-product branches. -/
theorem brunRoughIndicator_primesUpTo_eq_roughOneSlot (z n : ℕ) :
    (brunRoughIndicator (primesUpTo z) n : ℂ) = roughOneSlot (z : ℝ) n := by
  have hcut : ((primesUpTo z).filter fun p => p ∣ n).card = 0 ↔
      ∀ p : ℕ, p.Prime → p ∣ n → (z : ℝ) < p := by
    rw [card_eq_zero, filter_eq_empty_iff]
    constructor
    · intro hn p hp hpn
      have hz : z < p := lt_of_not_ge fun hpz => hn (mem_primesUpTo.mpr ⟨hp, hpz⟩) hpn
      exact_mod_cast hz
    · intro hn p hp hpn
      obtain ⟨hprime, hpz⟩ := mem_primesUpTo.mp hp
      exact ((show (p : ℝ) ≤ z from Nat.cast_le.mpr hpz).not_gt (hn p hprime hpn))
  simp only [brunRoughIndicator, roughOneSlot, hcut]
  split_ifs <;> norm_num

end

end ImbalancedChen.Part3
