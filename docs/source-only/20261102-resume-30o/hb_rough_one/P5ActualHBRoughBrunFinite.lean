import ImbalancedChen.P5OriginalOneLongLiteralBrunDictionary
import ImbalancedChen.P5OriginalPrimitiveCoprimeDensity
import ImbalancedChen.Part3RoughAuxiliarySW

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual strict rough projector and the archived literal Brun divisor bank.
The normalized coprime count has a uniform error 3: compare it with residue
zero (error 2), then count multiples with both endpoints (error 1). Thus the
positive Brun gap can be paid for EVERY q, without a tau(q)/phi(q) loss.
No Brun gap estimate, progression-error estimate or rough SW is an input.
The lower polynomial is never assumed nonnegative.
-/
namespace ImbalancedChen.P5Z.ActualHBRoughBrunFinite
noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open OriginalOneLongFiniteBrun OriginalOneLongDivisorIntervals
open OriginalOneLongSharpBrun OriginalPrimitiveCoprimeDensity
open OriginalOneLongLiteralBrunDictionary OriginalOneLongE5FiniteBudget
open Part3.TwoLongDivisorAxisClosure Part3.BrunFactorialRecurrenceE1

def chartPrimes (z : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor z + 1)).filter Nat.Prime

def brunSupport (z : ℝ) (j : ℕ) : Finset ℕ :=
  divisorSupport (chartPrimes z) (2*j+1)

def upperWeight (z : ℝ) (j d : ℕ) : ℝ :=
  upperCoefficient (chartPrimes z) (2*j) d

def gapWeight (z : ℝ) (j d : ℕ) : ℝ :=
  gapCoefficient (chartPrimes z) (2*j+1) d

def gapDensity (z : ℝ) (j : ℕ) : ℝ := brunEpsilon j (chartPrimes z)

def upperPolynomial (z : ℝ) (j n : ℕ) : ℝ :=
  polynomial (brunSupport z j) divisorMask (upperWeight z j) n

def gapPolynomial (z : ℝ) (j n : ℕ) : ℝ :=
  polynomial (brunSupport z j) divisorMask (gapWeight z j) n

theorem mem_chartPrimes {z : ℝ} (hz : 0 ≤ z) (p : ℕ) :
    p ∈ chartPrimes z ↔ p.Prime ∧ (p : ℝ) ≤ z := by
  simp only [chartPrimes, mem_filter, mem_range, Nat.lt_succ_iff,
    Nat.le_floor_iff hz, and_comm]

theorem chartPrimes_prime (z : ℝ) : ∀ p ∈ chartPrimes z, p.Prime := by
  intro p hp
  exact (mem_filter.mp hp).2

/-- Includes the unit, n=0 and every real cutoff endpoint. -/
theorem roughOneSlot_eq_actualRough {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    roughOneSlot z n = (actualRough (chartDivisor (chartPrimes z)) n : ℂ) := by
  have he : n.Coprime (chartDivisor (chartPrimes z)) ↔
      ∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ) := by
    rw [Nat.coprime_comm,
      chartDivisor_coprime_iff (chartPrimes z) n (chartPrimes_prime z)]
    constructor
    · intro h p hp hpn
      by_contra hn
      exact h p ((mem_chartPrimes hz p).mpr ⟨hp, le_of_not_gt hn⟩) hpn
    · intro h p hp hpn
      obtain ⟨hprime, hcap⟩ := (mem_chartPrimes hz p).mp hp
      exact (not_lt_of_ge hcap) (h p hprime hpn)
  simp only [roughOneSlot, actualRough, he]
  split_ifs <;> norm_num

theorem brun_weights (z : ℝ) (j d : ℕ) :
    |upperWeight z j d| ≤ 1 ∧ 0 ≤ gapWeight z j d ∧ gapWeight z j d ≤ 1 :=
  coefficient_bounds (chartPrimes z) (2*j) (2*j+1) d

theorem brun_support_squarefree {z : ℝ} {j d : ℕ} (hd : d ∈ brunSupport z j) :
    Squarefree d := by
  obtain ⟨S, hS, rfl⟩ := mem_image.mp hd
  have hSP := mem_powerset.mp (mem_filter.mp hS).1
  exact chartDivisor_squarefree S (fun p hp => chartPrimes_prime z p (hSP hp))

theorem upperWeight_eq_moebius {z : ℝ} {j d : ℕ} (hd : d ∈ brunSupport z j) :
    upperWeight z j d =
      if d ∈ divisorSupport (chartPrimes z) (2*j) then
        (ArithmeticFunction.moebius d : ℝ) else 0 :=
  upperCoefficient_eq_moebius_on_support (chartPrimes z) (2*j) (2*j+1) d
    (chartPrimes_prime z) hd

theorem brun_support_bounds {z : ℝ} (hz : 1 ≤ z) (j : ℕ) :
    (∀ d ∈ brunSupport z j, 0 < d ∧ (d : ℝ) ≤ z^(2*j+1)) ∧
      ((brunSupport z j).card : ℝ) ≤ z^(2*j+1) := by
  have hfloor : 1 ≤ Nat.floor z := (Nat.le_floor_iff (by linarith)).mpr hz
  have hbound := support_positive_and_cap (chartPrimes z) (2*j+1) (Nat.floor z)
    (chartPrimes_prime z) hfloor (fun p hp =>
      Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1))
  have hcast : ((Nat.floor z : ℝ)^(2*j+1)) ≤ z^(2*j+1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) _
  constructor
  · intro d hd
    exact ⟨(hbound d hd).1,
      (show (d : ℝ) ≤ (Nat.floor z : ℝ)^(2*j+1) by
        exact_mod_cast (hbound d hd).2).trans hcast⟩
  · have hc := positive_support_card_le (brunSupport z j) ((Nat.floor z)^(2*j+1))
      (fun d hd => (hbound d hd).1) (fun d hd => (hbound d hd).2)
    exact (show ((brunSupport z j).card : ℝ) ≤ (Nat.floor z : ℝ)^(2*j+1) by
      exact_mod_cast hc).trans hcast

theorem actual_brun_B1 (z : ℝ) (j n : ℕ) :
    0 ≤ upperPolynomial z j n - actualRough (chartDivisor (chartPrimes z)) n ∧
      upperPolynomial z j n - actualRough (chartDivisor (chartPrimes z)) n ≤
        gapPolynomial z j n :=
  actual_B1 j (chartPrimes z) n (chartPrimes_prime z)

theorem actual_brun_B2 (z : ℝ) (j q m : ℕ) :
    compatibleGapDensity (brunSupport z j) (gapWeight z j) q m ≤ gapDensity z j :=
  actual_B2 j (chartPrimes z) q m (chartPrimes_prime z)

theorem gapDensity_nonneg (z : ℝ) (j : ℕ) : 0 ≤ gapDensity z j := by
  unfold gapDensity brunEpsilon chartHarmonic
  positivity

/-- The exact mean is within 3 of length/q, uniformly even when q is much
larger than the interval. The comparison residue zero need not be primitive. -/
theorem normalized_coprime_count_error (L V q : ℕ) (hLV : L ≤ V) (hq : 0 < q) :
    |(part3IntervalCoprimeCount L V q : ℝ)/(q.totient : ℝ) -
      ((V-L : ℕ) : ℝ)/(q : ℝ)| ≤ 3 := by
  have hAP := part3IntervalAPCount_coprimeMean_error L V q 0 hq
  have he : part3IntervalAPCount L V q 0 = multiples L V q := by
    simp only [part3IntervalAPCount, multiples, Nat.modEq_zero_iff_dvd]
  rw [he] at hAP
  have hmul := multiples_abs_error L V q hLV hq
  have hAP' : |(part3IntervalCoprimeCount L V q : ℝ)/(q.totient : ℝ) -
      (multiples L V q : ℝ)| ≤ 2 := by
    simpa only [abs_sub_comm] using hAP
  calc
    _ = |((part3IntervalCoprimeCount L V q : ℝ)/(q.totient : ℝ) -
        (multiples L V q : ℝ)) +
        ((multiples L V q : ℝ) - ((V-L : ℕ) : ℝ)/(q : ℝ))| := by
      congr 1
      ring
    _ ≤ |(part3IntervalCoprimeCount L V q : ℝ)/(q.totient : ℝ) -
        (multiples L V q : ℝ)| +
        |(multiples L V q : ℝ) - ((V-L : ℕ) : ℝ)/(q : ℝ)| := abs_add _ _
    _ ≤ 3 := by linarith

theorem primitiveCoprimeDensity_three_totient (q : ℕ) (hq : 0 < q) :
    PrimitiveCoprimeDensity q (3*(q.totient : ℝ)) := by
  intro L V hLV
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have he : (part3IntervalCoprimeCount L V q : ℝ) -
      ((V-L : ℕ) : ℝ)*(q.totient : ℝ)/(q : ℝ) =
      ((part3IntervalCoprimeCount L V q : ℝ)/(q.totient : ℝ) -
        ((V-L : ℕ) : ℝ)/(q : ℝ))*(q.totient : ℝ) := by
    rw [sub_mul, div_mul_cancel₀ _ hphi.ne']
    ring
  rw [he, abs_mul, abs_of_pos hphi]
  exact mul_le_mul_of_nonneg_right (normalized_coprime_count_error L V q hLV hq) hphi.le

theorem uniform_meanError (q : ℕ) (hq : 0 < q) :
    meanError q (3*(q.totient : ℝ)) ≤ 4 := by
  have hphi : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hi := div_le_self (show (0 : ℝ) ≤ 1 by norm_num) hq1
  unfold meanError
  rw [mul_div_cancel_right₀ _ hphi]
  linarith

theorem exact_auxiliary_discrepancy (S : Finset ℕ) (r : ℕ → ℝ)
    (f : ℕ → ℂ) (q b : ℕ) :
    auxiliarySWError S (fun n => f n*(r n : ℂ)) 1 q b =
      discrepancy S (actualCount q b 1) (actualMean q 1) r f := by
  unfold auxiliarySWError discrepancy
  simp only [Nat.coprime_one_right_eq_true, and_true, one_mul]
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases ha : Nat.ModEq q n b <;> by_cases hc : n.Coprime q <;>
    simp [actualCount, actualMean, ha, hc] <;> push_cast <;> ring

def divisorError (L V q b d : ℕ) (f : ℕ → ℂ) : ℂ :=
  auxiliarySWError (Ico L V) (fun n => if d ∣ n then f n else 0) 1 q b

theorem divisorError_eq_atom (L V q b d : ℕ) (f : ℕ → ℂ) :
    divisorError L V q b d f =
      atom (Ico L V) divisorMask (actualCount q b 1) (actualMean q 1) f d := by
  have he : (fun n => if d ∣ n then f n else 0) =
      fun n => f n*(divisorMask d n : ℂ) := by
    funext n
    by_cases h : d ∣ n <;> simp [divisorMask, h]
  rw [divisorError, he, exact_auxiliary_discrepancy]
  rfl

/-- The positive comparison cost, with all count and exact-mean endpoint
errors paid. No assertion concerning a signed lower polynomial occurs. -/
theorem positive_gap_payment {z : ℝ} (hz : 1 ≤ z) (j L V q b : ℕ)
    (hLV : L ≤ V) (hq : 0 < q) (hb : b.Coprime q) :
    (∑ n ∈ Ico L V, gapPolynomial z j n *
      (actualCount q b 1 n + actualMean q 1 n)) ≤
      2*gapDensity z j*((V-L : ℕ) : ℝ)/(q : ℝ) + 10*z^(2*j+1) := by
  let T : ℝ := 3*(q.totient : ℝ)
  have hd := (brun_support_bounds hz j).1
  have hprim := primitiveCoprimeDensity_three_totient q hq
  have hcount (d : ℕ) (hdS : d ∈ brunSupport z j) :
      (∑ n ∈ Ico L V, (1 : ℝ)*divisorMask d n*actualCount q b 1 n) ≤
        atomMain L V q 1 d + (meanError q T+2) := by
    rw [actual_count_atom_eq]
    exact divisorAPMass_le_main L V q b 1 d T hLV (hd d hdS).1 hq hb
      (by positivity) hprim
  have hmean (d : ℕ) (hdS : d ∈ brunSupport z j) :
      (∑ n ∈ Ico L V, (1 : ℝ)*divisorMask d n*actualMean q 1 n) ≤
        atomMain L V q 1 d + meanError q T := by
    rw [actual_mean_atom_eq]
    exact divisorCoprimeMass_le_main L V q 1 d T hLV (hd d hdS).1 hq
      (by positivity) hprim
  have hgap := gap_count_mean_bound (Ico L V) (brunSupport z j) divisorMask
    (actualCount q b 1) (actualMean q 1) (fun _ => 1) (gapWeight z j)
    (atomMain L V q 1) (fun _ => meanError q T+2) (fun _ => meanError q T)
    (fun d _ => (brun_weights z j d).2.1) hcount hmean
  have hsum : (∑ d ∈ brunSupport z j, gapWeight z j d) ≤ z^(2*j+1) := by
    calc
      _ ≤ ∑ _d ∈ brunSupport z j, (1 : ℝ) :=
        sum_le_sum (fun d _ => (brun_weights z j d).2.2)
      _ = ((brunSupport z j).card : ℝ) := by simp
      _ ≤ _ := (brun_support_bounds hz j).2
  have hsplit : (∑ d ∈ brunSupport z j, gapWeight z j d *
      (2*atomMain L V q 1 d + (meanError q T+2) + meanError q T)) =
      2 * ((((V-L : ℕ) : ℝ)/(q : ℝ)) *
        compatibleGapDensity (brunSupport z j) (gapWeight z j) q 1) +
      2*(meanError q T+1)*(∑ d ∈ brunSupport z j, gapWeight z j d) := by
    rw [← gap_main_eq (brunSupport z j) (gapWeight z j) L V q 1 hq
      (fun d hdS => (hd d hdS).1)]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hdS
    ring
  simp only [one_mul] at hgap
  change (∑ n ∈ Ico L V, gapPolynomial z j n *
    (actualCount q b 1 n + actualMean q 1 n)) ≤ _ at hgap
  rw [hsplit] at hgap
  have hmain := mul_le_mul_of_nonneg_left (actual_brun_B2 z j q 1)
    (show 0 ≤ 2*(((V-L : ℕ) : ℝ)/(q : ℝ)) by positivity)
  have hrem : 2*(meanError q T+1)*(∑ d ∈ brunSupport z j, gapWeight z j d) ≤
      10*z^(2*j+1) := by
    calc
      _ ≤ 2*(meanError q T+1)*z^(2*j+1) :=
        mul_le_mul_of_nonneg_left hsum (by
          have := meanError_nonneg q T (by positivity)
          positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by have := uniform_meanError q hq; change meanError q T ≤ 4 at this; linarith)
        (pow_nonneg (by linarith) _)
  nlinarith [hgap, hmain, hrem]

/-- Reusable signed comparison for the original Mobius slot. Every divisor
atom has the same exact mean 1/phi(q). The right-hand atoms are COMPUTED
errors, not an assumed estimate, and the gap cost is already proved. -/
theorem signed_rough_brun_comparison {z : ℝ} (hz : 1 ≤ z)
    (j L V q b : ℕ) (f : ℕ → ℂ) (hLV : L ≤ V) (hq : 0 < q)
    (hb : b.Coprime q) (hf : ∀ n ∈ Ico L V, ‖f n‖ ≤ 1) :
    ‖auxiliarySWError (Ico L V) (fun n => f n*roughOneSlot z n) 1 q b‖ ≤
      ‖∑ d ∈ brunSupport z j, (upperWeight z j d : ℂ)*divisorError L V q b d f‖ +
        2*gapDensity z j*((V-L : ℕ) : ℝ)/(q : ℝ) + 10*z^(2*j+1) := by
  simp_rw [roughOneSlot_eq_actualRough (show 0 ≤ z by linarith)]
  rw [exact_auxiliary_discrepancy]
  have h := rough_to_upper (Ico L V) (actualCount q b 1) (actualMean q 1)
    (actualRough (chartDivisor (chartPrimes z))) (upperPolynomial z j)
    (gapPolynomial z j) (fun _ => 1) f
    (by intro n hn; unfold actualCount; split_ifs <;> norm_num)
    (by intro n hn; unfold actualMean; split_ifs <;> positivity)
    hf (fun n _ => (actual_brun_B1 z j n).1) (fun n _ => (actual_brun_B1 z j n).2)
  simp only [one_mul] at h
  change _ ≤ ‖discrepancy (Ico L V) (actualCount q b 1) (actualMean q 1)
    (polynomial (brunSupport z j) divisorMask (upperWeight z j)) f‖ + _ at h
  rw [discrepancy_polynomial] at h
  simp_rw [← divisorError_eq_atom] at h
  exact h.trans (by
    have hp := positive_gap_payment hz j L V q b hLV hq hb
    linarith)

/-- Genuine finite rough-one cancellation, uniform in all positive q. -/
theorem roughOne_interval_bound {z : ℝ} (hz : 1 ≤ z) (j L V q b : ℕ)
    (hLV : L ≤ V) (hq : 0 < q) (hb : b.Coprime q) :
    ‖auxiliarySWError (Ico L V) (roughOneSlot z) 1 q b‖ ≤
      12*z^(2*j+1) + 2*gapDensity z j*((V-L : ℕ) : ℝ)/(q : ℝ) := by
  have h := signed_rough_brun_comparison hz j L V q b (fun _ => 1)
    hLV hq hb (by intro n hn; simp)
  simp only [one_mul] at h
  have hatom (d : ℕ) (hd : d ∈ brunSupport z j) :
      ‖divisorError L V q b d (fun _ => 1)‖ ≤ 2 := by
    rw [divisorError_eq_atom, actual_discrepancy_atom_eq,
      Complex.norm_real, Real.norm_eq_abs]
    exact divisorRemainder_abs_le_two L V q b 1 d
      ((brun_support_bounds hz j).1 d hd).1 hq hb
  have hu : ‖∑ d ∈ brunSupport z j,
      (upperWeight z j d : ℂ)*divisorError L V q b d (fun _ => 1)‖ ≤
      2*z^(2*j+1) := by
    calc
      _ ≤ ∑ d ∈ brunSupport z j,
          ‖(upperWeight z j d : ℂ)*divisorError L V q b d (fun _ => 1)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _d ∈ brunSupport z j, (2 : ℝ) := by
        apply sum_le_sum
        intro d hd
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_mul (brun_weights z j d).1 (hatom d hd)
          (norm_nonneg _) zero_le_one).trans_eq (by ring)
      _ = 2*((brunSupport z j).card : ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (brun_support_bounds hz j).2 (by norm_num)
  linarith

/-- A universal large-q bound with an absolute endpoint cost and the exact
coprime mean. It has no log(height), upper scale bound or primitive-residue
requirement. Useful for the separate signed Mobius supplier. -/
theorem oneBounded_interval_large_modulus (L V q b : ℕ) (f : ℕ → ℂ)
    (hLV : L ≤ V) (hq : 0 < q) (hf : ∀ n ∈ Ico L V, ‖f n‖ ≤ 1) :
    ‖auxiliarySWError (Ico L V) f 1 q b‖ ≤
      2*((V-L : ℕ) : ℝ)/(q : ℝ)+6 := by
  have hAP : (part3IntervalAPCount L V q b : ℝ) ≤
      ((V-L : ℕ) : ℝ)/(q : ℝ)+3 := by
    have hr := (abs_le.mp (part3IntervalAPCount_abs_sub_le_two L V q b 0 hq)).2
    have he : part3IntervalAPCount L V q 0 = multiples L V q := by
      simp only [part3IntervalAPCount, multiples, Nat.modEq_zero_iff_dvd]
    rw [he] at hr
    have hm := (abs_le.mp (multiples_abs_error L V q hLV hq)).2
    linarith
  have hmean := (abs_le.mp (normalized_coprime_count_error L V q hLV hq)).2
  have hcountNorm : ‖∑ n ∈ Ico L V, if Nat.ModEq q n b then f n else 0‖ ≤
      (part3IntervalAPCount L V q b : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Ico L V, ‖if Nat.ModEq q n b then f n else 0‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Ico L V, if Nat.ModEq q n b then (1 : ℝ) else 0 := by
        apply sum_le_sum
        intro n hn
        by_cases h : Nat.ModEq q n b
        · simpa only [h, ite_true] using hf n hn
        · simp [h]
      _ = _ := by simp [part3IntervalAPCount]
  have hcopNorm : ‖∑ n ∈ Ico L V, if n.Coprime q then f n else 0‖ ≤
      (part3IntervalCoprimeCount L V q : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Ico L V, ‖if n.Coprime q then f n else 0‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Ico L V, if n.Coprime q then (1 : ℝ) else 0 := by
        apply sum_le_sum
        intro n hn
        by_cases h : n.Coprime q
        · simpa only [h, ite_true] using hf n hn
        · simp [h]
      _ = _ := by simp [part3IntervalCoprimeCount, Nat.coprime_comm]
  have hnorm := norm_sub_le
    (∑ n ∈ Ico L V, if Nat.ModEq q n b then f n else 0)
    ((∑ n ∈ Ico L V, if n.Coprime q then f n else 0)/(q.totient : ℂ))
  rw [norm_div, Complex.norm_natCast] at hnorm
  have hcop := div_le_div_of_nonneg_right hcopNorm (Nat.cast_nonneg q.totient)
  simp only [auxiliarySWError, Nat.coprime_one_right_eq_true, and_true, one_mul]
  linarith

end
end ImbalancedChen.P5Z.ActualHBRoughBrunFinite
