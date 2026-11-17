import ImbalancedChen.ChenInitialPrimeSource
import ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
New work beyond the N < 2*d prime switch: for EVEN centre N the
ORIGINAL receiver is coprime to N, so a possible quotient 2 is excluded.
Consequently every complete modulus d with N < 3*d has an EXACT
singleton/empty fibre. This captures the additional N/3 < d <= N/2
band without claiming its signed contribution is small.

The physical theorem uses the pre-existing actualSmallRoughModuli
and actualSmallRoughRho with a fixed supplied policy. It does not
recompute a policy, change beta, insert a new mask or apply external PP.
The remaining N^theta < d <= N/3 and the switched prime sum are unpaid.
-/

namespace ImbalancedChen.P4AOriginalFull87EvenUpperThird
noncomputable section
open scoped Classical BigOperators

/-- In an even centre, quotient 2 is impossible for a genuine receiver:
the quotient would divide both the receiver and the centre. -/
private theorem even_receiver_quotient_not_two
    (N d n : ℕ) (hEven : Even N)
    (hn : n ∈ chenPrimeReceiverSource N)
    (hdiv : d ∣ n) : n / d ≠ 2 := by
  intro hk
  have hmul : n / d * d = n := Nat.div_mul_cancel hdiv
  have htwo : 2 ∣ n := by
    refine ⟨d, ?_⟩
    calc
      n = (n / d) * d := hmul.symm
      _ = 2 * d := by rw [hk]
  have hcop : Nat.Coprime n N := (chenPrimeReceiverSource_data hn).2.2
  have htwoCop : Nat.Coprime 2 N := hcop.of_dvd_left htwo
  exact (Nat.prime_two.coprime_iff_not_dvd.mp htwoCop)
    (even_iff_two_dvd.mp hEven)

/-- For even N the actual upper-third receiver fibre has at most
one positive element. This is a full-modulus statement: d is not
replaced by its rough factor, and N=3*d stays outside the window. -/
theorem even_receiver_upper_third_dvd_eq
    (N d n : ℕ) (hEven : Even N)
    (hthird : N < 3 * d)
    (hn : n ∈ chenPrimeReceiverSource N)
    (hdiv : d ∣ n) : n = d := by
  obtain ⟨hnpos, hnle, _⟩ := chenPrimeReceiverSource_data hn
  have hmul : n / d * d = n := Nat.div_mul_cancel hdiv
  have hkpos : 0 < n / d := by
    by_contra hnot
    have hkzero : n / d = 0 := Nat.eq_zero_of_not_pos hnot
    have hzero : n = 0 := by simpa [hkzero] using hmul.symm
    omega
  have hklt : n / d < 3 := by
    by_contra hnot
    have hge : 3 ≤ n / d := by omega
    have htwod : 3 * d ≤ n := by
      calc
        3 * d ≤ (n / d) * d := Nat.mul_le_mul_right d hge
        _ = n := hmul
    omega
  have hknot2 : n / d ≠ 2 :=
    even_receiver_quotient_not_two N d n hEven hn hdiv
  have hkone : n / d = 1 := by omega
  calc
    n = (n / d) * d := hmul.symm
    _ = d := by simp [hkone]

/-- Exact ORIGINAL finite receiver fibre in the strictly enlarged window. -/
theorem even_receiver_upper_third_fibre
    (N d : ℕ) (hEven : Even N) (hthird : N < 3 * d) :
    (chenPrimeReceiverSource N).filter (fun n => d ∣ n) =
      if d ∈ chenPrimeReceiverSource N then {d} else ∅ := by
  classical
  let R := chenPrimeReceiverSource N
  change R.filter (fun n => d ∣ n) = if d ∈ R then {d} else ∅
  by_cases hmem : d ∈ R
  · have hf : R.filter (fun n => d ∣ n) = {d} := by
      ext n
      constructor
      · intro hn
        have heq : n = d := even_receiver_upper_third_dvd_eq
          N d n hEven hthird
          (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
        exact Finset.mem_singleton.mpr heq
      · intro hn
        have heq : n = d := Finset.mem_singleton.mp hn
        subst n
        exact Finset.mem_filter.mpr ⟨hmem, dvd_rfl⟩
    simp [hmem, hf]
  · have hf : R.filter (fun n => d ∣ n) = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro n hn
      obtain ⟨hsrc, hdiv⟩ := Finset.mem_filter.mp hn
      have heq : n = d :=
        even_receiver_upper_third_dvd_eq N d n hEven hthird hsrc hdiv
      exact hmem (heq ▸ hsrc)
    simp [hmem, hf]

/-- No approximate density and no separate primitive error in this band. -/
theorem even_receiver_upper_third_indicator
    (N d : ℕ) (hEven : Even N) (hthird : N < 3 * d) :
    (((chenPrimeReceiverSource N).filter (fun n => d ∣ n)).card : ℝ) =
      if d ∈ chenPrimeReceiverSource N then 1 else 0 := by
  classical
  rw [even_receiver_upper_third_fibre N d hEven hthird]
  split_ifs <;> simp

/-- Exact switch from complete moduli to the ORIGINAL prime carrier.
Signs and original source membership are retained. No o(H_N) estimate. -/
theorem even_upper_third_modulus_prime_switch
    (N X : ℕ) (hEven : Even N)
    (S : Finset ℕ) (weight : ℕ → ℝ) :
    (∑ d ∈ S,
      if N < 3 * d ∧ X < d then
        weight d *
          (((chenPrimeReceiverSource N).filter (fun n => d ∣ n)).card : ℝ)
      else 0) =
      ∑ P ∈ chenAdditivePrimeCarrier N,
        if N - P ∈ S ∧ N < 3 * (N - P) ∧ X < N - P then
          weight (N - P)
        else 0 := by
  classical
  let R := chenPrimeReceiverSource N
  have hpoint (d : ℕ) :
      (if N < 3 * d ∧ X < d then
        weight d *
          (((chenPrimeReceiverSource N).filter (fun n => d ∣ n)).card : ℝ)
       else 0) =
      (if d ∈ R ∧ N < 3 * d ∧ X < d then weight d else 0) := by
    by_cases hw : N < 3 * d ∧ X < d
    · have hind := even_receiver_upper_third_indicator N d hEven hw.1
      by_cases hm : d ∈ R
      · simp [hw, hm, R, hind]
      · simp [hw, hm, R, hind]
    · have hn : ¬ (d ∈ R ∧ N < 3 * d ∧ X < d) := by tauto
      simp [hw, hn]
  calc
    (∑ d ∈ S,
      if N < 3 * d ∧ X < d then
        weight d *
          (((chenPrimeReceiverSource N).filter (fun n => d ∣ n)).card : ℝ)
      else 0) =
      ∑ d ∈ S, if d ∈ R ∧ N < 3 * d ∧ X < d then weight d else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        exact hpoint d
    _ = ∑ d ∈ S.filter (fun d => d ∈ R ∧ N < 3 * d ∧ X < d),
          weight d := by rw [Finset.sum_filter]
    _ = ∑ d ∈ R.filter (fun d => d ∈ S ∧ N < 3 * d ∧ X < d),
          weight d := by
        congr 1
        ext d
        simp only [Finset.mem_filter]
        tauto
    _ = ∑ d ∈ R,
          if d ∈ S ∧ N < 3 * d ∧ X < d then weight d else 0 := by
        rw [Finset.sum_filter]
    _ = ∑ P ∈ chenAdditivePrimeCarrier N,
          if N - P ∈ S ∧ N < 3 * (N - P) ∧ X < N - P then
            weight (N - P)
          else 0 := by
        simpa only [R] using
          (sum_chenPrimeReceiverSource N
            (fun d => if d ∈ S ∧ N < 3 * d ∧ X < d
              then weight d else 0))

/-- The actual unchanged finite physical modulus and beta/rough coefficient
at a fixed supplied original policy; this is the extension of the previously
switched N/2<d window to N/3<d. No new sieve coefficient is defined. -/
theorem actual_even_physical_upper_third_prime_switch
    (policy : Bool → List ℕ → Bool)
    (N cap X : ℕ) (w z L : ℝ) (hEven : Even N) :
    (∑ d ∈ actualSmallRoughModuli (policy false) N cap w z,
      if N < 3 * d ∧ X < d then
        actualSmallRoughRho (policy false) N cap w z L d *
          (((chenPrimeReceiverSource N).filter (fun n => d ∣ n)).card : ℝ)
      else 0) =
      ∑ P ∈ chenAdditivePrimeCarrier N,
        if N - P ∈ actualSmallRoughModuli (policy false) N cap w z ∧
            N < 3 * (N - P) ∧ X < N - P then
          actualSmallRoughRho (policy false) N cap w z L (N - P)
        else 0 := by
  exact even_upper_third_modulus_prime_switch N X hEven
    (actualSmallRoughModuli (policy false) N cap w z)
    (actualSmallRoughRho (policy false) N cap w z L)

/-- The newly added N/3<d<=N/2 slice, distinct from the prior upper-half.
The complementary N/3 boundary (3*d=N) is NOT silently removed. -/
theorem actual_even_physical_new_third_to_half_prime_switch
    (policy : Bool → List ℕ → Bool)
    (N cap X : ℕ) (w z L : ℝ) (hEven : Even N) :
    (∑ d ∈ actualSmallRoughModuli (policy false) N cap w z,
      if N < 3 * d ∧ X < d then
        (if 2 * d ≤ N then
          actualSmallRoughRho (policy false) N cap w z L d else 0) *
          (((chenPrimeReceiverSource N).filter (fun n => d ∣ n)).card : ℝ)
      else 0) =
      ∑ P ∈ chenAdditivePrimeCarrier N,
        if N - P ∈ actualSmallRoughModuli (policy false) N cap w z ∧
            N < 3 * (N - P) ∧ X < N - P then
          (if 2 * (N - P) ≤ N then
            actualSmallRoughRho (policy false) N cap w z L (N - P) else 0)
        else 0 := by
  exact even_upper_third_modulus_prime_switch N X hEven
    (actualSmallRoughModuli (policy false) N cap w z)
    (fun d => if 2 * d ≤ N then
      actualSmallRoughRho (policy false) N cap w z L d else 0)

end
end ImbalancedChen.P4AOriginalFull87EvenUpperThird
