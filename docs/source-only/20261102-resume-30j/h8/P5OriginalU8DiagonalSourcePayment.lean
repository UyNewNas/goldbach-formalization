import ImbalancedChen.P5zUpsilon8OriginalSlot
import ImbalancedChen.P5OriginalPrimeEndpointDivisors
import ImbalancedChen.Part3PolynomialResidueDivisorBound
import ImbalancedChen.TotientReciprocalBudget
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED. The repeated terminal prime q=p2 is paid in
the actual signed U8 source discrepancy, before any PP theorem is used.
All original pair bands, centre masks, labels and the same physical rho
are retained. The strict rank-three source still needs its analytic PP
supplier. No adopted integral endpoint or h8 estimate is assumed here.
-/

namespace ImbalancedChen.P5OriginalU8DiagonalSourcePayment

noncomputable section
open Filter Topology
open scoped BigOperators
open Classical
open P5U8SharpKSource

/-- A label-preserving divisor estimate. Products need not be injective. -/
theorem labelled_error_le_divisors {α : Type*} (S : Finset α) (f : α → ℕ)
    (N D : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hsource : ∀ t ∈ S, f t < N)
    (hQ : Q ⊆ Finset.Icc 1 D) (hrho : ∀ q ∈ Q, |rho q| ≤ 1) :
    |p5z_labelledDistributionError S f (fun _ => 1) N Q rho| ≤
      (∑ t ∈ S, ((N - f t).divisors.card : ℝ)) +
        (S.card : ℝ) * (4 * (1 + Real.log (max 1 (D : ℝ)))) := by
  have hcong :
      |∑ q ∈ Q, rho q * p5z_labelledCongruenceMass S f (fun _ => 1) N q| ≤
        ∑ t ∈ S, ((N - f t).divisors.card : ℝ) := by
    have heq :
        (∑ q ∈ Q, rho q * p5z_labelledCongruenceMass S f (fun _ => 1) N q) =
          ∑ t ∈ S, ∑ q ∈ Q with Nat.ModEq q (f t) N, rho q := by
      simp only [p5z_labelledCongruenceMass, Finset.mul_sum, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro q hq
      by_cases h : Nat.ModEq q (f t) N <;> simp [h]
    rw [heq]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro t ht
    have hd := P5OriginalPrimeEndpoint.sum_abs_rho_congruence_le_divisors
      Q rho N (f t) (ne_of_lt (hsource t ht)) hrho
    have hdist : P5OriginalPrimeEndpoint.distance N (f t) = N - f t := by
      simp only [P5OriginalPrimeEndpoint.distance, if_pos (hsource t ht).le]
    rw [hdist] at hd
    exact (Finset.abs_sum_le_sum_abs _ _).trans hd
  have hmean :
      |∑ q ∈ Q, rho q *
        (p5z_labelledCoprimeMass S f (fun _ => 1) q / (Nat.totient q : ℝ))| ≤
          (S.card : ℝ) * (4 * (1 + Real.log (max 1 (D : ℝ)))) := by
    have hm (q : ℕ) :
        |p5z_labelledCoprimeMass S f (fun _ => 1) q| ≤ (S.card : ℝ) := by
      have hcount : p5z_labelledCoprimeMass S f (fun _ => 1) q =
          ((S.filter (fun t => Nat.Coprime (f t) q)).card : ℝ) := by
        simp only [p5z_labelledCoprimeMass, ← Finset.sum_filter]
        simp
      rw [hcount, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    calc
      _ ≤ ∑ q ∈ Q, |rho q *
          (p5z_labelledCoprimeMass S f (fun _ => 1) q / (Nat.totient q : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ Q, (S.card : ℝ) * (1 / (Nat.totient q : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        rw [abs_mul, abs_div, abs_of_nonneg (Nat.cast_nonneg _)]
        calc
          _ ≤ 1 * ((S.card : ℝ) / (Nat.totient q : ℝ)) :=
            mul_le_mul (hrho q hq)
              (div_le_div_of_nonneg_right (hm q) (Nat.cast_nonneg _))
              (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) zero_le_one
          _ = _ := by ring
      _ = (S.card : ℝ) * ∑ q ∈ Q, 1 / (Nat.totient q : ℝ) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_reciprocal_totient_subset_le_log Q D hQ) (Nat.cast_nonneg _)
  have heq : p5z_labelledDistributionError S f (fun _ => 1) N Q rho =
      (∑ q ∈ Q, rho q * p5z_labelledCongruenceMass S f (fun _ => 1) N q) -
        ∑ q ∈ Q, rho q *
          (p5z_labelledCoprimeMass S f (fun _ => 1) q / (Nat.totient q : ℝ)) := by
    simp only [p5z_labelledDistributionError, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add hcong hmean)

/-- Exact signed split at the original inclusive q=p2 wall. -/
theorem physicalPP_eq_strict_add_diagonal (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 3 N N Q rho (physicalWeight N) =
      p5z_labelledDistributionError (strictTriples N) product (fun _ => 1) N Q rho +
      p5z_labelledDistributionError (diagonalTriples N) product (fun _ => 1) N Q rho := by
  rw [← distribution_eq_physicalPP]
  have hsplit (F : Triple → ℝ) :
      (∑ t ∈ arithmeticTriples N, F t) =
        (∑ t ∈ strictTriples N, F t) + ∑ t ∈ diagonalTriples N, F t := by
    simp only [strictTriples, diagonalTriples, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have horder := (arithmetic_sorted ht).2
    by_cases heq : t.2 = t.1.2
    · have hnot : ¬ t.1.2 < t.2 := by omega
      simp only [if_neg hnot, if_pos heq, zero_add]
    · have hlt : t.1.2 < t.2 := by omega
      simp only [if_pos hlt, if_neg heq, add_zero]
  unfold p5z_labelledDistributionError p5z_labelledCongruenceMass p5z_labelledCoprimeMass
  simp_rw [hsplit]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- The true diagonal signed PP cost is O(N^(3/4)), uniformly over all
one-bounded coefficients of any fixed polynomial scope. The modulus
scope enters only the constant; no diagonal distribution input occurs. -/
theorem diagonal_error_uniform_power (scopeNu : ℝ) (hscopeNu : 0 ≤ scopeNu) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ D : ℕ, ∀ Q : Finset ℕ,
      ∀ rho : ℕ → ℝ, Q ⊆ Finset.Icc 1 D → (D : ℝ) ≤ (N : ℝ) ^ scopeNu →
      (∀ q ∈ Q, |rho q| ≤ 1) →
      |p5z_labelledDistributionError (diagonalTriples N) product (fun _ => 1) N Q rho| ≤
        C * (N : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨C, hC, htau⟩ := Part3.PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) (show (0 : ℝ) < 1 / 12 by norm_num)
  refine ⟨C + 4 + 48 * scopeNu, by positivity, ?_⟩
  intro N hN D Q rho hQ hD hrho
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have ht (t : Triple) (ht : t ∈ diagonalTriples N) : product t < N :=
    arithmetic_product_lt (Finset.mem_filter.mp ht).1
  have hdiv (t : Triple) (hmem : t ∈ diagonalTriples N) :
      ((N - product t).divisors.card : ℝ) ≤ C * (N : ℝ) ^ (1 / 12 : ℝ) := by
    have hp : 0 < N - product t := Nat.sub_pos_of_lt (ht t hmem)
    have hb : ((N - product t).divisors.card : ℝ) ≤
        C * ((N - product t : ℕ) : ℝ) ^ (1 / 12 : ℝ) := by
      simpa only [MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.fouvryTau_two]
        using htau (N - product t) hp
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.sub_le N (product t)) (by norm_num)) hC.le)
  have hmax : max (1 : ℝ) (D : ℝ) ≤ (N : ℝ) ^ scopeNu :=
    max_le (Real.one_le_rpow hN1 hscopeNu) hD
  have hlogD : Real.log (max 1 (D : ℝ)) ≤ scopeNu * Real.log (N : ℝ) := by
    have h := Real.log_le_log (zero_lt_one.trans_le (le_max_left _ _)) hmax
    rwa [Real.log_rpow hNpos] at h
  have hlogN : Real.log (N : ℝ) ≤ 12 * (N : ℝ) ^ (1 / 12 : ℝ) := by
    have h := Real.log_le_rpow_div hNpos.le (show (0 : ℝ) < 1 / 12 by norm_num)
    norm_num at h ⊢
    linarith only [h]
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 12 : ℝ) :=
    Real.one_le_rpow hN1 (by norm_num)
  have hlog : 4 * (1 + Real.log (max 1 (D : ℝ))) ≤
      (4 + 48 * scopeNu) * (N : ℝ) ^ (1 / 12 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlogN hscopeNu
    nlinarith only [hlogD, hmul, hone]
  have hfinite := labelled_error_le_divisors (diagonalTriples N) product N D Q rho ht hQ hrho
  have hsum : (∑ t ∈ diagonalTriples N, ((N - product t).divisors.card : ℝ)) ≤
      ((diagonalTriples N).card : ℝ) * (C * (N : ℝ) ^ (1 / 12 : ℝ)) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hdiv
  calc
    _ ≤ ((diagonalTriples N).card : ℝ) *
        ((C + 4 + 48 * scopeNu) * (N : ℝ) ^ (1 / 12 : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (diagonalTriples N).card)
      nlinarith only [hfinite, hsum, hm]
    _ ≤ (N : ℝ) ^ (2 / 3 : ℝ) *
        ((C + 4 + 48 * scopeNu) * (N : ℝ) ^ (1 / 12 : ℝ)) :=
      mul_le_mul_of_nonneg_right (diagonal_card_le_power (by omega)) (by positivity)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add hNpos]
      norm_num

/-- Fixed-power error is below the very log-cube scale demanded by h8. -/
theorem eventually_power_three_quarters_le_logCube (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) ^ (3 / 4 : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) ^ 3 := by
  have hlim : Tendsto (fun N : ℕ =>
      C * (Real.log (N : ℝ) ^ 3 / (N : ℝ) ^ (1 / 4 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_nat_log_pow_div_rpow 3 (show (0 : ℝ) < 1 / 4 by norm_num)).const_mul C
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (2 : ℕ)] with N hsmall hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpow : (N : ℝ) ^ (3 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) = N := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hsmall' : C * Real.log (N : ℝ) ^ 3 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    have hratio : C * Real.log (N : ℝ) ^ 3 / (N : ℝ) ^ (1 / 4 : ℝ) ≤ 1 := by
      simpa only [mul_div_assoc] using hsmall.le
    simpa only [one_mul] using
      (div_le_iff₀ (Real.rpow_pos_of_pos hNpos (1 / 4))).mp hratio
  apply (le_div_iff₀ (pow_pos hlog 3)).mpr
  have hmul := mul_le_mul_of_nonneg_left hsmall'
    (Real.rpow_nonneg hNpos.le (3 / 4))
  nlinarith only [hmul, hpow]

/-- The actual attached rho pays the diagonal uniformly, with all
zero coefficients removed by an exact identity. Scope is the original
nonzero-coefficient scope and no new policy licence is imposed. -/
theorem eventually_actual_diagonal_le_logCube
    (nu r e scopeNu : ℝ) (hscopeNu : 0 ≤ scopeNu)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (Licensed : ℕ → Prop)
    (hscope : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → ∀ d : ℕ,
      d ∈ attachedUpperModuli nu r e retain cap N →
      attachedUpperCoefficient nu r e retain cap N d ≠ 0 → (d : ℝ) ≤ (N : ℝ) ^ scopeNu) :
    ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      |p5z_labelledDistributionError (diagonalTriples N) product (fun _ => 1) N
        (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N)| ≤
          (N : ℝ) / Real.log (N : ℝ) ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := diagonal_error_uniform_power scopeNu hscopeNu
  filter_upwards [hscope, eventually_power_three_quarters_le_logCube C,
    eventually_ge_atTop (2 : ℕ)] with N hscopeN hpay hN
  intro hEven hL
  let Q := attachedUpperModuli nu r e retain cap N
  let rho := attachedUpperCoefficient nu r e retain cap N
  let A := p5z_activeModuli Q rho
  have hactive : p5z_labelledDistributionError (diagonalTriples N) product (fun _ => 1)
      N A rho = p5z_labelledDistributionError (diagonalTriples N) product (fun _ => 1)
        N Q rho := p5z_active_sum_rho_mul Q rho _
  have hA : A ⊆ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ scopeNu)) := by
    intro d hd
    obtain ⟨hdQ, hdne⟩ := Finset.mem_filter.mp hd
    have hsf := actualSmallRoughModuli_squarefree (retain N) N (cap N) _ _ hdQ
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hsf.ne_zero,
      Nat.le_floor (hscopeN hEven hL d hdQ hdne)⟩
  rw [← hactive]
  exact (hbound N hN _ A rho hA
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    (fun d _ => actualSmallRoughRho_abs_le_one (retain N) N (cap N) _ _ _ d)).trans hpay

/-- The remaining source supplier needs only the strict original triples.
The q=p2 part of the physical PP premise is now proved internally. -/
theorem actual_physicalPP_of_strict_source
    (nu r e scopeNu : ℝ) (hscopeNu : 0 ≤ scopeNu)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (Licensed : ℕ → Prop)
    (hscope : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → ∀ d : ℕ,
      d ∈ attachedUpperModuli nu r e retain cap N →
      attachedUpperCoefficient nu r e retain cap N d ≠ 0 → (d : ℝ) ≤ (N : ℝ) ^ scopeNu)
    (hstrict : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      |p5z_labelledDistributionError (strictTriples N) product (fun _ => 1) N
        (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N)| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N) (physicalWeight N)| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ 3 := by
  obtain ⟨C, hC, hstrict⟩ := hstrict
  refine ⟨C + 1, by positivity, ?_⟩
  filter_upwards [hstrict, eventually_actual_diagonal_le_logCube nu r e scopeNu
    hscopeNu retain cap Licensed hscope] with N hs hd
  intro hEven hL
  rw [physicalPP_eq_strict_add_diagonal]
  refine (abs_add _ _).trans ?_
  have h := add_le_add (hs hEven hL) (hd hEven hL)
  convert h using 1 <;> ring

end
end ImbalancedChen.P5OriginalU8DiagonalSourcePayment
