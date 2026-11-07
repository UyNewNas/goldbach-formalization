import ImbalancedChen.ActualSelbergCoefficients
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact main term of the explicit finite Selberg coefficients

The standard finite coefficients from `ActualSelbergCoefficients` attain
the exact main term `1 / finiteSelbergNormalizer s L`. The transformed
coefficients are calculated here by a finite bijection and Möbius
cancellation, then substituted into mathlib's proved diagonalization.

Neither the transformed identity nor the main-term evaluation is a
hypothesis. No asymptotic estimate of the normalizer is claimed.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Multiplication by `d` identifies its coprime tail with the allowed
multiples of `d`. Squarefreeness supplies coprimality in the inverse map. -/
theorem finiteSelberg_mul_coprimeSum_eq_sum_multiples
    (s : BoundingSieve) (L : ℕ) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    s.selbergTerms d * finiteSelbergCoprimeSum s L d =
      ∑ v ∈ s.prodPrimes.divisors with d ∣ v ∧ v ≤ L,
        s.selbergTerms v := by
  classical
  have hP : s.prodPrimes ≠ 0 := BoundingSieve.prodPrimes_ne_zero (s := s)
  have hdpos : 0 < d := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hd, hP⟩)
  unfold finiteSelbergCoprimeSum
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun j _ => d * j) ?_ ?_ ?_ ?_
  · intro j hj
    obtain ⟨hjP, hjcop, hjL⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr
        ⟨hjcop.symm.mul_dvd_of_dvd_of_dvd hd (Nat.dvd_of_mem_divisors hjP), hP⟩,
        ⟨dvd_mul_right d j, hjL⟩⟩
  · intro a _ha b _hb hab
    exact Nat.eq_of_mul_eq_mul_left hdpos hab
  · intro v hv
    obtain ⟨hvP, hdv, hvL⟩ := Finset.mem_filter.mp hv
    obtain ⟨j, rfl⟩ := hdv
    have hprod : d * j ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hvP
    have hjP : j ∣ s.prodPrimes :=
      (show j ∣ d * j from ⟨d, Nat.mul_comm d j⟩).trans hprod
    have hcop : Nat.Coprime j d :=
      (Nat.coprime_of_squarefree_mul
        (BoundingSieve.squarefree_of_dvd_prodPrimes (s := s) hprod)).symm
    exact ⟨j, Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hjP, hP⟩, hcop, hvL⟩, rfl⟩
  · intro j hj
    exact ((BoundingSieve.selbergTerms_isMultiplicative (s := s)).map_mul_of_coprime
      (Finset.mem_filter.mp hj).2.1.symm).symm

/-- Multiplying the actual coefficient by the density cancels its local
denominator. The formula remains exact beyond the cutoff, where its
multiple sum is empty. -/
theorem nu_mul_finiteSelbergWeight_eq_sum_multiples
    (s : BoundingSieve) (L : ℕ) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    s.nu d * finiteSelbergWeight s L d =
      (ArithmeticFunction.moebius d : ℝ) *
        (∑ v ∈ s.prodPrimes.divisors with d ∣ v ∧ v ≤ L,
          s.selbergTerms v) / finiteSelbergNormalizer s L := by
  classical
  by_cases hdL : d ≤ L
  · rw [finiteSelbergWeight, if_pos ⟨hd, hdL⟩,
      ← finiteSelberg_mul_coprimeSum_eq_sum_multiples s L hd]
    have hnu : s.nu d ≠ 0 := BoundingSieve.nu_ne_zero (s := s) hd
    simp only [div_eq_mul_inv]
    calc
      _ = (s.nu d * (s.nu d)⁻¹) *
          ((ArithmeticFunction.moebius d : ℝ) * s.selbergTerms d *
            finiteSelbergCoprimeSum s L d * (finiteSelbergNormalizer s L)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hnu, one_mul]; ring
  · have hsum : (∑ v ∈ s.prodPrimes.divisors with d ∣ v ∧ v ≤ L,
        s.selbergTerms v) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      obtain ⟨hvP, hdv, hvL⟩ := Finset.mem_filter.mp hv
      exact False.elim (hdL ((Nat.le_of_dvd (Nat.pos_of_mem_divisors hvP) hdv).trans hvL))
    simp [finiteSelbergWeight, hdL, hsum]

/-- On the squarefree divisor lattice, the sum of Möbius values over an
upper interval cancels unless that interval contains only its endpoint. -/
private theorem moebius_upper_divisor_sum
    {v m : ℕ} (hv : Squarefree v) :
    (∑ d ∈ v.divisors with m ∣ d,
      (ArithmeticFunction.moebius d : ℝ)) =
      if v = m then (ArithmeticFunction.moebius m : ℝ) else 0 := by
  classical
  have hdivsum (n : ℕ) :
      (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) =
        if n = 1 then 1 else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
    simpa only [ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply] using h
  by_cases hmv : m ∣ v
  · rcases hmv with ⟨k, rfl⟩
    have hm0 : m ≠ 0 := left_ne_zero_of_mul hv.ne_zero
    have hk0 : k ≠ 0 := right_ne_zero_of_mul hv.ne_zero
    have hbij :
        (∑ t ∈ k.divisors, (ArithmeticFunction.moebius (m * t) : ℝ)) =
          ∑ d ∈ (m * k).divisors with m ∣ d,
            (ArithmeticFunction.moebius d : ℝ) := by
      refine Finset.sum_bij (fun t _ => m * t) ?_ ?_ ?_ ?_
      · intro t ht
        refine Finset.mem_filter.mpr ⟨?_, ⟨t, rfl⟩⟩
        exact Nat.mem_divisors.mpr
          ⟨mul_dvd_mul (dvd_refl m) (Nat.dvd_of_mem_divisors ht), hv.ne_zero⟩
      · intro a _ha b _hb hab
        exact mul_left_cancel₀ hm0 hab
      · intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hd, hmd⟩
        rcases hmd with ⟨t, rfl⟩
        rcases Nat.dvd_of_mem_divisors hd with ⟨r, hr⟩
        have ht : t ∣ k := by
          refine ⟨r, ?_⟩
          apply mul_left_cancel₀ hm0
          simpa only [mul_assoc] using hr
        exact ⟨t, Nat.mem_divisors.mpr ⟨ht, hk0⟩, rfl⟩
      · intro t _ht
        rfl
    calc
      (∑ d ∈ (m * k).divisors with m ∣ d,
          (ArithmeticFunction.moebius d : ℝ)) =
          ∑ t ∈ k.divisors,
            (ArithmeticFunction.moebius (m * t) : ℝ) := hbij.symm
      _ = (ArithmeticFunction.moebius m : ℝ) *
          (∑ t ∈ k.divisors,
            (ArithmeticFunction.moebius t : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro t ht
        have hmt : Squarefree (m * t) :=
          hv.squarefree_of_dvd
            (mul_dvd_mul (dvd_refl m) (Nat.dvd_of_mem_divisors ht))
        have hmu :=
          ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
            (Nat.coprime_of_squarefree_mul hmt)
        simpa only [Int.cast_mul] using
          congrArg (fun z : ℤ => (z : ℝ)) hmu
      _ = (ArithmeticFunction.moebius m : ℝ) *
          (if k = 1 then 1 else 0) := by rw [hdivsum]
      _ = if m * k = m then
          (ArithmeticFunction.moebius m : ℝ) else 0 := by
        by_cases hk : k = 1
        · simp [hk]
        · have hmk : m * k ≠ m := by
            intro h
            apply hk
            apply mul_left_cancel₀ hm0
            simpa only [mul_one] using h
          simp [hk, hmk]
  · have hfilter : v.divisors.filter (fun d => m ∣ d) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hd, hmd⟩
      exact hmv (hmd.trans (Nat.dvd_of_mem_divisors hd))
    have hvm : v ≠ m := by
      intro h
      subst v
      exact hmv (dvd_refl m)
    simp only [hfilter, Finset.sum_empty, if_neg hvm]

/-- The transformed coefficients are evaluated from the explicit finite
weight formula. All off-diagonal contributions cancel by Möbius inversion. -/
theorem finiteSelbergWeight_transformed
    (s : BoundingSieve) (L : ℕ) {m : ℕ} (hm : m ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
      if m ∣ d then s.nu d * finiteSelbergWeight s L d else 0) =
      if m ≤ L then
        (ArithmeticFunction.moebius m : ℝ) * s.selbergTerms m /
          finiteSelbergNormalizer s L
      else 0 := by
  classical
  have hP : s.prodPrimes ≠ 0 := BoundingSieve.prodPrimes_ne_zero (s := s)
  have hmP : m ∈ s.prodPrimes.divisors := Nat.mem_divisors.mpr ⟨hm, hP⟩
  rw [← Finset.sum_filter]
  calc
    (∑ d ∈ s.prodPrimes.divisors with m ∣ d,
        s.nu d * finiteSelbergWeight s L d) =
        (∑ d ∈ s.prodPrimes.divisors with m ∣ d,
          (ArithmeticFunction.moebius d : ℝ) *
            (∑ v ∈ s.prodPrimes.divisors with d ∣ v ∧ v ≤ L,
              s.selbergTerms v)) / finiteSelbergNormalizer s L := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      exact nu_mul_finiteSelbergWeight_eq_sum_multiples s L
        (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)
    _ = (∑ v ∈ s.prodPrimes.divisors with v ≤ L,
          s.selbergTerms v * (∑ d ∈ v.divisors with m ∣ d,
            (ArithmeticFunction.moebius d : ℝ))) / finiteSelbergNormalizer s L := by
      congr 1
      calc
        _ = ∑ v ∈ s.prodPrimes.divisors, ∑ d ∈ s.prodPrimes.divisors,
            if m ∣ d then
              if d ∣ v ∧ v ≤ L then
                (ArithmeticFunction.moebius d : ℝ) * s.selbergTerms v
              else 0
            else 0 := by
          simp_rw [Finset.mul_sum, Finset.sum_filter, Finset.ite_sum_zero]
          exact Finset.sum_comm
        _ = _ := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro v hv
          by_cases hvL : v ≤ L
          · rw [if_pos hvL,
              ← Nat.divisors_filter_dvd_of_dvd hP (Nat.dvd_of_mem_divisors hv)]
            simp_rw [Finset.mul_sum, Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro d _hd
            by_cases hmd : m ∣ d <;> by_cases hdv : d ∣ v <;>
              simp [hmd, hdv, hvL, mul_comm]
          · rw [if_neg hvL]
            apply Finset.sum_eq_zero
            intro d _hd
            simp [hvL]
    _ = (∑ v ∈ s.prodPrimes.divisors with v ≤ L,
          if v = m then (ArithmeticFunction.moebius m : ℝ) * s.selbergTerms m
          else 0) / finiteSelbergNormalizer s L := by
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      rw [moebius_upper_divisor_sum
        (BoundingSieve.squarefree_of_mem_divisors_prodPrimes
          (s := s) (Finset.mem_filter.mp hv).1)]
      by_cases hvm : v = m <;> simp [hvm, mul_comm]
    _ = _ := by
      by_cases hmL : m ≤ L <;> simp [hmL, hmP]

/-- Mathlib's genuine lambda-square main sum at the explicit finite
Selberg weights is exactly the reciprocal normalizer. -/
theorem mainSum_lambdaSquared_finiteSelbergWeight
    (s : BoundingSieve) {L : ℕ} (hL : 1 ≤ L) :
    s.mainSum (BoundingSieve.lambdaSquared (finiteSelbergWeight s L)) =
      1 / finiteSelbergNormalizer s L := by
  classical
  have hG : finiteSelbergNormalizer s L ≠ 0 := (finiteSelbergNormalizer_pos s hL).ne'
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  calc
    _ = (∑ m ∈ s.prodPrimes.divisors with m ≤ L, s.selbergTerms m) /
        (finiteSelbergNormalizer s L) ^ 2 := by
      rw [Finset.sum_div, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      have hmP : m ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hm
      rw [finiteSelbergWeight_transformed s L hmP]
      by_cases hmL : m ≤ L
      · simp only [if_pos hmL]
        have hh : s.selbergTerms m ≠ 0 :=
          (BoundingSieve.selbergTerms_pos (s := s) hmP).ne'
        have hmu : (ArithmeticFunction.moebius m : ℝ) ^ 2 = 1 := by
          exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
            (BoundingSieve.squarefree_of_dvd_prodPrimes (s := s) hmP)
        rw [div_pow, mul_pow, hmu, one_mul]
        field_simp [hh, hG] <;> ring
      · simp [hmL]
    _ = 1 / finiteSelbergNormalizer s L := by
      change finiteSelbergNormalizer s L / (finiteSelbergNormalizer s L) ^ 2 = _
      field_simp [hG]

/-- A completely finite optimized sieve inequality, retaining the actual
lambda-square error. Estimating the normalizer asymptotically is separate. -/
theorem siftedSum_le_finiteSelbergNormalizer_add_errSum
    (s : BoundingSieve) {L : ℕ} (hL : 1 ≤ L) :
    s.siftedSum ≤ s.totalMass / finiteSelbergNormalizer s L +
      s.errSum (BoundingSieve.lambdaSquared (finiteSelbergWeight s L)) := by
  have h := BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
    (s := s) (BoundingSieve.lambdaSquared (finiteSelbergWeight s L))
    (upperMoebius_finiteSelbergWeight s hL)
  rw [mainSum_lambdaSquared_finiteSelbergWeight s hL] at h
  simpa only [div_eq_mul_inv, one_mul] using h

end

end ImbalancedChen
