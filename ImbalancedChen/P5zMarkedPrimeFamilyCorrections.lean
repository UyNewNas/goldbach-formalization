import ImbalancedChen.P5zMarkedPrimeFamilyMultiplicity
import ImbalancedChen.P5zElevenErrorTransport
import ImbalancedChen.CurrentChenUpsilon9CoprimeGateBudget

/-! SOURCE ONLY / UNCOMPILED. Elementary primitive correction and small-prime
payments for ANY fixed-rank marked prime source. Normal source mass J is a
legitimate premise; no U* or corrected-source upper bound is a premise. -/
namespace ImbalancedChen
noncomputable section
open Filter Topology
open scoped BigOperators
open Classical

private theorem p5z_marked_prime_inverse_le {p : ℕ} (hp : Nat.Prime p)
    {H : ℝ} (hH : 0 < H) (hHp : H ≤ (p : ℝ)) : 1 / ((p : ℝ) - 1) ≤ 2 / H := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hh : H / 2 ≤ (p : ℝ) - 1 := by linarith only [hHp, hp2]
  calc
    _ ≤ 1 / (H / 2) := one_div_le_one_div_of_le (half_pos hH) hh
    _ = _ := by field_simp [hH.ne']

/-- Union bound over the actual rank prime slots, including repeated ones.
The divisor/totient estimate is the proved elementary finite helper. -/
theorem p5z_marked_noncoprime_totient_sum_le {rank N : ℕ}
    (t : Fin rank → Fin (N + 1)) (ht : t ∈ Part3.labelledPrimeTuples rank N)
    (H : ℝ) (hH : 0 < H) (hrough : ∀ i, H ≤ ((t i).val : ℝ))
    (D : Finset ℕ) (Q : ℕ) (hD : D ⊆ Finset.Icc 1 Q) :
    (∑ d ∈ D, if Nat.Coprime (Part3.labelledProduct t) d then (0 : ℝ)
      else 1 / (Nat.totient d : ℝ)) ≤
      (8 * (rank : ℝ) / H) * (1 + Real.log (max 1 (Q : ℝ))) := by
  have hp : ∀ i, Nat.Prime (t i).val := (Finset.mem_filter.mp ht).2
  have hL : 0 ≤ 1 + Real.log (max 1 (Q : ℝ)) := by
    have h := Real.log_nonneg (le_max_left (1 : ℝ) (Q : ℝ))
    linarith only [h]
  have hpoint (d : ℕ) :
      (if Nat.Coprime (Part3.labelledProduct t) d then (0 : ℝ) else 1 / (Nat.totient d : ℝ)) ≤
      ∑ i : Fin rank, if (t i).val ∣ d then 1 / (Nat.totient d : ℝ) else 0 := by
    by_cases hc : Nat.Coprime (Part3.labelledProduct t) d
    · rw [if_pos hc]
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    · have hex : ∃ i : Fin rank, ¬ Nat.Coprime (t i).val d := by
        by_contra hn
        apply hc
        apply Nat.coprime_prod_left_iff.mpr
        intro i hi
        by_contra hbad
        exact hn ⟨i, hbad⟩
      obtain ⟨i, hi⟩ := hex
      have hdiv : (t i).val ∣ d := by
        by_contra hn
        exact hi ((hp i).coprime_iff_not_dvd.mpr hn)
      have hsingle := Finset.single_le_sum
        (fun j (_hj : j ∈ (Finset.univ : Finset (Fin rank))) =>
          show 0 ≤ (if (t j).val ∣ d then 1 / (Nat.totient d : ℝ) else 0) by positivity)
        (Finset.mem_univ i)
      simpa only [if_neg hc, if_pos hdiv] using hsingle
  have hsum := Finset.sum_le_sum (fun d (_hd : d ∈ D) => hpoint d)
  rw [Finset.sum_comm] at hsum
  have hslot (i : Fin rank) :
      (∑ d ∈ D, if (t i).val ∣ d then 1 / (Nat.totient d : ℝ) else 0) ≤
        (8 / H) * (1 + Real.log (max 1 (Q : ℝ))) := by
    apply (currentChenUpsilon9_dvd_reciprocalTotient_sum_le D Q (t i).val (hp i) hD).trans
    have hinv := p5z_marked_prime_inverse_le (hp i) hH (hrough i)
    have hm := mul_le_mul_of_nonneg_right hinv hL
    nlinarith only [hm]
  calc
    _ ≤ ∑ i : Fin rank, ∑ d ∈ D,
        if (t i).val ∣ d then 1 / (Nat.totient d : ℝ) else 0 := hsum
    _ ≤ ∑ _i : Fin rank, (8 / H) * (1 + Real.log (max 1 (Q : ℝ))) :=
      Finset.sum_le_sum (fun i _ => hslot i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Exact signed recentering on weighted marked labels. -/
theorem p5z_markedCoprimeCorrection_eq_neg_sum {rank N : ℕ}
    (S : Finset (Fin rank → Fin (N + 1))) (W : (Fin rank → Fin (N + 1)) → ℝ)
    (D : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledCoprimeCorrection S Part3.labelledProduct W D rho =
      -(∑ t ∈ S, ∑ d ∈ D, W t * (rho d *
        (if Nat.Coprime (Part3.labelledProduct t) d then 0 else 1 / (Nat.totient d : ℝ)))) := by
  unfold p5z_labelledCoprimeCorrection p5z_labelledCoprimeMass p5z_labelledMass
  simp only [← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ t ∈ S, ∑ d ∈ D, -(W t * (rho d *
        (if Nat.Coprime (Part3.labelledProduct t) d then 0 else 1 / (Nat.totient d : ℝ)))) := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hc : Nat.Coprime (Part3.labelledProduct t) d <;>
        simp only [hc, if_true, if_false] <;> ring
    _ = _ := by simp only [Finset.sum_neg_distrib]

/-- Finite weighted correction cost, with an arbitrary fixed coefficient
bound M. No unit-bound is borrowed for a different physical coefficient. -/
theorem p5z_marked_abs_correction_le_mass {rank N : ℕ}
    (S : Finset (Fin rank → Fin (N + 1))) (hS : S ⊆ Part3.labelledPrimeTuples rank N)
    (W : (Fin rank → Fin (N + 1)) → ℝ) (hW : ∀ t ∈ S, 0 ≤ W t)
    (H : ℝ) (hH : 0 < H) (hrough : ∀ t ∈ S, ∀ i, H ≤ ((t i).val : ℝ))
    (D : Finset ℕ) (Q : ℕ) (hD : D ⊆ Finset.Icc 1 Q)
    (rho : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hrho : ∀ d ∈ D, |rho d| ≤ M) :
    |p5z_labelledCoprimeCorrection S Part3.labelledProduct W D rho| ≤
      M * ((8 * (rank : ℝ) / H) * (1 + Real.log (max 1 (Q : ℝ)))) * p5z_labelledMass S W := by
  rw [p5z_markedCoprimeCorrection_eq_neg_sum, abs_neg]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ t ∈ S, W t * (M *
        ((8 * (rank : ℝ) / H) * (1 + Real.log (max 1 (Q : ℝ))))) := by
      apply Finset.sum_le_sum
      intro t ht
      calc
        _ ≤ ∑ d ∈ D, |W t * (rho d *
            (if Nat.Coprime (Part3.labelledProduct t) d then 0 else 1 / (Nat.totient d : ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ D, W t * (M *
            (if Nat.Coprime (Part3.labelledProduct t) d then 0 else 1 / (Nat.totient d : ℝ))) := by
          apply Finset.sum_le_sum
          intro d hd
          have hb : 0 ≤ (if Nat.Coprime (Part3.labelledProduct t) d then (0 : ℝ)
            else 1 / (Nat.totient d : ℝ)) := by positivity
          rw [abs_mul, abs_of_nonneg (hW t ht), abs_mul, abs_of_nonneg hb]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hrho d hd) hb) (hW t ht)
        _ = W t * (M * ∑ d ∈ D,
            if Nat.Coprime (Part3.labelledProduct t) d then 0 else 1 / (Nat.totient d : ℝ)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (p5z_marked_noncoprime_totient_sum_le t (hS ht) H hH (hrough t ht) D Q hD) hM) (hW t ht)
    _ = _ := by unfold p5z_labelledMass; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t ht; ring

/-- Polynomial physical scope pays the primitive correction for a genuinely
rough marked source with normal source-mass upper coefficient J>=0. -/
theorem p5z_eventually_marked_correction_le {rank : ℕ}
    (S : (N : ℕ) → Finset (Fin rank → Fin (N + 1)))
    (W : (N : ℕ) → (Fin rank → Fin (N + 1)) → ℝ)
    (hS : ∀ N, S N ⊆ Part3.labelledPrimeTuples rank N)
    (hW : ∀ N, ∀ t ∈ S N, 0 ≤ W N t)
    (a nu M J : ℝ) (ha : 0 < a) (hnu : 0 ≤ nu) (hM : 0 ≤ M) (hJ : 0 ≤ J)
    (hrough : ∀ᶠ N : ℕ in atTop, Even N → ∀ t ∈ S N, ∀ i,
      (N : ℝ) ^ a ≤ ((t i).val : ℝ))
    (hmass : ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      p5z_labelledMass (S N) (W N) ≤ (J + eta) * ((N : ℝ) / Real.log (N : ℝ)))
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ D : Finset ℕ, ∀ Q : ℕ, ∀ rho : ℕ → ℝ,
      D ⊆ Finset.Icc 1 Q → (Q : ℝ) ≤ (N : ℝ) ^ nu → (∀ d ∈ D, |rho d| ≤ M) →
      |p5z_labelledCoprimeCorrection (S N) Part3.labelledProduct (W N) D rho| ≤
        eta * singularNormalization N := by
  let c := M * (8 * (rank : ℝ)) * (nu + 1) * (J + 1)
  have hpower := eventually_powerLog_le_singularNormalization c (1 - a) 0 (by linarith only [ha]) eta heta
  have hlog : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hpower, hrough, hmass 1 (by norm_num), hlog, eventually_ge_atTop (2 : ℕ)]
    with N hpowerN hroughN hmassN hlogN hN
  intro hEven D Q rho hD hQ hrho
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp := zero_lt_one.trans hNr
  have hHp : 0 < (N : ℝ) ^ a := Real.rpow_pos_of_pos hNp _
  have hlogp : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlogN
  have hmax : max (1 : ℝ) (Q : ℝ) ≤ (N : ℝ) ^ nu := max_le (Real.one_le_rpow hNr.le hnu) hQ
  have hlogQ : Real.log (max 1 (Q : ℝ)) ≤ nu * Real.log (N : ℝ) := by
    have h := Real.log_le_log (zero_lt_one.trans_le (le_max_left _ _)) hmax
    rwa [Real.log_rpow hNp] at h
  have hL : 1 + Real.log (max 1 (Q : ℝ)) ≤ (nu + 1) * Real.log (N : ℝ) := by
    nlinarith only [hlogQ, hlogN]
  have hfinite := p5z_marked_abs_correction_le_mass (S N) (hS N) (W N) (hW N)
    ((N : ℝ) ^ a) hHp (hroughN hEven) D Q hD rho M hM hrho
  have hpaid : M * ((8 * (rank : ℝ) / (N : ℝ) ^ a) * (1 + Real.log (max 1 (Q : ℝ)))) *
      p5z_labelledMass (S N) (W N) ≤
    M * ((8 * (rank : ℝ) / (N : ℝ) ^ a) * ((nu + 1) * Real.log (N : ℝ))) *
      ((J + 1) * ((N : ℝ) / Real.log (N : ℝ))) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hL (by positivity)) hM
    · exact hmassN hEven
    · exact Finset.sum_nonneg (fun t ht => hW N t ht)
    · positivity
  have heq : M * ((8 * (rank : ℝ) / (N : ℝ) ^ a) * ((nu + 1) * Real.log (N : ℝ))) *
      ((J + 1) * ((N : ℝ) / Real.log (N : ℝ))) = c * (N : ℝ) ^ (1 - a) := by
    dsimp only [c]
    rw [Real.rpow_sub hNp, Real.rpow_one]
    field_simp [hHp.ne', hlogp.ne'] <;> ring
  rw [heq] at hpaid
  exact (hfinite.trans hpaid).trans (by simpa only [pow_zero, mul_one] using hpowerN)

/-- Exact ceiling cutoff payment, including B=0 and all rounding losses. -/
theorem p5z_eventually_marked_smallPrimeMass_le_ceil {rank : ℕ}
    (S : (N : ℕ) → Finset (Fin rank → Fin (N + 1)))
    (W : (N : ℕ) → (Fin rank → Fin (N + 1)) → ℝ)
    (hS : ∀ N, S N ⊆ Part3.labelledPrimeTuples rank N)
    (B : ℝ) (hB : 0 ≤ B) (hW : ∀ N, ∀ t ∈ S N, W N t ≤ B)
    (hcap : ∀ N, ∀ t ∈ S N, Part3.labelledProduct t ≤ N)
    (theta : ℝ) (htheta : theta < 1) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      p5z_labelledSmallPrimeMass (S N) Part3.labelledProduct (W N) N
        (Nat.ceil ((N : ℝ) ^ theta)) ≤ eta * singularNormalization N := by
  let C : ℝ := B * (rank ^ rank : ℕ)
  have hC : 0 ≤ C := mul_nonneg hB (Nat.cast_nonneg _)
  filter_upwards [eventually_powerLog_le_singularNormalization C theta 0 htheta (eta / 2) (half_pos heta),
    p5z_eventually_constant_le_singularNormalization C (eta / 2) (half_pos heta)]
    with N hpowerN hconstN
  have hsmall := p5z_markedSmallPrimeMass_le (S N) (hS N) (W N) B hB (hW N) (hcap N)
    (Nat.ceil ((N : ℝ) ^ theta))
  have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg N) theta)).le
  have hscaled := mul_le_mul_of_nonneg_left hceil hC
  simp only [pow_zero, mul_one] at hpowerN
  nlinarith only [hsmall, hscaled, hpowerN, hconstN]

end
end ImbalancedChen

