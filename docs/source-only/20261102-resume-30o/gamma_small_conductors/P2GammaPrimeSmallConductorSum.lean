import ImbalancedChen.P2GammaPrimeTargetDeletion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Small primitive conductors for the actual prime row. Both factors retain
the quotient k-unit filter. No coprimality between r and k is used. The
primitive count and the residue factor phi(r) are paid separately.
-/

namespace ImbalancedChen.P2GammaPrimeSmallConductorSum
noncomputable section
open Classical Finset
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open P2GammaSmallConductorArithmetic P2GammaPrimeCharacterSW P2GammaPrimeTargetDeletion
open Part3.MellinPrimeIntervalSW20261026b
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def smallConductorContribution (R Q : ℕ) (S T : Finset ℕ) (a b : ℕ → ℂ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 Q, ∑ r ∈ Finset.Icc 2 R with r*k ≤ Q,
    (1/((r*k).totient : ℝ))*
      ∑ psi : PrimitiveCharacter r,
        ‖rowTransform S a k r psi.1‖*‖rowTransform T b k r psi.1‖

/-- Finite scalar payment only. The actual prime theorem is instantiated
in `actual_mellin_small_conductors` below; this is not an SW supplier. -/
theorem smallConductorContribution_le (R Q : ℕ) (S T : Finset ℕ)
    (a b : ℕ → ℂ) {E : ℝ} (hE : 0 ≤ E)
    (hprime : ∀ k r : ℕ, 0 < k → 1 < r → ∀ psi : PrimitiveCharacter r,
      ‖rowTransform S a k r psi.1‖ ≤ (r.totient : ℝ)*E*(k.divisors.card : ℝ)) :
    smallConductorContribution R Q S T a b ≤
      16*E*rowMass T b*(R : ℝ)^2*(1+Real.log (max 1 (Q : ℝ)))^2 := by
  have hmass : 0 ≤ rowMass T b := rowMass_nonneg T b
  have hpoint (k r : ℕ) (hk : 0 < k) (hr : 1 < r) :
      (1/((r*k).totient : ℝ))*
        (∑ psi : PrimitiveCharacter r,
          ‖rowTransform S a k r psi.1‖*‖rowTransform T b k r psi.1‖) ≤
        E*rowMass T b*(r.totient : ℝ)*((k.divisors.card : ℝ)/(k.totient : ℝ)) := by
    have hr0 : 0 < r := by omega
    have hphi : (0 : ℝ) < (r.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hr0
    have hsum :
        (∑ psi : PrimitiveCharacter r,
          ‖rowTransform S a k r psi.1‖*‖rowTransform T b k r psi.1‖) ≤
        (r.totient : ℝ)*((r.totient : ℝ)*E*(k.divisors.card : ℝ)*rowMass T b) := by
      calc
        _ ≤ ∑ _psi : PrimitiveCharacter r,
            (r.totient : ℝ)*E*(k.divisors.card : ℝ)*rowMass T b := by
          exact Finset.sum_le_sum fun psi hpsi =>
            mul_le_mul (hprime k r hk hr psi) (rowTransform_norm_le_mass T b k r psi.1)
              (norm_nonneg _) (by positivity)
        _ = (Fintype.card (PrimitiveCharacter r) : ℝ)*
            ((r.totient : ℝ)*E*(k.divisors.card : ℝ)*rowMass T b) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (primitive_character_count_le_phi r hr0) (by positivity)
    calc
      _ ≤ ((1/(r.totient : ℝ))*(1/(k.totient : ℝ)))*
          ((r.totient : ℝ)*((r.totient : ℝ)*E*(k.divisors.card : ℝ)*rowMass T b)) :=
        mul_le_mul (inv_totient_mul_le r k hr0 hk) hsum (by positivity) (by positivity)
      _ = _ := by field_simp [hphi.ne']; ring
  unfold smallConductorContribution
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 Q, ∑ r ∈ Finset.Icc 2 R with r*k ≤ Q,
        E*rowMass T b*(r.totient : ℝ)*((k.divisors.card : ℝ)/(k.totient : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.sum_le_sum fun r hr => hpoint k r (Finset.mem_Icc.mp hk).1
        (by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1; omega)
    _ ≤ ∑ k ∈ Finset.Icc 1 Q, ∑ r ∈ Finset.Icc 2 R,
        E*rowMass T b*(r.totient : ℝ)*((k.divisors.card : ℝ)/(k.totient : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun r hr hnot => by positivity)
    _ = E*rowMass T b*(∑ r ∈ Finset.Icc 2 R, (r.totient : ℝ))*
        (∑ k ∈ Finset.Icc 1 Q, (k.divisors.card : ℝ)/(k.totient : ℝ)) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ E*rowMass T b*(R : ℝ)^2*
        (16*(1+Real.log (max 1 (Q : ℝ)))^2) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (sum_phi_small_le_square R) (mul_nonneg hE hmass))
        (sum_tau_div_totient_le_log_sq Q) (by positivity) (by positivity)
    _ = _ := by ring

/-- The actual small-conductor prime row, for every subinterval and Mellin
mode in the admitted log range, and every independent complement row.
The target is deleted directly and C0 is the fixed integer one. -/
theorem actual_mellin_small_conductors
    (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    {eta J A Ctarget : ℝ} (heta : 0 < eta) (hJ : 0 ≤ J)
    (hCtarget : 0 ≤ Ctarget) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ x M u v : ℝ, x0 ≤ x → x^eta ≤ M →
      1 ≤ M → M ≤ u → u ≤ v → v ≤ 2*M →
      ∀ t : ℝ, |t| ≤ Real.log x^J →
      ∀ target : ℕ, 0 < target → (target : ℝ) ≤ x^Ctarget →
      ∀ R Q : ℕ, ∀ T : Finset ℕ, ∀ b : ℕ → ℂ,
      smallConductorContribution R Q (primeSWInterval u v) T
        (targetDeleted target (mellinPrimeCoefficient Phi t M)) b ≤
        C*M*rowMass T b*(R : ℝ)^2*(1+Real.log (max 1 (Q : ℝ)))^2/Real.log x^A := by
  obtain ⟨C,hC,x0,hx0,hbound⟩ :=
    targetDeleted_mellin_prime_character_completeScale Phi hPhi heta hJ hCtarget (A := A)
  refine ⟨16*C,by positivity,x0,hx0,?_⟩
  intro x M u v hx hpower hM hlo huv hhi t ht target htarget hTarget R Q T b
  have hL : 0 < Real.log x := Real.log_pos (hx0.trans_le hx)
  have hE : 0 ≤ C*M/Real.log x^A := by positivity
  have hpayment := smallConductorContribution_le R Q (primeSWInterval u v) T
    (targetDeleted target (mellinPrimeCoefficient Phi t M)) b hE (by
      intro k r hk hr psi
      have hh := hbound x M u v hx hpower hM hlo huv hhi t ht target htarget hTarget
        k r hk (by omega) psi.1 (primitiveCharacter_ne_one hr psi)
      convert hh using 1 <;> ring)
  convert hpayment using 1 <;> ring

/-- After the geometric/norm orders B and D are fixed, choose the stronger
prime accuracy A+2B+2. The two fixed logarithmic costs then disappear. -/
theorem actual_mellin_small_conductors_logSaving
    (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    {eta J A Ctarget B D : ℝ} (heta : 0 < eta) (hJ : 0 ≤ J)
    (hCtarget : 0 ≤ Ctarget) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ x M u v : ℝ, x0 ≤ x → x^eta ≤ M →
      1 ≤ M → M ≤ u → u ≤ v → v ≤ 2*M →
      ∀ t : ℝ, |t| ≤ Real.log x^J →
      ∀ target : ℕ, 0 < target → (target : ℝ) ≤ x^Ctarget →
      ∀ R Q : ℕ, (R : ℝ) ≤ Real.log x^B → (Q : ℝ) ≤ x^D →
      ∀ T : Finset ℕ, ∀ b : ℕ → ℂ,
      smallConductorContribution R Q (primeSWInterval u v) T
        (targetDeleted target (mellinPrimeCoefficient Phi t M)) b ≤
        C*M*rowMass T b/Real.log x^A := by
  obtain ⟨C,hC,x1,hx1,hbound⟩ := actual_mellin_small_conductors Phi hPhi heta hJ hCtarget
    (A := A+2*B+2)
  refine ⟨C*(1+D)^2,mul_pos hC (sq_pos_of_pos (by linarith)),max x1 (Real.exp 1),
    hx1.trans_le (le_max_left _ _),?_⟩
  intro x M u v hx hpower hM hlo huv hhi t ht target htarget hTarget R Q hR hQ T b
  have hx1' : x1 ≤ x := (le_max_left _ _).trans hx
  have hxexp : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hxgt : 1 < x := hx1.trans_le hx1'
  have hx0 : 0 < x := zero_lt_one.trans hxgt
  have hL1 : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxexp
  have hL : 0 < Real.log x := zero_lt_one.trans_le hL1
  have hmax : max 1 (Q : ℝ) ≤ x^D :=
    max_le (Real.one_le_rpow hxgt.le hD) hQ
  have hlogQ : Real.log (max 1 (Q : ℝ)) ≤ D*Real.log x := by
    calc
      _ ≤ Real.log (x^D) := Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hmax
      _ = _ := Real.log_rpow hx0 D
  have hQcost : (1+Real.log (max 1 (Q : ℝ)))^2 ≤ (1+D)^2*Real.log x^2 := by
    have hqnonneg : 0 ≤ 1+Real.log (max 1 (Q : ℝ)) := by
      have hl := Real.log_nonneg (le_max_left 1 (Q : ℝ))
      linarith
    have hbase : 1+Real.log (max 1 (Q : ℝ)) ≤ (1+D)*Real.log x := by nlinarith
    have hs := pow_le_pow_left₀ hqnonneg hbase 2
    simpa only [mul_pow] using hs
  have hRcost : (R : ℝ)^2 ≤ Real.log x^(2*B) := by
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg R) hR 2
    have heq : (Real.log x^B)^2 = Real.log x^(2*B) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]
      congr 1
      ring
    exact hs.trans_eq heq
  have hcost : (R : ℝ)^2*(1+Real.log (max 1 (Q : ℝ)))^2/
        Real.log x^(A+2*B+2) ≤ (1+D)^2/Real.log x^A := by
    calc
      _ ≤ (Real.log x^(2*B)*((1+D)^2*Real.log x^2))/Real.log x^(A+2*B+2) :=
        div_le_div_of_nonneg_right (mul_le_mul hRcost hQcost (by positivity) (by positivity))
          (Real.rpow_nonneg hL.le _)
      _ = _ := by
        rw [show A+2*B+2 = A+(2*B+2) by ring,
          Real.rpow_add hL,Real.rpow_add hL,Real.rpow_natCast]
        field_simp [(Real.rpow_pos_of_pos hL A).ne',
          (Real.rpow_pos_of_pos hL (2*B)).ne',hL.ne']
        <;> ring
  have hp := hbound x M u v hx1' hpower hM hlo huv hhi t ht target htarget hTarget R Q T b
  calc
    _ ≤ C*M*rowMass T b*(R : ℝ)^2*(1+Real.log (max 1 (Q : ℝ)))^2/
        Real.log x^(A+2*B+2) := hp
    _ = (C*M*rowMass T b)*((R : ℝ)^2*(1+Real.log (max 1 (Q : ℝ)))^2/
        Real.log x^(A+2*B+2)) := by ring
    _ ≤ (C*M*rowMass T b)*((1+D)^2/Real.log x^A) :=
      mul_le_mul_of_nonneg_left hcost (by positivity)
    _ = _ := by ring

end
end ImbalancedChen.P2GammaPrimeSmallConductorSum
