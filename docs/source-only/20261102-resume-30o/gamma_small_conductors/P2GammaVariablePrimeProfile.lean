import ImbalancedChen.P2GammaPrimeTargetDeletion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The amplitude may vary after the SW constant. The only amplitude inputs
are its actual differentiability, derivative integrability and stated
geometric Abel norm. No distribution premise is used. The complex Abel
identity is the public-source version of the private proof in
Part3MellinPrimeIntervalSW, now retaining its full variable-amplitude API.
-/

namespace ImbalancedChen.P2GammaVariablePrimeProfile
noncomputable section
open Classical Finset Set MeasureTheory Filter
open scoped BigOperators Topology
open Part3 P2GammaPrimeCharacterSW P2GammaPrimeTargetDeletion
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def profilePrimeCoefficient (f : ℝ → ℂ) (n : ℕ) : ℂ := f n*(primeSWBeta n : ℂ)

def profileAbelNorm (f : ℝ → ℂ) (u v : ℝ) : ℝ :=
  ‖f v‖+∫ y in Ioc u v, ‖deriv f y‖

private def primeKernel (k r b n : ℕ) : ℂ :=
  (if Nat.ModEq r n b ∧ n.Coprime k then (primeSWBeta n : ℂ) else 0)-
    (if n.Coprime (k*r) then (primeSWBeta n : ℂ) else 0)/(r.totient : ℂ)

private theorem kernel_sum_eq (S : Finset ℕ) (k r b : ℕ) :
    (∑ n ∈ S, primeKernel k r b n) =
      (betaCoprimeAPDiscrepancy S primeSWBeta r k b : ℂ) := by
  have hfirst :
      (∑ n ∈ S, if Nat.ModEq r n b ∧ n.Coprime k then (primeSWBeta n : ℂ) else 0) =
        ((∑ n ∈ S, if n.Coprime k ∧ Nat.ModEq r n b then primeSWBeta n else 0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime k <;> by_cases hm : Nat.ModEq r n b <;> simp [hc,hm]
  have hsecond :
      (∑ n ∈ S, if n.Coprime (k*r) then (primeSWBeta n : ℂ) else 0) =
        ((∑ n ∈ S, if n.Coprime (r*k) then primeSWBeta n else 0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime (k*r) <;> simp [Nat.mul_comm r k,hc]
  simp only [primeKernel,Finset.sum_sub_distrib,← Finset.sum_div]
  rw [hfirst,hsecond]
  simp only [betaCoprimeAPDiscrepancy,coprimeMass,Complex.ofReal_sub,
    Complex.ofReal_div,Complex.ofReal_natCast]

private theorem weighted_kernel_sum (S : Finset ℕ) (f : ℝ → ℂ) (k r b : ℕ) :
    auxiliarySWError S (profilePrimeCoefficient f) k r b =
      ∑ n ∈ S, f n*primeKernel k r b n := by
  unfold auxiliarySWError
  simp only [primeKernel,mul_sub,mul_div_assoc,Finset.sum_sub_distrib,Finset.sum_div]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : Nat.ModEq r n b ∧ n.Coprime k <;> simp [profilePrimeCoefficient,hc]
  · apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime (k*r) <;> simp [profilePrimeCoefficient,hc]

/-- A genuine prime theorem, uniform in the amplitude after its norm is
displayed. The source prime supplier is invoked, never assumed. -/
theorem complex_profile_prime_SW (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M u v : ℝ,
      1 ≤ M → M ≤ u → u ≤ v → v ≤ 2*M →
      ∀ f : ℝ → ℂ,
      (∀ y ∈ Icc u v, DifferentiableAt ℝ f y) →
      IntegrableOn (deriv f) (Icc u v) →
      ∀ k r b : ℕ, 0 < k → 0 < r → b.Coprime r →
      ‖auxiliarySWError (primeSWInterval u v) (profilePrimeCoefficient f) k r b‖ ≤
        (C*M*(k.divisors.card : ℝ)/Real.log (2*M)^D)*profileAbelNorm f u v := by
  obtain ⟨C,hC,hSW⟩ := primeSW_uniform_real D
  refine ⟨C,hC,?_⟩
  intro M u v hM hlo huv hhi f hfd hfi k r b hk hr hb
  let c : ℕ → ℂ := fun n => if Nat.floor u < n then primeKernel k r b n else 0
  let E : ℝ := C*M*(k.divisors.card : ℝ)/Real.log (2*M)^D
  have hu0 : 0 ≤ u := by linarith
  have hprefix (y : ℝ) :
      (∑ n ∈ Finset.Icc 0 (Nat.floor y), c n) =
        (betaCoprimeAPDiscrepancy (primeSWInterval u y) primeSWBeta r k b : ℂ) := by
    have hset : (Finset.Icc 0 (Nat.floor y)).filter (fun n => Nat.floor u < n) =
        Finset.Ioc (Nat.floor u) (Nat.floor y) := by
      ext n
      simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
      omega
    change (∑ n ∈ Finset.Icc 0 (Nat.floor y),
      if Nat.floor u < n then primeKernel k r b n else 0) = _
    rw [← Finset.sum_filter,hset,kernel_sum_eq]
    rfl
  have hzero : (∑ n ∈ Finset.Icc 0 (Nat.floor u), c n) = 0 := by
    rw [hprefix]
    simp [primeSWInterval,betaCoprimeAPDiscrepancy,coprimeMass]
  have hbound (y : ℝ) (hy : y ∈ Icc u v) :
      ‖∑ n ∈ Finset.Icc 0 (Nat.floor y), c n‖ ≤ E := by
    rw [hprefix,Complex.norm_real,Real.norm_eq_abs]
    simpa only [fouvryTau_two,E] using hSW M u y hM hlo hy.1 (hy.2.trans hhi) r k hr hk b hb
  have heq : auxiliarySWError (primeSWInterval u v) (profilePrimeCoefficient f) k r b =
      f v*(∑ n ∈ Finset.Icc 0 (Nat.floor v), c n)-
        ∫ y in Ioc u v, deriv f y*∑ n ∈ Finset.Icc 0 (Nat.floor y), c n := by
    rw [weighted_kernel_sum]
    have hs : (∑ n ∈ primeSWInterval u v, f n*primeKernel k r b n) =
        ∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v), f n*c n := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [c,if_pos (Finset.mem_Ioc.mp hn).1]
    rw [hs,sum_mul_eq_sub_sub_integral_mul c hu0 huv hfd hfi,hzero,mul_zero,sub_zero]
  have hmajor : IntegrableOn (fun y => ‖deriv f y‖*E) (Ioc u v) :=
    (hfi.mono_set Ioc_subset_Icc_self).norm.mul_const E
  have hIntegral :
      ‖∫ y in Ioc u v, deriv f y*∑ n ∈ Finset.Icc 0 (Nat.floor y), c n‖ ≤
        (∫ y in Ioc u v, ‖deriv f y‖)*E := by
    have hi := norm_integral_le_of_norm_le hmajor (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound y ⟨hy.1.le,hy.2⟩) (norm_nonneg _))
    simpa only [integral_mul_const] using hi
  rw [heq]
  calc
    _ ≤ ‖f v*(∑ n ∈ Finset.Icc 0 (Nat.floor v), c n)‖+
        ‖∫ y in Ioc u v, deriv f y*∑ n ∈ Finset.Icc 0 (Nat.floor y), c n‖ := norm_sub_le _ _
    _ ≤ ‖f v‖*E+(∫ y in Ioc u v, ‖deriv f y‖)*E := add_le_add
      (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hbound v ⟨huv,le_rfl⟩) (norm_nonneg _)) hIntegral
    _ = _ := by dsimp only [E,profileAbelNorm]; ring

/-- Every permitted varying complex profile with the stated logarithmic
Abel norm supplies the actual nonprincipal prime transform. A profile norm
is a geometric input, not a prime-estimate premise. -/
theorem variable_profile_character_completeScale
    {eta J A V : ℝ} (heta : 0 < eta) (hV : 0 ≤ V) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ x M u v : ℝ, x0 ≤ x → x^eta ≤ M →
      1 ≤ M → M ≤ u → u ≤ v → v ≤ 2*M →
      ∀ f : ℝ → ℂ,
      (∀ y ∈ Icc u v, DifferentiableAt ℝ f y) →
      IntegrableOn (deriv f) (Icc u v) →
      profileAbelNorm f u v ≤ V*Real.log x^J →
      ∀ k r : ℕ, 0 < k → 0 < r → ∀ psi : DirichletCharacter ℂ r,
      psi ≠ 1 →
      ‖rowTransform (primeSWInterval u v) (profilePrimeCoefficient f) k r psi‖ ≤
        (r.totient : ℝ)*(C*M*(k.divisors.card : ℝ)/Real.log x^A) := by
  let D : ℕ := Nat.ceil (A+J)
  obtain ⟨C,hC,hSW⟩ := complex_profile_prime_SW D
  refine ⟨C*(V+1)/eta^D,div_pos (mul_pos hC (by linarith)) (pow_pos heta D),Real.exp 1,
    Real.one_lt_exp_iff.mpr (by norm_num),?_⟩
  intro x M u v hx hpower hM hlo huv hhi f hfd hfi hvar k r hk hr psi hpsi
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hx
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hL1 : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
  have hL : 0 < Real.log x := zero_lt_one.trans_le hL1
  have hlogM : 0 < Real.log (2*M) := Real.log_pos (by linarith)
  have hcomp : eta*Real.log x ≤ Real.log (2*M) := by
    calc
      _ = Real.log (x^eta) := (Real.log_rpow hx0 eta).symm
      _ ≤ Real.log M := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hpower
      _ ≤ _ := Real.log_le_log (by linarith) (by linarith)
  have hceil : Real.log x^(A+J) ≤ Real.log x^D := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hL1 (Nat.le_ceil (A+J))
  have hden : eta^D*Real.log x^(A+J) ≤ Real.log (2*M)^D := by
    calc
      _ ≤ eta^D*Real.log x^D := mul_le_mul_of_nonneg_left hceil (pow_nonneg heta.le D)
      _ = (eta*Real.log x)^D := (mul_pow _ _ _).symm
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg heta.le hL.le) hcomp D
  let : NeZero r := ⟨hr.ne'⟩
  apply rowTransform_norm_le_phi_error _ _ k psi hpsi (by positivity)
  intro b hb
  have hvar' : profileAbelNorm f u v ≤ (V+1)*Real.log x^J :=
    hvar.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hL.le _))
  calc
    _ ≤ (C*M*(k.divisors.card : ℝ)/Real.log (2*M)^D)*profileAbelNorm f u v :=
      hSW M u v hM hlo huv hhi f hfd hfi k r b hk hr hb
    _ ≤ (C*M*(k.divisors.card : ℝ)/Real.log (2*M)^D)*((V+1)*Real.log x^J) :=
      mul_le_mul_of_nonneg_left hvar' (by positivity)
    _ ≤ (C*M*(k.divisors.card : ℝ)/(eta^D*Real.log x^(A+J)))*((V+1)*Real.log x^J) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity)
          (mul_pos (pow_pos heta D) (Real.rpow_pos_of_pos hL _)) hden)
        (by positivity)
    _ = _ := by
      rw [Real.rpow_add hL]
      field_simp [(pow_pos heta D).ne',(Real.rpow_pos_of_pos hL A).ne',
        (Real.rpow_pos_of_pos hL J).ne']
      <;> ring

end
end ImbalancedChen.P2GammaVariablePrimeProfile
