import ImbalancedChen.Part3PrimeMellinProfileVariation
import ImbalancedChen.Part3RoughAuxiliarySW

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Complex Abel summation is applied to the literal prime coefficient times
Phi(n/U)*exp(i*t*log(n/U)). The original auxiliarySWError and its exact
primitive-coprime mean are used. The frequency cost is explicitly 1+|t|;
this module does not assert frequency-independent Siegel--Walfisz.
-/

namespace ImbalancedChen.Part3.MellinPrimeIntervalSW20261026b
noncomputable section
open Classical Finset Set MeasureTheory
open scoped BigOperators Topology
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open PrimeMellinProfileVariation20261026b

def mellinPrimeCoefficient (Phi : ℝ → ℝ) (t U : ℝ) (n : ℕ) : ℂ :=
  physicalProfile Phi t U n * (primeSWBeta n : ℂ)

private def primeKernel (k q b n : ℕ) : ℂ :=
  (if Nat.ModEq q n b ∧ n.Coprime k then (primeSWBeta n : ℂ) else 0) -
    (if n.Coprime (k*q) then (primeSWBeta n : ℂ) else 0) / (q.totient : ℂ)

private theorem kernel_sum_eq (S : Finset ℕ) (k q b : ℕ) :
    (∑ n ∈ S, primeKernel k q b n) =
      (betaCoprimeAPDiscrepancy S primeSWBeta q k b : ℂ) := by
  have hfirst :
      (∑ n ∈ S, if Nat.ModEq q n b ∧ n.Coprime k then (primeSWBeta n : ℂ) else 0) =
      ((∑ n ∈ S, if n.Coprime k ∧ Nat.ModEq q n b then primeSWBeta n else 0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime k <;> by_cases hm : Nat.ModEq q n b <;> simp [hc,hm]
  have hsecond :
      (∑ n ∈ S, if n.Coprime (k*q) then (primeSWBeta n : ℂ) else 0) =
      ((∑ n ∈ S, if n.Coprime (q*k) then primeSWBeta n else 0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime (k*q) <;> simp [Nat.mul_comm q k,hc]
  simp only [primeKernel, Finset.sum_sub_distrib, ← Finset.sum_div]
  rw [hfirst,hsecond]
  simp only [betaCoprimeAPDiscrepancy, coprimeMass, Complex.ofReal_sub,
    Complex.ofReal_div, Complex.ofReal_natCast]

private theorem weighted_kernel_sum (S : Finset ℕ) (f : ℝ → ℂ) (k q b : ℕ) :
    auxiliarySWError S (fun n => f n*(primeSWBeta n : ℂ)) k q b =
      ∑ n ∈ S, f n*primeKernel k q b n := by
  unfold auxiliarySWError
  simp only [primeKernel,mul_sub,mul_div_assoc,Finset.sum_sub_distrib,Finset.sum_div]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : Nat.ModEq q n b ∧ n.Coprime k <;> simp [hc]
  · apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime (k*q) <;> simp [hc]

private theorem complex_Abel_prime_bound (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U u v : ℝ,
      1 ≤ U → U ≤ u → u ≤ v → v ≤ 2*U →
      ∀ f : ℝ → ℂ,
      (∀ y ∈ Icc u v, DifferentiableAt ℝ f y) →
      IntegrableOn (deriv f) (Icc u v) →
      ∀ k q b : ℕ, 0 < k → 0 < q → b.Coprime q →
      ‖auxiliarySWError (primeSWInterval u v)
        (fun n => f n*(primeSWBeta n : ℂ)) k q b‖ ≤
        (C*U*(fouvryTau 2 k : ℝ)/Real.log (2*U)^B)*
          (‖f v‖+∫ y in Ioc u v, ‖deriv f y‖) := by
  obtain ⟨C,hC,hSW⟩ := primeSW_uniform_real B
  refine ⟨C,hC,?_⟩
  intro U u v hU hlo huv hhi f hfd hfi k q b hk hq hb
  let c : ℕ → ℂ := fun n => if Nat.floor u < n then primeKernel k q b n else 0
  let E : ℝ := C*U*(fouvryTau 2 k : ℝ)/Real.log (2*U)^B
  have hu0 : 0 ≤ u := by linarith
  have hprefix (y : ℝ) :
      (∑ n ∈ Finset.Icc 0 (Nat.floor y), c n) =
        (betaCoprimeAPDiscrepancy (primeSWInterval u y) primeSWBeta q k b : ℂ) := by
    have hset : (Finset.Icc 0 (Nat.floor y)).filter (fun n => Nat.floor u < n) =
        Finset.Ioc (Nat.floor u) (Nat.floor y) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    change (∑ n ∈ Finset.Icc 0 (Nat.floor y),
      if Nat.floor u < n then primeKernel k q b n else 0) = _
    rw [← Finset.sum_filter,hset,kernel_sum_eq]
    rfl
  have hzero : (∑ n ∈ Finset.Icc 0 (Nat.floor u), c n) = 0 := by
    rw [hprefix]
    simp [primeSWInterval,betaCoprimeAPDiscrepancy,coprimeMass]
  have hbound (y : ℝ) (hy : y ∈ Icc u v) :
      ‖∑ n ∈ Finset.Icc 0 (Nat.floor y), c n‖ ≤ E := by
    rw [hprefix,Complex.norm_real,Real.norm_eq_abs]
    exact hSW U u y hU hlo hy.1 (hy.2.trans hhi) q k hq hk b hb
  have heq : auxiliarySWError (primeSWInterval u v)
      (fun n => f n*(primeSWBeta n : ℂ)) k q b =
      f v*(∑ n ∈ Finset.Icc 0 (Nat.floor v), c n) -
        ∫ y in Ioc u v, deriv f y*∑ n ∈ Finset.Icc 0 (Nat.floor y), c n := by
    rw [weighted_kernel_sum]
    have hs : (∑ n ∈ primeSWInterval u v, f n*primeKernel k q b n) =
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
    _ ≤ ‖f v*(∑ n ∈ Finset.Icc 0 (Nat.floor v), c n)‖ +
        ‖∫ y in Ioc u v, deriv f y*∑ n ∈ Finset.Icc 0 (Nat.floor y), c n‖ := norm_sub_le _ _
    _ ≤ ‖f v‖*E+(∫ y in Ioc u v, ‖deriv f y‖)*E := add_le_add
      (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hbound v ⟨huv,le_rfl⟩) (norm_nonneg _)) hIntegral
    _ = _ := by dsimp only [E]; ring

/-- Actual complex Mellin-modulated prime SW with its mandatory explicit
frequency cost. All residue and auxiliary parameters retain the original
primitive mean. The constant precedes t, the interval and arithmetic data. -/
theorem mellin_prime_interval_SW (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi) (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U u v : ℝ,
      1 ≤ U → U ≤ u → u ≤ v → v ≤ 2*U → ∀ t : ℝ,
      ∀ k q b : ℕ, 0 < k → 0 < q → b.Coprime q →
      ‖auxiliarySWError (primeSWInterval u v) (mellinPrimeCoefficient Phi t U) k q b‖ ≤
        C*(1+|t|)*U*(fouvryTau 2 k : ℝ)/Real.log (2*U)^B := by
  obtain ⟨M0,hM0⟩ := (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2)).exists_bound_of_continuousOn
    hPhi.continuous.continuousOn
  obtain ⟨D0,hD0⟩ := (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2)).exists_bound_of_continuousOn
    hPhi.continuous_deriv_one.continuousOn
  let M : ℝ := max M0 1
  let D : ℝ := max D0 1
  have hM1 : 1 ≤ M := le_max_right _ _
  have hD1 : 1 ≤ D := le_max_right _ _
  have hM (y : ℝ) (hy : y ∈ Icc (1 : ℝ) 2) : |Phi y| ≤ M := by
    have hh : |Phi y| ≤ M0 := by simpa only [Real.norm_eq_abs] using hM0 y hy
    exact hh.trans (le_max_left _ _)
  have hD (y : ℝ) (hy : y ∈ Icc (1 : ℝ) 2) : |deriv Phi y| ≤ D := by
    have hh : |deriv Phi y| ≤ D0 := by simpa only [Real.norm_eq_abs] using hD0 y hy
    exact hh.trans (le_max_left _ _)
  obtain ⟨C,hC,hAbel⟩ := complex_Abel_prime_bound B
  refine ⟨C*(M+D),mul_pos hC (by linarith),?_⟩
  intro U u v hU hlo huv hhi t k q b hk hq hb
  have hUpos : 0 < U := by linarith
  have hpositive : Icc u v ⊆ Ioi (0 : ℝ) := fun y hy => by
    exact lt_of_lt_of_le hUpos (hlo.trans hy.1)
  have hcont : ContinuousOn (deriv (physicalProfile Phi t U)) (Icc u v) :=
    ((physicalProfile_contDiffOn hPhi t hUpos).continuousOn_deriv_of_isOpen
      isOpen_Ioi (by norm_num)).mono hpositive
  have hraw := hAbel U u v hU hlo huv hhi (physicalProfile Phi t U)
    (fun y hy => (physicalProfile_hasDerivAt hPhi t hUpos (hpositive hy)).differentiableAt)
    hcont.integrableOn_Icc k q b hk hq hb
  have hvariation := physicalProfile_variation_le hPhi (by linarith : 0 ≤ M)
    (by linarith : 0 ≤ D) hM hD hUpos hlo huv hhi t
  have hlog : 0 < Real.log (2*U) := Real.log_pos (by linarith)
  have hE : 0 ≤ C*U*(fouvryTau 2 k : ℝ)/Real.log (2*U)^B := by positivity
  change ‖auxiliarySWError (primeSWInterval u v)
    (fun n => physicalProfile Phi t U n*(primeSWBeta n : ℂ)) k q b‖ ≤ _
  calc
    _ ≤ _ := hraw
    _ ≤ (C*U*(fouvryTau 2 k : ℝ)/Real.log (2*U)^B)*((M+D)*(1+|t|)) :=
      mul_le_mul_of_nonneg_left hvariation hE
    _ = _ := by ring

end
end ImbalancedChen.Part3.MellinPrimeIntervalSW20261026b
