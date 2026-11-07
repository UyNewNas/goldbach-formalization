import ImbalancedChen.P1OriginalCoarseUpperResidualUniformity
import MathlibNt.SieveTheory.LiLiuPrereqWFAnalytic

/-!
# Actual signed upper-density tails at a small common prime cutoff

SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY.

Both actual upper densities use the SAME target-deleted prime carrier.
Their Euler baseline cancels exactly before any estimate.  The pinned
all-depth actual-T exponential theorem supplies a quantitative defect
bound under its explicit power budget.  Its auxiliary parameter may be
smaller than the literal logarithmic residual, so the actual coefficient,
cutoff and strict level remain unchanged.

This file supplies pointwise arithmetic tail inequalities and finite
moving-budget adapters.  It does not postulate a small-prime mean or
replace the required a-to-zero summation by a bound depending on 1/a.
-/

namespace ImbalancedChen.P1OriginalSmallCutoffActualTail

noncomputable section
open scoped Classical BigOperators
open Filter Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

def boundaryExcess (N cap : ℕ) (y R : ℝ) : ℝ :=
  ∑ q ∈ actualSmallPrimeFinset N cap y,
    ∑ s ∈ actualUpperRosserBoundarySets N cap y R q,
      actualUpperRosserBoundaryTerm N cap y q s

theorem boundaryExcess_nonneg (N cap : ℕ) (hEven : Even N) (y R : ℝ) :
    0 ≤ boundaryExcess N cap y R := by
  apply Finset.sum_nonneg
  intro q hq
  apply Finset.sum_nonneg
  intro s hs
  apply actualUpperRosserBoundaryTerm_nonneg N cap hEven y hq
  exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1).trans
    (Finset.filter_subset _ _)

theorem actualPlus_eq_euler_mul_one_add_boundary (N cap : ℕ) (hEven : Even N)
    (y R : ℝ) (hcap : y ≤ (cap : ℝ)) (hy : 1 < y) (hyR : y ≤ R) :
    actualSmallRosserPlusDensity N cap y R =
      actualSmallEulerProduct N cap y * (1 + boundaryExcess N cap y R) := by
  have hratio := actualSmallRosserPlusDensity_ratio_eq_one_add_boundary N cap hEven y R
    hcap (hy.trans_le hyR)
    (fun p hp => (mem_actualSmallPrimeFinset.mp hp).2.2.2.trans_le hyR)
  have hV := actualSmallEulerProduct_pos N cap y hEven
  have h := (div_eq_iff hV.ne').mp hratio
  simpa only [boundaryExcess, mul_comm] using h

/-- Exact cancellation of the Euler baseline of the same actual carrier. -/
theorem actualPlus_sub_eq_euler_mul_boundary_sub (N cap : ℕ) (hEven : Even N)
    (y Rold Rnew : ℝ) (hcap : y ≤ (cap : ℝ)) (hy : 1 < y)
    (hold : y ≤ Rold) (hnew : y ≤ Rnew) :
    actualSmallRosserPlusDensity N cap y Rold - actualSmallRosserPlusDensity N cap y Rnew =
      actualSmallEulerProduct N cap y *
        (boundaryExcess N cap y Rold - boundaryExcess N cap y Rnew) := by
  rw [actualPlus_eq_euler_mul_one_add_boundary N cap hEven y Rold hcap hy hold,
    actualPlus_eq_euler_mul_one_add_boundary N cap hEven y Rnew hcap hy hnew]
  ring

theorem actualPlus_excess_nonneg (N cap : ℕ) (hEven : Even N)
    (y R : ℝ) (hcap : y ≤ (cap : ℝ)) (hy : 1 < y) (hyR : y ≤ R) :
    0 ≤ actualSmallRosserPlusDensity N cap y R - actualSmallEulerProduct N cap y := by
  rw [actualPlus_eq_euler_mul_one_add_boundary N cap hEven y R hcap hy hyR]
  have h := mul_nonneg (actualSmallEulerProduct_pos N cap y hEven).le
    (boundaryExcess_nonneg N cap hEven y R)
  nlinarith only [h]

/-- A smaller analytic parameter still covers the literal actual carrier.
This is the only cutoff change on the Suzuki side; R and the actual
coefficient on the left remain fixed. -/
theorem root_covers_actual_cutoff (y R t : ℝ) (hy : 1 < y) (hyR : y ≤ R)
    (ht : 2 ≤ t) (hpower : y ^ t ≤ R) :
    2 ≤ Nat.ceil R ∧ y ≤ (Nat.ceil R : ℝ) ^ (1 / t) ∧
      2 ≤ Nat.ceil ((Nat.ceil R : ℝ) ^ (1 / t)) := by
  have hy0 : 0 < y := zero_lt_one.trans hy
  have ht0 : 0 < t := by linarith
  have hD : 2 ≤ Nat.ceil R := by
    have h1 : (1 : ℕ) < Nat.ceil R := Nat.lt_ceil.mpr (by simpa using hy.trans_le hyR)
    omega
  have hcancel : t * (1 / t) = (1 : ℝ) := by field_simp [ht0.ne']
  have hroot : (y ^ t) ^ (1 / t) = y := by
    rw [← Real.rpow_mul hy0.le, hcancel, Real.rpow_one]
  have hcover : y ≤ (Nat.ceil R : ℝ) ^ (1 / t) := by
    rw [← hroot]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hy0.le _)
      (hpower.trans (Nat.le_ceil R)) (by positivity)
  have hz : 2 ≤ Nat.ceil ((Nat.ceil R : ℝ) ^ (1 / t)) := by
    have h1 : (1 : ℕ) < Nat.ceil ((Nat.ceil R : ℝ) ^ (1 / t)) :=
      Nat.lt_ceil.mpr (by simpa using hy.trans_le hcover)
    omega
  exact ⟨hD, hcover, hz⟩

theorem actual_suzuki_cutoff_all_primes (N : ℕ) (hEven : Even N)
    (y R t : ℝ) (hcover : y ≤ (Nat.ceil R : ℝ) ^ (1 / t)) :
    ∀ p ∈ (goldbachB8PlusBoundingSieve N hEven y).prodPrimes.primeFactors,
      p < Nat.ceil ((Nat.ceil R : ℝ) ^ (1 / t)) := by
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ goldbachB10ProdPrimes N y :=
    (Nat.mem_primeFactors_of_ne_zero
      (goldbachB8PlusBoundingSieve N hEven y).prodPrimes_ne_zero).mp hp |>.2
  exact Nat.lt_ceil.mpr ((prime_dvd_goldbachB10ProdPrimes_lt hprime hpdvd).trans_le hcover)

theorem actual_suzukiVProduct_eq_euler (N cap : ℕ) (hEven : Even N)
    (y R t : ℝ) (hcap : y ≤ (cap : ℝ))
    (hcover : y ≤ (Nat.ceil R : ℝ) ^ (1 / t)) :
    suzukiVProduct (goldbachB8PlusBoundingSieve N hEven y)
      (Nat.ceil ((Nat.ceil R : ℝ) ^ (1 / t)) : ℝ) = actualSmallEulerProduct N cap y := by
  rw [suzukiVProduct_eq_sieveProductPrimeFactors_of_all_lt]
  · exact (actualSmallEulerProduct_eq_b8_sieveProductPrimeFactors N cap hEven y hcap).symm
  · intro p hp
    exact_mod_cast actual_suzuki_cutoff_all_primes N hEven y R t hcover p hp

/-- Genuine pinned exponential control of the ACTUAL Suzuki parity sum,
uniform in the depth, target and actual finite prime carrier.  The power
budget is explicit; it is not replaced by a fixed-positive-exponent bound. -/
theorem exists_actual_goldbachT_exp_bound :
    ∃ A B K : ℝ, 0 < A ∧ 0 < B ∧ 2 ≤ K ∧
      ∀ N cap : ℕ, ∀ hEven : Even N, ∀ y R t : ℝ, ∀ depth : ℕ,
        y ≤ (cap : ℝ) → 1 < y → y ≤ R → 2 ≤ t → y ^ t ≤ R →
        t ^ 13 ≤ Real.log (Nat.ceil R : ℝ) →
        Real.exp 1 ≤ Real.log (Nat.ceil R : ℝ) → 1 ≤ depth →
        suzukiActualT (goldbachB8PlusBoundingSieve N hEven y) depth (Nat.ceil R)
            (Nat.ceil ((Nat.ceil R : ℝ) ^ (1 / t))) ≤
          actualSmallEulerProduct N cap y *
            (A * Real.exp (-t) + B * Real.exp (Real.sqrt K) * Real.exp (-t) *
              (Real.log (Nat.ceil R : ℝ)) ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨A, B, hA, hB, hsource⟩ :=
    LiLiuPrereqWF.SmallRosser.exists_actualT_exp_bound
  obtain ⟨K0, _hK0, hlocal⟩ :=
    exists_goldbachB8PlusBoundingSieve_dimensionOneLocalProductBound
  let K : ℝ := max 2 K0
  have hK : 2 ≤ K := le_max_left _ _
  have hK0 : K0 ≤ K := le_max_right _ _
  refine ⟨A, B, K, hA, hB, hK, ?_⟩
  intro N cap hEven y R t depth hcap hy hyR ht hpower hbudget hlog hdepth
  obtain ⟨hD, hcover, hz⟩ := root_covers_actual_cutoff y R t hy hyR ht hpower
  have hlocal' : HasDimensionOneLocalProductBound (goldbachB8PlusBoundingSieve N hEven y) K :=
    HasDimensionOneLocalProductBound.mono (hlocal N hEven y) hK0
  have hdom : t ∈ KappaOneModel.parityDomain 2 depth := by
    unfold KappaOneModel.parityDomain
    split_ifs <;> simp only [Set.mem_Ioi, Set.mem_Ici] <;> linarith
  have h := hsource (goldbachB8PlusBoundingSieve N hEven y) K depth (Nat.ceil R) t
    hK hlocal' hdepth hD ht hdom hbudget hlog hz
  rw [actual_suzukiVProduct_eq_euler N cap hEven y R t hcap hcover] at h
  exact h

theorem exists_actualPlus_excess_exp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N cap : ℕ, Even N → ∀ y R t : ℝ,
      y ≤ (cap : ℝ) → 1 < y → y ≤ R → 2 ≤ t → y ^ t ≤ R →
      t ^ 13 ≤ Real.log (Nat.ceil R : ℝ) →
      Real.exp 1 ≤ Real.log (Nat.ceil R : ℝ) →
      0 ≤ actualSmallRosserPlusDensity N cap y R - actualSmallEulerProduct N cap y ∧
      actualSmallRosserPlusDensity N cap y R - actualSmallEulerProduct N cap y ≤
        actualSmallEulerProduct N cap y * (C * Real.exp (-t)) := by
  obtain ⟨A, B, K, hA, hB, _hK, hsource⟩ := exists_actual_goldbachT_exp_bound
  let C : ℝ := A + B * Real.exp (Real.sqrt K)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N cap hEven y R t hcap hy hyR ht hpower hbudget hlog
  let S := goldbachB8PlusBoundingSieve N hEven y
  let D : ℕ := Nat.ceil R
  let z : ℕ := Nat.ceil ((D : ℝ) ^ (1 / t))
  obtain ⟨hD, hcover, _hz⟩ := root_covers_actual_cutoff y R t hy hyR ht hpower
  have hcut := actual_suzuki_cutoff_all_primes N hEven y R t hcover
  have hlevel : ∀ p ∈ S.prodPrimes.primeFactors, p < D := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ goldbachB10ProdPrimes N y :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
    exact Nat.lt_ceil.mpr ((prime_dvd_goldbachB10ProdPrimes_lt hprime hpdvd).trans_le hyR)
  have hexact := upperRosserSuzukiExactBridge S D z (by omega) hlevel hcut
  have hdict := actualSmallRosserPlusDensity_eq_b8_mainSum_natCeil N cap hEven y R hcap
  have hVdict := actualSmallEulerProduct_eq_b8_sieveProductPrimeFactors N cap hEven y hcap
  rw [← hdict, ← hVdict] at hexact
  have hT := hsource N cap hEven y R t (2 * S.prodPrimes.primeFactors.card + 1)
    hcap hy hyR ht hpower hbudget hlog (by omega)
  have hexp1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlogpow : (Real.log (Nat.ceil R : ℝ)) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (hexp1.trans hlog) (by norm_num)
  have herror : A * Real.exp (-t) + B * Real.exp (Real.sqrt K) * Real.exp (-t) *
      (Real.log (Nat.ceil R : ℝ)) ^ (-(1 / 3 : ℝ)) ≤ C * Real.exp (-t) := by
    calc
      _ ≤ A * Real.exp (-t) + B * Real.exp (Real.sqrt K) * Real.exp (-t) * 1 :=
        add_le_add_left (mul_le_mul_of_nonneg_left hlogpow (by positivity)) _
      _ = C * Real.exp (-t) := by dsimp [C]; ring
  have hT' := hT.trans (mul_le_mul_of_nonneg_left herror
    (actualSmallEulerProduct_pos N cap y hEven).le)
  exact ⟨actualPlus_excess_nonneg N cap hEven y R hcap hy hyR,
    by linarith only [hexact, hT']⟩

/-- The baseline is counted ZERO times.  Since both actual excesses lie
in the same interval [0,V*C*exp(-t)], their signed difference has that
same bound, with no extra V term. -/
theorem exists_actualPlus_signed_exp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N cap : ℕ, Even N → ∀ y Rold Rnew t : ℝ,
      y ≤ (cap : ℝ) → 1 < y → y ≤ Rold → y ≤ Rnew → 2 ≤ t →
      y ^ t ≤ Rold → y ^ t ≤ Rnew →
      t ^ 13 ≤ Real.log (Nat.ceil Rold : ℝ) →
      t ^ 13 ≤ Real.log (Nat.ceil Rnew : ℝ) →
      Real.exp 1 ≤ Real.log (Nat.ceil Rold : ℝ) →
      Real.exp 1 ≤ Real.log (Nat.ceil Rnew : ℝ) →
      |actualSmallRosserPlusDensity N cap y Rold - actualSmallRosserPlusDensity N cap y Rnew| ≤
        actualSmallEulerProduct N cap y * (C * Real.exp (-t)) := by
  obtain ⟨C, hC, hsource⟩ := exists_actualPlus_excess_exp_bound
  refine ⟨C, hC, ?_⟩
  intro N cap hEven y Rold Rnew t hcap hy hold hnew ht hpo hpn hbo hbn hlo hln
  have ho := hsource N cap hEven y Rold t hcap hy hold ht hpo hbo hlo
  have hn := hsource N cap hEven y Rnew t hcap hy hnew ht hpn hbn hln
  exact abs_le.mpr ⟨by linarith only [ho.1, hn.2], by linarith only [ho.2, hn.1]⟩

/-- The quantitative actual signed tail in the exact manuscript
normalization.  There is no fixed-a constant in this bound. -/
theorem exists_actualPlus_signed_normalized_exp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N cap : ℕ, 2 ≤ N → Even N → ∀ y Rold Rnew t : ℝ,
      y ≤ (cap : ℝ) → 4 ≤ y → y ≤ Rold → y ≤ Rnew → 2 ≤ t →
      y ^ t ≤ Rold → y ^ t ≤ Rnew →
      t ^ 13 ≤ Real.log (Nat.ceil Rold : ℝ) →
      t ^ 13 ≤ Real.log (Nat.ceil Rnew : ℝ) →
      Real.exp 1 ≤ Real.log (Nat.ceil Rold : ℝ) →
      Real.exp 1 ≤ Real.log (Nat.ceil Rnew : ℝ) →
      |(actualSmallRosserPlusDensity N cap y Rold - actualSmallRosserPlusDensity N cap y Rnew) *
          Real.log (N : ℝ) / singularSeries N| ≤
        C * (Real.log (N : ℝ) / Real.log y) * Real.exp (-t) := by
  obtain ⟨A, hA, hsource⟩ := exists_actualPlus_signed_exp_bound
  obtain ⟨B, hB, hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro N cap hN hEven y Rold Rnew t hcap hy hold hnew ht hpo hpn hbo hbn hlo hln
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hn
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hscale : 0 ≤ Real.log (N : ℝ) / singularSeries N :=
    div_nonneg hlogN.le (singularSeries_pos N).le
  have habs := hsource N cap hEven y Rold Rnew t hcap (by linarith) hold hnew ht
    hpo hpn hbo hbn hlo hln
  have hE := hEuler N cap (by omega) hEven y hy hcap
  calc
    |(actualSmallRosserPlusDensity N cap y Rold - actualSmallRosserPlusDensity N cap y Rnew) *
        Real.log (N : ℝ) / singularSeries N| =
        |actualSmallRosserPlusDensity N cap y Rold - actualSmallRosserPlusDensity N cap y Rnew| *
          (Real.log (N : ℝ) / singularSeries N) := by
      rw [mul_div_assoc, abs_mul, abs_of_nonneg hscale]
    _ ≤ (actualSmallEulerProduct N cap y * (A * Real.exp (-t))) *
        (Real.log (N : ℝ) / singularSeries N) := mul_le_mul_of_nonneg_right habs hscale
    _ ≤ ((B * singularSeries N / Real.log y) * (A * Real.exp (-t))) *
        (Real.log (N : ℝ) / singularSeries N) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE (by positivity)) hscale
    _ = (A * B) * (Real.log (N : ℝ) / Real.log y) * Real.exp (-t) := by
      field_simp [(singularSeries_pos N).ne', hlogy.ne'] <;> ring

/-- Common physical lower levels turn the source budgets into finite
inequalities at N.  Geometry supplies N^c <= each quotient, not a mean. -/
theorem exists_actualPlus_signed_power_budget_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N cap : ℕ, 2 ≤ N → Even N → ∀ y Rold Rnew c t : ℝ,
      y ≤ (cap : ℝ) → 4 ≤ y → 0 < c → 2 ≤ t →
      y ^ t ≤ (N : ℝ) ^ c → t ^ 13 ≤ c * Real.log (N : ℝ) →
      Real.exp 1 ≤ c * Real.log (N : ℝ) →
      (N : ℝ) ^ c ≤ Rold → (N : ℝ) ^ c ≤ Rnew →
      |(actualSmallRosserPlusDensity N cap y Rold - actualSmallRosserPlusDensity N cap y Rnew) *
          Real.log (N : ℝ) / singularSeries N| ≤
        C * (Real.log (N : ℝ) / Real.log y) * Real.exp (-t) := by
  obtain ⟨C, hC, hsource⟩ := exists_actualPlus_signed_normalized_exp_bound
  refine ⟨C, hC, ?_⟩
  intro N cap hN hEven y Rold Rnew c t hcap hy hc ht hpower hbudget hlog hold hnew
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hyPower : y ≤ y ^ t := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ y) (by linarith : (1 : ℝ) ≤ t)
  have hOldLog : c * Real.log (N : ℝ) ≤ Real.log (Nat.ceil Rold : ℝ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hn c) (hold.trans (Nat.le_ceil Rold))
    simpa only [Real.log_rpow hn] using h
  have hNewLog : c * Real.log (N : ℝ) ≤ Real.log (Nat.ceil Rnew : ℝ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hn c) (hnew.trans (Nat.le_ceil Rnew))
    simpa only [Real.log_rpow hn] using h
  exact hsource N cap hN hEven y Rold Rnew t hcap hy
    (hyPower.trans (hpower.trans hold)) (hyPower.trans (hpower.trans hnew)) ht
    (hpower.trans hold) (hpower.trans hnew) (hbudget.trans hOldLog) (hbudget.trans hNewLog)
    (hlog.trans hOldLog) (hlog.trans hNewLog)

theorem capped_parameter_power (N : ℕ) (hN : 2 ≤ N) (y c L : ℝ)
    (hy : 4 ≤ y) (hL : 2 ≤ L)
    (hs : 2 ≤ c * Real.log (N : ℝ) / Real.log y)
    (hbudget : L ^ 13 ≤ c * Real.log (N : ℝ)) :
    let t := min (c * Real.log (N : ℝ) / Real.log y) L
    2 ≤ t ∧ t ^ 13 ≤ c * Real.log (N : ℝ) ∧ y ^ t ≤ (N : ℝ) ^ c := by
  let t := min (c * Real.log (N : ℝ) / Real.log y) L
  have ht : 2 ≤ t := le_min hs hL
  have htL : t ≤ L := min_le_right _ _
  have htBudget := (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ t) htL 13).trans hbudget
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have htlog : t * Real.log y ≤ c * Real.log (N : ℝ) :=
    (le_div_iff₀ hlogy).mp (min_le_left _ _)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨ht, htBudget, ?_⟩
  rw [Real.rpow_def_of_pos (by linarith : 0 < y), Real.rpow_def_of_pos hn]
  exact Real.exp_le_exp.mpr (by nlinarith only [htlog])

/-- Exponential decay after capping the auxiliary coordinate.  This
explicit pointwise majorant is valid even if the literal residual is
beyond the source moving range. -/
theorem exists_actualPlus_signed_capped_parameter_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N cap : ℕ, 2 ≤ N → Even N → ∀ y Rold Rnew c L : ℝ,
      y ≤ (cap : ℝ) → 4 ≤ y → 0 < c → 2 ≤ L →
      2 ≤ c * Real.log (N : ℝ) / Real.log y →
      L ^ 13 ≤ c * Real.log (N : ℝ) → Real.exp 1 ≤ c * Real.log (N : ℝ) →
      (N : ℝ) ^ c ≤ Rold → (N : ℝ) ^ c ≤ Rnew →
      |(actualSmallRosserPlusDensity N cap y Rold - actualSmallRosserPlusDensity N cap y Rnew) *
          Real.log (N : ℝ) / singularSeries N| ≤
        C * (Real.log (N : ℝ) / Real.log y) *
          Real.exp (-min (c * Real.log (N : ℝ) / Real.log y) L) := by
  obtain ⟨C, hC, hsource⟩ := exists_actualPlus_signed_power_budget_bound
  refine ⟨C, hC, ?_⟩
  intro N cap hN hEven y Rold Rnew c L hcap hy hc hL hs hbudget hlog hold hnew
  have ht := capped_parameter_power N hN y c L hy hL hs hbudget
  exact hsource N cap hN hEven y Rold Rnew c _ hcap hy hc ht.1 ht.2.2 ht.2.1 hlog hold hnew

theorem exp_neg_min_le_add (x L : ℝ) :
    Real.exp (-min x L) ≤ Real.exp (-x) + Real.exp (-L) := by
  by_cases h : x ≤ L
  · rw [min_eq_left h]
    linarith [Real.exp_pos (-L)]
  · rw [min_eq_right (le_of_not_ge h)]
    linarith [Real.exp_pos (-x)]

theorem scalar_exp_tail_le_inverse (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    x * Real.exp (-(c * x)) ≤ 2 / (c ^ 2 * x) := by
  have hpow := Real.pow_div_factorial_le_exp (mul_pos hc hx).le 2
  norm_num at hpow
  have hm := mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-(c * x))).le
  have hcancel : Real.exp (c * x) * Real.exp (-(c * x)) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hcancel] at hm
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hc) hx)).mpr
  nlinarith only [hm]

/-- An actual pointwise small-cutoff majorant: a multiple of the last
log-prime coordinate, plus one explicit moving-budget remainder.  C is
absolute and is selected before c,L,N,y and both residual levels. -/
theorem exists_actualPlus_signed_linear_cutoff_majorant :
    ∃ C : ℝ, 0 < C ∧ ∀ N cap : ℕ, 2 ≤ N → Even N → ∀ y Rold Rnew c L : ℝ,
      y ≤ (cap : ℝ) → 4 ≤ y → 0 < c → 2 ≤ L →
      2 ≤ c * Real.log (N : ℝ) / Real.log y →
      L ^ 13 ≤ c * Real.log (N : ℝ) → Real.exp 1 ≤ c * Real.log (N : ℝ) →
      (N : ℝ) ^ c ≤ Rold → (N : ℝ) ^ c ≤ Rnew →
      |(actualSmallRosserPlusDensity N cap y Rold - actualSmallRosserPlusDensity N cap y Rnew) *
          Real.log (N : ℝ) / singularSeries N| ≤
        (2 * C / c ^ 2) * (Real.log y / Real.log (N : ℝ)) +
          (C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L) := by
  obtain ⟨C, hC, hsource⟩ := exists_actualPlus_signed_capped_parameter_bound
  refine ⟨C, hC, ?_⟩
  intro N cap hN hEven y Rold Rnew c L hcap hy hc hL hs hbudget hlog hold hnew
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hn
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  let x : ℝ := Real.log (N : ℝ) / Real.log y
  have hx : 0 < x := div_pos hlogN hlogy
  have hratio : c * Real.log (N : ℝ) / Real.log y = c * x := by dsimp [x]; ring
  have habs := hsource N cap hN hEven y Rold Rnew c L hcap hy hc hL hs hbudget hlog hold hnew
  rw [hratio] at habs
  have hFirst : C * x * Real.exp (-(c * x)) ≤
      (2 * C / c ^ 2) * (Real.log y / Real.log (N : ℝ)) := by
    calc
      C * x * Real.exp (-(c * x)) = C * (x * Real.exp (-(c * x))) := by ring
      _ ≤ C * (2 / (c ^ 2 * x)) :=
        mul_le_mul_of_nonneg_left (scalar_exp_tail_le_inverse c x hc hx) hC.le
      _ = _ := by
        dsimp [x]
        field_simp [hc.ne', hlogN.ne', hlogy.ne'] <;> ring
  have hxUpper : x ≤ Real.log (N : ℝ) / Real.log 4 :=
    div_le_div_of_nonneg_left hlogN.le hlog4
      (Real.log_le_log (by norm_num : (0 : ℝ) < 4) hy)
  have hLast : C * x * Real.exp (-L) ≤
      (C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L) := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hxUpper hC.le) (Real.exp_pos (-L)).le
    calc
      _ ≤ (C * (Real.log (N : ℝ) / Real.log 4)) * Real.exp (-L) := h
      _ = _ := by ring
  calc
    _ ≤ C * x * Real.exp (-min (c * x) L) := habs
    _ ≤ C * x * (Real.exp (-(c * x)) + Real.exp (-L)) :=
      mul_le_mul_of_nonneg_left (exp_neg_min_le_add (c * x) L) (mul_pos hC hx).le
    _ = C * x * Real.exp (-(c * x)) + C * x * Real.exp (-L) := by ring
    _ ≤ _ := add_le_add hFirst hLast

/-- The only sub-four ACTUAL prime cutoff for an even target is three;
below or at three the actual carrier is empty and the signed difference
vanishes identically.  There is no missing tiny-cutoff baseline term. -/
theorem actualPlus_sub_eq_zero_of_cutoff_le_three (N cap : ℕ) (hEven : Even N)
    (y Rold Rnew : ℝ) (hcap : y ≤ (cap : ℝ)) (hy : 1 < y) (hy3 : y ≤ 3)
    (hold : y ≤ Rold) (hnew : y ≤ Rnew) :
    actualSmallRosserPlusDensity N cap y Rold - actualSmallRosserPlusDensity N cap y Rnew = 0 := by
  have hempty : actualSmallPrimeFinset N cap y = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro p hp
    have hp3 : 3 ≤ p := by
      have hp2 := (actualSmallPrimeFinset_odd_of_even hEven hp).2
      omega
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hpy := (mem_actualSmallPrimeFinset.mp hp).2.2.2
    linarith
  rw [actualPlus_sub_eq_euler_mul_boundary_sub N cap hEven y Rold Rnew hcap hy hold hnew]
  simp [boundaryExcess, hempty]

/-- A genuinely small cutoff gives the required long residual coordinate
from its finite power inequality.  The majorant constant does not depend
on this a. -/
theorem parameter_lower_of_small_power_cutoff (N : ℕ) (hN : 2 ≤ N)
    (y a c : ℝ) (hy : 1 < y) (hac : 2 * a ≤ c)
    (hcut : y ≤ (N : ℝ) ^ a) :
    2 ≤ c * Real.log (N : ℝ) / Real.log y := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hn
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hcutLog := Real.log_le_log (zero_lt_one.trans hy) hcut
  rw [Real.log_rpow (zero_lt_one.trans hn)] at hcutLog
  apply (le_div_iff₀ hlogy).mpr
  nlinarith only [hcutLog, mul_le_mul_of_nonneg_right hac hlogN.le]

open HistoricalThirdCoarse.P1OriginalUpperResidual in
/-- The actual original raw Q3 and checked Q4 receive the same absolute
constant, selected before the original policy and all its finite tables.
Only the finite geometric lower gap and the explicit source budget enter
as inputs.  In particular no positive lower cutoff a or mean bound is
an input.  The checked level comparison transfers the old gap to Q4. -/
theorem exists_original_signed_linear_cutoff_majorant :
    ∃ C : ℝ, 0 < C ∧ ∀ N cap : ℕ, 2 ≤ N → Even N →
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega rho : ℝ)
        (J4 : Finset (P1OriginalCoarseContinuation.FourthCell m))
        (cap4 : P1OriginalCoarseContinuation.FourthCell m → ℚ),
        P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true →
        ∀ p ∈ admittedTuples (e : ℝ) chi m omega rho N cap, ∀ c L : ℝ,
          4 ≤ (p 3 : ℝ) → 0 < c → 2 ≤ L →
          2 ≤ c * Real.log (N : ℝ) / Real.log (p 3 : ℝ) →
          L ^ 13 ≤ c * Real.log (N : ℝ) → Real.exp 1 ≤ c * Real.log (N : ℝ) →
          (N : ℝ) ^ c ≤ oldLevel (e : ℝ) chi m omega N p / (∏ i, p i : ℕ) →
          |normalizedResidual N cap p (oldLevel (e : ℝ) chi m omega N p) -
              normalizedResidual N cap p (newLevel e chi m omega J4 cap4 N p)| ≤
            (2 * C / c ^ 2) * actualPrimeTupleLog N p 3 +
              (C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L) := by
  obtain ⟨C, hC, hsource⟩ := exists_actualPlus_signed_linear_cutoff_majorant
  refine ⟨C, hC, ?_⟩
  intro N cap hN hEven e chi m omega rho J4 cap4 hcheck p hp c L hy hc hL hs
    hbudget hlog hold
  have hN1 : 1 < N := by omega
  have hcap := (admitted_last_bounds (e : ℝ) chi m omega rho N cap hN1 p hp).2
  have hlevels := oldLevel_le_newLevel e chi m omega rho J4 cap4 hcheck N cap hN1 p hp
  have hnew : (N : ℝ) ^ c ≤ newLevel e chi m omega J4 cap4 N p / (∏ i, p i : ℕ) :=
    hold.trans (div_le_div_of_nonneg_right hlevels (Nat.cast_nonneg _))
  have h := hsource N cap hN hEven (p 3 : ℝ)
    (oldLevel (e : ℝ) chi m omega N p / (∏ i, p i : ℕ))
    (newLevel e chi m omega J4 cap4 N p / (∏ i, p i : ℕ))
    c L hcap hy hc hL hs hbudget hlog hold hnew
  simpa only [normalizedResidual, actualPrimeTupleLog, sub_mul, sub_div] using h

end
end ImbalancedChen.P1OriginalSmallCutoffActualTail
