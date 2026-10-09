import ImbalancedChen.ActualOptimizedSieveBound
import ImbalancedChen.EnlargedSelbergCap
import ImbalancedChen.FullNormalizerCarrier
import ImbalancedChen.HalfProductMassLimit

/-!
# Conditional analytic composition for the original bad count

For each fixed rational `1/2 < b = num/den < 1` and fixed
`2/5 < theta < 1/2`, the actual bad count is eventually at most
`((4/theta) * log(1/b) + epsilon) * singularNormalization N` on even centres.

The independent upstream inputs are stated literally: real PNT, the
fixed-test weighted-prime Mertens limit, the limit of the full arithmetic
Selberg normalizer times the genuine singular series divided by `log N`,
and the summed primitive discrepancy at accuracy `22 = 2*3 + 16`.
No estimate for `B` or for the sifted count is an input.

The exact level is `floor(N^(theta/2))`, its strict cap is `L+1`, the
original real cutoff is `logCutoff N`, and the finite error uses level
`L*L`. The normalizer limit is along the even filter and equals `theta/4`,
with no extra factor two. The square-root error is proved negligible using
the positive genuine twin-prime constant. The exact finite optimized sieve,
full-carrier identity, roughness gate, and paid localization losses give
the final result. All eventual thresholds are chosen after fixing theta.

This is a conditional supplier composition. It neither supplies the
independent analytic hypotheses nor asserts distribution at theta = 1/2,
and it makes no claim concerning the refined coefficient 6.786.
-/

namespace ImbalancedChen

noncomputable section

open Filter Asymptotics Topology
open scoped BigOperators

/-- The actual squared coefficient level is within the ambient source
size for subunit exponents. The stronger floor level is retained. -/
theorem enlargedSelbergLevel_mul_self_le_center {theta : ℝ}
    (htheta : theta ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    enlargedSelbergLevel theta N * enlargedSelbergLevel theta N ≤ N := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpower : (N : ℝ) ^ theta ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNreal htheta
  have hfloor : (Nat.floor ((N : ℝ) ^ theta) : ℝ) ≤ (N : ℝ) :=
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) theta)).trans hpower
  exact (enlargedSelbergLevel_mul_self_le_floor theta N).trans
    (by exact_mod_cast hfloor)

/-- Passing from the usual full power level to the exact squared natural
level costs nothing: every summand is a nonnegative absolute discrepancy. -/
theorem enlargedSelberg_primitive_discrepancy_le_floor
    (num den N : ℕ) (T theta : ℝ) :
    (∑ d ∈ Finset.Icc 1
        (enlargedSelbergLevel theta N * enlargedSelbergLevel theta N)
        with Nat.Coprime d N,
      |halfProductCongruenceMass num den N T d -
        halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)|) ≤
    ∑ d ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ theta)) with Nat.Coprime d N,
      |halfProductCongruenceMass num den N T d -
        halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)| := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hdIcc, hcop⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdpos, hdlevel⟩ := Finset.mem_Icc.mp hdIcc
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hdpos, hdlevel.trans (enlargedSelbergLevel_mul_self_le_floor theta N)⟩, hcop⟩
  · intro d _ _
    exact abs_nonneg _

/-- The exact accuracy-three square-root error is a fixed constant times
`N/log(N)^3`. The sign hypotheses remove both absolute-value ambiguities. -/
theorem selberg_sqrt_log_error_eq {K : ℝ} (hK : 0 ≤ K)
    {N : ℕ} (hlog : 0 < Real.log (N : ℝ)) :
    Real.sqrt (K * (N : ℝ) ^ 2 / (Real.log (N : ℝ)) ^ 6) =
      Real.sqrt K * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
  have hden : ((Real.log (N : ℝ)) ^ 3) ^ 2 =
      (Real.log (N : ℝ)) ^ 6 := by ring
  calc
    Real.sqrt (K * (N : ℝ) ^ 2 / (Real.log (N : ℝ)) ^ 6) =
        Real.sqrt ((Real.sqrt K * (N : ℝ) / (Real.log (N : ℝ)) ^ 3) ^ 2) := by
      congr 1
      rw [div_pow, mul_pow, Real.sq_sqrt hK, hden]
    _ = _ := Real.sqrt_sq (by positivity)

/-- Accuracy three is sufficient for a negligible weighted sieve error
in the genuine normalization. This uses `C_2 > 0`, not an assumed lower
bound or an upper bound for the moving singular series. -/
theorem eventually_selberg_sqrt_error_le_singularNormalization
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        Real.sqrt (K * (N : ℝ) ^ 2 / (Real.log (N : ℝ)) ^ 6) ≤
          epsilon * singularNormalization N := by
  intro epsilon hepsilon
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun N : ℕ => Real.sqrt K / Real.log (N : ℝ))
      atTop (𝓝 0) := hloglim.const_div_atTop (Real.sqrt K)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      Real.sqrt K / Real.log (N : ℝ) < epsilon * twinPrimeConstant :=
    hdecay.eventually (gt_mem_nhds (mul_pos hepsilon twinPrimeConstant_pos))
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℕ)] with N hsmallN hN
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNreal
  have hbase : 0 ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by positivity
  calc
    Real.sqrt (K * (N : ℝ) ^ 2 / (Real.log (N : ℝ)) ^ 6) =
        (Real.sqrt K / Real.log (N : ℝ)) *
          ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
      rw [selberg_sqrt_log_error_eq hK hlog]
      field_simp [hlog.ne'] <;> ring
    _ ≤ (epsilon * twinPrimeConstant) *
        ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_right hsmallN.le hbase
    _ = epsilon *
        (twinPrimeConstant * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by ring
    _ ≤ epsilon * singularNormalization N :=
      mul_le_mul_of_nonneg_left (singularNormalization_lower N) hepsilon.le

/-- Exact algebra behind the normalization of the finite main term.
The normalizer can even vanish: its totalized division then vanishes on
both sides. No estimate for this denominator is hidden in the identity. -/
theorem selberg_mainTerm_eq_normalized_ratio
    (mass G : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    mass / G =
      ((mass / ((N : ℝ) / Real.log (N : ℝ))) /
        (G * singularSeries N / Real.log (N : ℝ))) * singularNormalization N := by
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans hNreal
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hNreal).ne'
  have hseries : singularSeries N ≠ 0 := (singularSeries_pos N).ne'
  by_cases hG : G = 0
  · simp [hG]
  · unfold singularNormalization
    field_simp [hG, hNpos.ne', hlog, hseries] <;> ring

/-- The independent mass and full-normalizer limits give the exact
coefficient `4/theta`. This intermediate statement concerns only the
finite main term and is not a premise of the final count theorem. -/
theorem eventually_enlargedSelberg_mainTerm_le
    {num den : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (hMass : Tendsto (fun N : ℕ =>
      ((halfProductSource num den N (logCutoff N)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)))
      atTop (𝓝 (Real.log (1 / ((num : ℝ) / (den : ℝ))))))
    (hNormalizer : Tendsto (fun N : ℕ =>
      fullSelbergNormalizer N (enlargedSelbergLevel theta N) *
        singularSeries N / Real.log (N : ℝ))
      (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 (theta / 4))) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N →
        ((halfProductSource num den N (logCutoff N)).card : ℝ) /
          fullSelbergNormalizer N (enlargedSelbergLevel theta N) ≤
        ((4 / theta) * Real.log (1 / ((num : ℝ) / (den : ℝ))) + epsilon) *
          singularNormalization N := by
  intro epsilon hepsilon
  have hquot := (hMass.mono_left inf_le_left).div hNormalizer
    (ne_of_gt (by positivity : 0 < theta / 4))
  have hcoefficient : Real.log (1 / ((num : ℝ) / (den : ℝ))) / (theta / 4) =
      (4 / theta) * Real.log (1 / ((num : ℝ) / (den : ℝ))) := by
    field_simp [htheta.ne'] <;> ring
  rw [hcoefficient] at hquot
  have hsmall := hquot.eventually (gt_mem_nhds
    (lt_add_of_pos_right ((4 / theta) *
      Real.log (1 / ((num : ℝ) / (den : ℝ)))) hepsilon))
  rw [Filter.eventually_inf_principal] at hsmall
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℕ),
    eventually_singularNormalization_pos] with N hsmallN hN hH hEven
  rw [selberg_mainTerm_eq_normalized_ratio _ _ hN]
  exact mul_le_mul_of_nonneg_right (hsmallN hEven).le hH.le

/-- Fixed-theta conditional upper bound for the original `B`, from the
literal primitive discrepancy at the exact `L*L` level. The only analytic
premises are independent real PNT, weighted Mertens, the arithmetic full
normalizer limit, and accuracy-22 primitive-source distribution. -/
theorem eventually_B_le_enlargedSelberg_of_analytic_inputs
    (hPNT : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ, (Nat.primeCounting (Nat.floor x) : ℝ) =
        (1 + c x) * x / Real.log x)
    {num den : ℕ} (hden : 0 < den) (hhalf : den < 2 * num) (hnumden : num < den)
    {theta : ℝ} (hthetaLower : 2 / 5 < theta) (hthetaUpper : theta < 1 / 2)
    (hMertens : Tendsto (fun N : ℕ =>
      ∑ r ∈ halfProductHighPrimes N
          (Nat.floor ((N : ℝ) ^ halfProductMassAlpha num den)),
        (1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ))
      atTop (𝓝 (Real.log (1 / ((num : ℝ) / (den : ℝ))))))
    (hNormalizer : Tendsto (fun N : ℕ =>
      fullSelbergNormalizer N (enlargedSelbergLevel theta N) *
        singularSeries N / Real.log (N : ℝ))
      (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 (theta / 4)))
    (hDistribution : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, Even N →
        (∑ d ∈ Finset.Icc 1
            (enlargedSelbergLevel theta N * enlargedSelbergLevel theta N)
            with Nat.Coprime d N,
          |halfProductCongruenceMass num den N (logCutoff N) d -
            halfProductCoprimeMass num den N (logCutoff N) d / (Nat.totient d : ℝ)|) ≤
          C * (N : ℝ) / (Real.log (N : ℝ)) ^ 22) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N →
        (B num den N : ℝ) ≤
          ((4 / theta) * Real.log (1 / ((num : ℝ) / (den : ℝ))) + epsilon) *
            singularNormalization N := by
  have hnum : 0 < num := by omega
  have htheta : 0 < theta := by linarith
  have hMass := tendsto_halfProductSource_logCutoff_mass_of_real_pnt_and_weighted_mertens
    hPNT hnum hnumden hMertens
  obtain ⟨C, hC, hDistribution⟩ := hDistribution
  intro epsilon hepsilon
  have hthird : 0 < epsilon / 3 := by positivity
  have hlogLarge : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards
    [eventually_enlargedSelberg_mainTerm_le htheta hMass hNormalizer
      (epsilon / 3) hthird,
      eventually_selberg_sqrt_error_le_singularNormalization (3 * (8 : ℝ) ^ 16 * C)
        (by positivity) (epsilon / 3) hthird,
      eventually_enlargedSelbergCap_data num den hden hhalf hnumden
        hthetaLower hthetaUpper (epsilon / 3) hthird,
      hDistribution, hlogLarge, eventually_ge_atTop (2 : ℕ)]
    with N hmain herr hdata hdist hlog hN hEven
  obtain ⟨hL, _hsquaredFloor, hT, hcap, _hpaidLoss, hB⟩ := hdata
  have hlevel : enlargedSelbergLevel theta N * enlargedSelbergLevel theta N ≤ N :=
    enlargedSelbergLevel_mul_self_le_center (by linarith) (by omega)
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hfinite := siftedHalfProductSource_card_le_optimized_of_unweighted_logBound
    num den N (logCutoff N) (enlargedSelbergCap theta N) hEven
    hnum hden hT hcap (enlargedSelbergLevel theta N) 3 hL hlevel hNreal hlog
    C hC (by simpa only [show 2 * (3 : ℕ) + 16 = 22 by norm_num] using hdist hEven)
  have hcarrier :
      (∑ d ∈ (sieveProduct N (enlargedSelbergCap theta N)).divisors
          with d ≤ enlargedSelbergLevel theta N,
        ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2)) =
      fullSelbergNormalizer N (enlargedSelbergLevel theta N) := by
    unfold fullSelbergNormalizer
    rw [sieveProduct_divisors_filter_eq_fullCarrier
      (enlargedSelbergLevel_lt_cap theta N)]
  rw [hcarrier] at hfinite
  simp only [show 2 * (3 : ℕ) = 6 by norm_num] at hfinite
  have hmainN := hmain hEven
  nlinarith only [hB, hfinite, hmainN, herr]

/-- Usual-power-level version of the same complete composition. The
supplied discrepancy is explicit up to `floor(N^theta)`; the finite sieve
still uses its exact proved level `floor(N^(theta/2))^2`, never a larger one. -/
theorem eventually_B_le_enlargedSelberg_of_floor_analytic_inputs
    (hPNT : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ, (Nat.primeCounting (Nat.floor x) : ℝ) =
        (1 + c x) * x / Real.log x)
    {num den : ℕ} (hden : 0 < den) (hhalf : den < 2 * num) (hnumden : num < den)
    {theta : ℝ} (hthetaLower : 2 / 5 < theta) (hthetaUpper : theta < 1 / 2)
    (hMertens : Tendsto (fun N : ℕ =>
      ∑ r ∈ halfProductHighPrimes N
          (Nat.floor ((N : ℝ) ^ halfProductMassAlpha num den)),
        (1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ))
      atTop (𝓝 (Real.log (1 / ((num : ℝ) / (den : ℝ))))))
    (hNormalizer : Tendsto (fun N : ℕ =>
      fullSelbergNormalizer N (enlargedSelbergLevel theta N) *
        singularSeries N / Real.log (N : ℝ))
      (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 (theta / 4)))
    (hDistribution : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, Even N →
        (∑ d ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ theta)) with Nat.Coprime d N,
          |halfProductCongruenceMass num den N (logCutoff N) d -
            halfProductCoprimeMass num den N (logCutoff N) d / (Nat.totient d : ℝ)|) ≤
          C * (N : ℝ) / (Real.log (N : ℝ)) ^ 22) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N →
        (B num den N : ℝ) ≤
          ((4 / theta) * Real.log (1 / ((num : ℝ) / (den : ℝ))) + epsilon) *
            singularNormalization N := by
  apply eventually_B_le_enlargedSelberg_of_analytic_inputs
    hPNT hden hhalf hnumden hthetaLower hthetaUpper hMertens hNormalizer
  obtain ⟨C, hC, hdist⟩ := hDistribution
  refine ⟨C, hC, hdist.mono ?_⟩
  intro N hN hEven
  exact (enlargedSelberg_primitive_discrepancy_le_floor
    num den N (logCutoff N) theta).trans (hN hEven)

/-- Supplying the independent analytic inputs for every fixed interior
`theta` gives coefficient eight by the correct order of limits. For each
epsilon, one interior theta is chosen first; only then is the eventual
threshold obtained. No distribution or normalizer claim at the endpoint
`theta = 1/2` is required. -/
theorem eventually_B_le_eight_of_enlargedSelberg_analytic_inputs
    (hPNT : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ, (Nat.primeCounting (Nat.floor x) : ℝ) =
        (1 + c x) * x / Real.log x)
    {num den : ℕ} (hden : 0 < den) (hhalf : den < 2 * num) (hnumden : num < den)
    (hMertens : Tendsto (fun N : ℕ =>
      ∑ r ∈ halfProductHighPrimes N
          (Nat.floor ((N : ℝ) ^ halfProductMassAlpha num den)),
        (1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ))
      atTop (𝓝 (Real.log (1 / ((num : ℝ) / (den : ℝ))))))
    (hNormalizers : ∀ theta : ℝ, 2 / 5 < theta → theta < 1 / 2 →
      Tendsto (fun N : ℕ =>
        fullSelbergNormalizer N (enlargedSelbergLevel theta N) *
          singularSeries N / Real.log (N : ℝ))
        (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 (theta / 4)))
    (hDistributions : ∀ theta : ℝ, 2 / 5 < theta → theta < 1 / 2 →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ N : ℕ in atTop, Even N →
          (∑ d ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ theta)) with Nat.Coprime d N,
            |halfProductCongruenceMass num den N (logCutoff N) d -
              halfProductCoprimeMass num den N (logCutoff N) d / (Nat.totient d : ℝ)|) ≤
            C * (N : ℝ) / (Real.log (N : ℝ)) ^ 22) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N →
        (B num den N : ℝ) ≤
          (8 * Real.log (1 / ((num : ℝ) / (den : ℝ))) + epsilon) *
            singularNormalization N := by
  intro epsilon hepsilon
  let ell : ℝ := Real.log (1 / ((num : ℝ) / (den : ℝ)))
  have hnum : 0 < num := by omega
  have hbpos : 0 < (num : ℝ) / (den : ℝ) :=
    div_pos (Nat.cast_pos.mpr hnum) (Nat.cast_pos.mpr hden)
  have hblt : (num : ℝ) / (den : ℝ) < 1 :=
    (div_lt_one (Nat.cast_pos.mpr hden)).mpr (Nat.cast_lt.mpr hnumden)
  have hell : 0 < ell := Real.log_pos ((one_lt_div hbpos).mpr hblt)
  have hdenom : 0 < 8 * ell + epsilon / 2 := by positivity
  have hratio : 4 * ell / (8 * ell + epsilon / 2) < 1 / 2 := by
    apply (div_lt_iff₀ hdenom).mpr
    linarith
  have hmax : max (2 / 5 : ℝ) (4 * ell / (8 * ell + epsilon / 2)) < 1 / 2 :=
    max_lt (by norm_num) hratio
  obtain ⟨theta, hthetaMax, hthetaUpper⟩ := exists_between hmax
  have hthetaLower : 2 / 5 < theta :=
    (le_max_left _ _).trans_lt hthetaMax
  have hthetaPos : 0 < theta := by linarith
  have hthetaRatio : 4 * ell / (8 * ell + epsilon / 2) < theta :=
    (le_max_right _ _).trans_lt hthetaMax
  have hproduct : 4 * ell < theta * (8 * ell + epsilon / 2) :=
    (div_lt_iff₀ hdenom).mp hthetaRatio
  have hcoefficient : (4 / theta) * ell < 8 * ell + epsilon / 2 := by
    have hdiv : (4 * ell) / theta < 8 * ell + epsilon / 2 :=
      (div_lt_iff₀ hthetaPos).mpr (by nlinarith only [hproduct])
    calc
      (4 / theta) * ell = (4 * ell) / theta := by ring
      _ < _ := hdiv
  have hfixed := eventually_B_le_enlargedSelberg_of_floor_analytic_inputs
    hPNT hden hhalf hnumden hthetaLower hthetaUpper hMertens
    (hNormalizers theta hthetaLower hthetaUpper)
    (hDistributions theta hthetaLower hthetaUpper)
    (epsilon / 2) (half_pos hepsilon)
  filter_upwards [hfixed, eventually_singularNormalization_pos] with N hN hH hEven
  calc
    (B num den N : ℝ) ≤ ((4 / theta) * ell + epsilon / 2) *
        singularNormalization N := hN hEven
    _ ≤ (8 * ell + epsilon) * singularNormalization N :=
      mul_le_mul_of_nonneg_right (by linarith) hH.le

end

end ImbalancedChen
