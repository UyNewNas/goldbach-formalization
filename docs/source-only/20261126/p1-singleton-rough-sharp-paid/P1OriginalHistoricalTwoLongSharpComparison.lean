import ImbalancedChen.P1OriginalHistoricalTwoLongRoughComparison
import ImbalancedChen.P4BOriginalSharpPairComparison
import ImbalancedChen.P4BOriginalSharpEndpointPrices

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

Historical P1 sharp-strip comparison at the original finite modulus set
and signed coefficient. The original sharp_pair_point, stripPairMean_point,
polynomial_P2 supplier and historical reciprocal moments are invoked.
The strip mean keeps 32*delta*U*V*densityLog(x)^2 before the modulus sum,
with one totient inverse and twice the two exact coprime means.

The final local price has external logarithmic orders 24, 26, 25+2B,
24+4B. The leading term uses M*U*V=x and the small strip integral; its
order 26 is independent of B. Only the other errors contain derivative
losses. No lower bound U,V >= x^(1/3), P4 endpoint terminal, scalar
payment premise, error premise or short-mass premise is introduced.

All imported source-availability and unique-owner obligations remain.
No sharp native-mode/Fourier/outer-HB conclusion is asserted here.
-/

namespace ImbalancedChen.P1OriginalHistoricalTwoLongSharpComparison
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open P1OriginalHistoricalTwoLongP2
open P1OriginalHistoricalTwoLongRoughComparison
open P4BOriginalRoughPairFinite (roughDelta polyDelta)
open P4BOriginalSharpLongProfiles
  (stripProfile stripProfile_support stripPrice stripPrice_nonneg sharpProfile)
open P4BOriginalSharpStripMean (stripPairMean stripPairMean_point)
open P4BOriginalSharpPairComparison (sharp_pair_point)
open P4BOriginalEnvelopePolynomialPayment (p2Price p2Price_nonneg)
open P4BOriginalPairMeanNorm (densityLog densityLog_one_le)
open P4BOriginalE3LogPrices (primary_price)
open P4BOriginalSharpEndpointPrices
  (sizeConstant sizeConstant_nonneg log_product_bound)
open Part3.TwoLongTransitionMellinN2 (profile logSize logSize_one_le)
open Part3.TwoLongHBMellinBrunProfiles (pairCost pairCost_nonneg)
open Part3.TwoLongActualLowerCorePayment (moment_log_budget short_log_budget)
open Part3.TwoLongActualHBShortMass
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ActualRoughHeathBrownWords (Role)

/-- Only finite summation is new: the current strip integral, nonunit
short branch and single totient inverse are in stripPairMean_point. -/
theorem historical_strip_mean_sum
    (B : ℝ) (old fresh : List ℕ → Bool) (N cap D : ℕ) (w z L : ℝ)
    (hlevel : ∀ q ∈ historicalModuli B old fresh N cap w z, q ≤ D)
    {delta U V Z x : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 < U) (hV : 0 < V) (hZ : 1 ≤ Z) (hx : 1 ≤ x)
    (j : ℕ) (hy : Z^(2*j+1) ≤ x) (Mset : Finset ℕ) (alpha : ℕ → ℂ) :
    (∑ q ∈ historicalModuli B old fresh N cap w z,
      ‖historicalRho old fresh N cap w z L q‖ * ∑ short ∈ Mset,
        2*‖alpha short‖*stripPairMean hd hs U V Z j q short) ≤
      2*(∑ short ∈ Mset, ‖alpha short‖)*reciprocalMoment D*
        (32*delta*U*V*(densityLog x)^2 +
          4*stripPrice/delta^2*(U+V)*Z^(2*j+1)*densityLog x +
          2*stripPrice^2/delta^4*(Z^(2*j+1))^2) := by
  let Q := historicalModuli B old fresh N cap w z
  let c := historicalRho old fresh N cap w z L
  let μ := ∑ short ∈ Mset, ‖alpha short‖
  let Y := Z^(2*j+1)
  let a₀ := 32*delta*U*V*(densityLog x)^2
  let a₁ := 4*stripPrice/delta^2*(U+V)*Y*densityLog x
  let a₂ := 2*stripPrice^2/delta^4*Y^2
  have hμ : 0 ≤ μ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hY : 0 ≤ Y := pow_nonneg (zero_le_one.trans hZ) _
  have hlog : 0 ≤ densityLog x := zero_le_one.trans (densityLog_one_le hx)
  have hP := stripPrice_nonneg
  have ha₀ : 0 ≤ a₀ := by dsimp only [a₀]; positivity
  have ha₁ : 0 ≤ a₁ := by dsimp only [a₁]; positivity
  have ha₂ : 0 ≤ a₂ := by dsimp only [a₂]; positivity
  have hinner (q : ℕ) (hq : q ∈ Q) :
      (∑ short ∈ Mset, 2*‖alpha short‖*stripPairMean hd hs U V Z j q short) ≤
        2*μ*(a₀+a₁*(q.divisors.card : ℝ)+a₂*(q.divisors.card : ℝ)^2)/(q.totient : ℝ) := by
    have hqpos := (historical_modulus_class B old fresh N cap w z L hq).1
    calc
      _ ≤ ∑ short ∈ Mset, ‖alpha short‖ *
          (2*(a₀+a₁*(q.divisors.card : ℝ)+a₂*(q.divisors.card : ℝ)^2)/(q.totient : ℝ)) := by
        apply Finset.sum_le_sum
        intro short hshort
        have hp := mul_le_mul_of_nonneg_left
          (stripPairMean_point hd hs hU hV hZ hx j q short hqpos hy)
          (show 0 ≤ 2*‖alpha short‖ by positivity)
        exact hp.trans_eq (by dsimp only [a₀, a₁, a₂, Y]; ring)
      _ = μ*(2*(a₀+a₁*(q.divisors.card : ℝ)+a₂*(q.divisors.card : ℝ)^2)/(q.totient : ℝ)) := by
        dsimp only [μ]
        rw [Finset.sum_mul]
      _ = _ := by ring
  have h₀ := historical_tau_moment B old fresh N cap D w z L hlevel 0 (by norm_num)
  have h₁ := historical_tau_moment B old fresh N cap D w z L hlevel 1 (by norm_num)
  have h₂ := historical_tau_moment B old fresh N cap D w z L hlevel 2 (by norm_num)
  have hsum := add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₀ ha₀)
    (mul_le_mul_of_nonneg_left h₁ ha₁)) (mul_le_mul_of_nonneg_left h₂ ha₂)
  have heq : (∑ q ∈ Q, ‖c q‖ *
      (a₀+a₁*(q.divisors.card : ℝ)+a₂*(q.divisors.card : ℝ)^2)/(q.totient : ℝ)) =
      a₀*(∑ q ∈ Q, ‖c q‖*(q.divisors.card : ℝ)^0/(q.totient : ℝ)) +
      a₁*(∑ q ∈ Q, ‖c q‖*(q.divisors.card : ℝ)^1/(q.totient : ℝ)) +
      a₂*(∑ q ∈ Q, ‖c q‖*(q.divisors.card : ℝ)^2/(q.totient : ℝ)) := by
    simp only [Finset.mul_sum, ←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  calc
    _ ≤ ∑ q ∈ Q, ‖c q‖ *
        (2*μ*(a₀+a₁*(q.divisors.card : ℝ)+a₂*(q.divisors.card : ℝ)^2)/(q.totient : ℝ)) :=
      Finset.sum_le_sum (fun q hq => mul_le_mul_of_nonneg_left (hinner q hq) (norm_nonneg _))
    _ = 2*μ*(∑ q ∈ Q, ‖c q‖ *
        (a₀+a₁*(q.divisors.card : ℝ)+a₂*(q.divisors.card : ℝ)^2)/(q.totient : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ 2*μ*((a₀+a₁+a₂)*reciprocalMoment D) := by
      rw [heq]
      exact mul_le_mul_of_nonneg_left (hsum.trans_eq (by ring)) (by positivity)
    _ = _ := by dsimp only [μ, a₀, a₁, a₂, Y]; ring

/-- The finite bill retains the small integral in its leading mean. -/
def endpointInvoice {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (U V x Y μ : ℝ) (D : ℕ) : ℝ :=
  logSize U*logSize V*
    ((p2Price (stripProfile true hd hs U) (stripProfile false hd hs V) +
        p2Price (stripProfile false hd hs U) (stripProfile true hd hs V))*
        (Y^2*μ)*momentBudget D +
      2*μ*reciprocalMoment D*
        (32*delta*U*V*(densityLog x)^2 +
          4*stripPrice/delta^2*(U+V)*Y*densityLog x +
          2*stripPrice^2/delta^4*Y^2))

theorem endpointInvoice_mono {delta U V x Y μ ν : ℝ}
    (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hx : 1 ≤ x) (hY : 0 ≤ Y)
    (D : ℕ) (hμ : μ ≤ ν) :
    endpointInvoice hd hs U V x Y μ D ≤ endpointInvoice hd hs U V x Y ν D := by
  have hL := mul_nonneg (zero_le_one.trans (logSize_one_le U))
    (zero_le_one.trans (logSize_one_le V))
  have hP := add_nonneg
    (p2Price_nonneg (stripProfile true hd hs U) (stripProfile false hd hs V))
    (p2Price_nonneg (stripProfile false hd hs U) (stripProfile true hd hs V))
  have hm := momentBudget_nonneg D
  have hr := reciprocalMoment_nonneg D
  have hp := stripPrice_nonneg
  have hl := zero_le_one.trans (densityLog_one_le hx)
  have hb : 0 ≤ 32*delta*U*V*(densityLog x)^2 +
      4*stripPrice/delta^2*(U+V)*Y*densityLog x +
      2*stripPrice^2/delta^4*Y^2 := by positivity
  unfold endpointInvoice
  apply mul_le_mul_of_nonneg_left _ hL
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hμ (sq_nonneg Y)) hP) hm
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hμ (by norm_num)) hr) hb

/-- Original signed historical Q/rho, arbitrary finite short support and
frequencies. The analytic sharp and strip estimates are existing APIs. -/
theorem historical_finite_endpoint_invoice
    (B : ℝ) (old fresh : List ℕ → Bool) (N cap D : ℕ) (w z L : ℝ)
    (hlevel : ∀ q ∈ historicalModuli B old fresh N cap w z, q ≤ D)
    (log₁ log₂ : Bool) {delta U V Z x : ℝ}
    (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 < U) (hV : 0 < V) (hZ : 1 ≤ Z) (hx : 1 ≤ x)
    (t₁ t₂ : ℝ) (j : ℕ) (hy : Z^(2*j+1) ≤ x)
    (Mset : Finset ℕ) (alpha : ℕ → ℂ) :
    ‖historicalRoughSum B old fresh N cap w z L
        (sharpProfile log₁ U t₁) (sharpProfile log₂ V t₂) U V Z Mset alpha -
      historicalRoughSum B old fresh N cap w z L
        (profile false log₁ delta U t₁) (profile false log₂ delta V t₂) U V Z Mset alpha‖ ≤
      endpointInvoice hd hs U V x (Z^(2*j+1)) (∑ short ∈ Mset, ‖alpha short‖) D := by
  let Q := historicalModuli B old fresh N cap w z
  let c := historicalRho old fresh N cap w z L
  let G₁ := stripProfile true hd hs U
  let U₁ := stripProfile false hd hs U
  let G₂ := stripProfile true hd hs V
  let U₂ := stripProfile false hd hs V
  let absAlpha := fun short => (‖alpha short‖ : ℂ)
  let μ := ∑ short ∈ Mset, ‖alpha short‖
  let S := logSize U*logSize V
  have hS : 0 ≤ S := mul_nonneg (zero_le_one.trans (logSize_one_le U))
    (zero_le_one.trans (logSize_one_le V))
  have hA := historical_polynomial_norm_sum B old fresh N cap D w z L hlevel G₁ U₂
    (stripProfile_support true hd hs U) (stripProfile_support false hd hs V)
    hU hV hZ j false false Mset absAlpha
  have hC := historical_polynomial_norm_sum B old fresh N cap D w z L hlevel U₁ G₂
    (stripProfile_support false hd hs U) (stripProfile_support true hd hs V)
    hU hV hZ j false false Mset absAlpha
  have hmass : (∑ short ∈ Mset, ‖absAlpha short‖) = μ := by simp [absAlpha, μ]
  rw [hmass] at hA hC
  have hMean := historical_strip_mean_sum B old fresh N cap D w z L hlevel
    hd hs hU hV hZ hx j hy Mset alpha
  have hp (q short : ℕ) :=
    (sharp_pair_point log₁ log₂ hd hs U V t₁ t₂ Z j short N q (alpha short)).trans
      (mul_le_mul_of_nonneg_left (add_le_add_right (norm_add_le _ _) _) hS)
  have H : ‖historicalRoughSum B old fresh N cap w z L
        (sharpProfile log₁ U t₁) (sharpProfile log₂ V t₂) U V Z Mset alpha -
      historicalRoughSum B old fresh N cap w z L
        (profile false log₁ delta U t₁) (profile false log₂ delta V t₂) U V Z Mset alpha‖ ≤
      S*((∑ q ∈ Q, ‖c q‖*∑ short ∈ Mset,
          ‖polyDelta G₁ U₂ U V Z j false false short N q (absAlpha short)‖) +
        (∑ q ∈ Q, ‖c q‖*∑ short ∈ Mset,
          ‖polyDelta U₁ G₂ U V Z j false false short N q (absAlpha short)‖) +
        (∑ q ∈ Q, ‖c q‖*∑ short ∈ Mset,
          2*‖alpha short‖*stripPairMean hd hs U V Z j q short)) := by
    unfold historicalRoughSum
    rw [←Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ q ∈ Q, ‖c q‖*∑ short ∈ Mset,
          ‖roughDelta (sharpProfile log₁ U t₁) (sharpProfile log₂ V t₂) U V Z short N q (alpha short) -
            roughDelta (profile false log₁ delta U t₁) (profile false log₂ delta V t₂) U V Z short N q (alpha short)‖ := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro q hq
        rw [←mul_sub, norm_mul, ←Finset.sum_sub_distrib]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ ≤ ∑ q ∈ Q, ‖c q‖*∑ short ∈ Mset,
          S*(‖polyDelta G₁ U₂ U V Z j false false short N q (absAlpha short)‖ +
            ‖polyDelta U₁ G₂ U V Z j false false short N q (absAlpha short)‖ +
            2*‖alpha short‖*stripPairMean hd hs U V Z j q short) :=
        Finset.sum_le_sum (fun q hq => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun short hshort => hp q short)) (norm_nonneg _))
      _ = _ := by
        calc
          _ = ∑ q ∈ Q, S*(‖c q‖*∑ short ∈ Mset,
              (‖polyDelta G₁ U₂ U V Z j false false short N q (absAlpha short)‖ +
                ‖polyDelta U₁ G₂ U V Z j false false short N q (absAlpha short)‖ +
                2*‖alpha short‖*stripPairMean hd hs U V Z j q short)) := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [←Finset.mul_sum]
            ring
          _ = _ := by
            rw [←Finset.mul_sum]
            simp only [Finset.sum_add_distrib, mul_add]
  exact H.trans ((mul_le_mul_of_nonneg_left (add_le_add (add_le_add hA hC) hMean) hS).trans_eq
    (by unfold endpointInvoice; dsimp only [S, G₁, U₁, G₂, U₂, μ]; ring))

/-- Four explicit local prices. B affects only derivative errors; the
small-integral term has the fixed logarithmic order 26. -/
def endpointFourTermBudget (smoothOrder : ℕ) (x U V Y M : ℝ) (D : ℕ) : ℝ :=
  let ell := Real.log x
  let delta := (ell^smoothOrder)⁻¹
  (256*8^16*sizeConstant)*pairCost delta U V 1*
      (M*Y^2*(D : ℝ)^(3/2 : ℝ))*ell^24 +
    (262144*8^16*sizeConstant)*x*delta*ell^26 +
    (4096*8^16*sizeConstant*stripPrice)*(M*(U+V)*Y)*ell^(25+2*smoothOrder) +
    (256*8^16*sizeConstant*stripPrice^2)*(M*Y^2)*ell^(24+4*smoothOrder)

/-- Finite price algebra from original price/log APIs. In particular
hprod is an exact scale identity, and mu is defined rather than assumed
to satisfy a requested mass or discrepancy estimate. -/
theorem endpointInvoice_le_four_terms
    (smoothOrder s D : ℕ) {x U V Y M : ℝ}
    (hsCard : s ≤ 6) (hx : 1 < x) (hlog : 1 ≤ Real.log x)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUx : U ≤ 4*x) (hVx : V ≤ 4*x)
    (hD : 1 ≤ D) (hDx : (D : ℝ) ≤ x) (hY : 0 ≤ Y) (hM : 0 ≤ M)
    (hprod : M*U*V = x)
    (hd : 0 < ((Real.log x)^smoothOrder)⁻¹)
    (hs : ((Real.log x)^smoothOrder)⁻¹ ≤ 1/4) :
    endpointInvoice hd hs U V x Y (M*(1+Real.log x)^s) D ≤
      endpointFourTermBudget smoothOrder x U V Y M D := by
  let ell := Real.log x
  let delta := (ell^smoothOrder)⁻¹
  let μ := M*(1+ell)^s
  let P := p2Price (stripProfile true hd hs U) (stripProfile false hd hs V) +
    p2Price (stripProfile false hd hs U) (stripProfile true hd hs V)
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hell : 0 ≤ ell := zero_le_one.trans hlog
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  have hμ : 0 ≤ μ := by dsimp only [μ]; positivity
  have hμb : μ ≤ 64*M*ell^6 :=
    (mul_le_mul_of_nonneg_left (short_log_budget hsCard hlog) hM).trans_eq (by ring)
  have hP0 : 0 ≤ P := add_nonneg
    (p2Price_nonneg (stripProfile true hd hs U) (stripProfile false hd hs V))
    (p2Price_nonneg (stripProfile false hd hs U) (stripProfile true hd hs V))
  have hp₁ : p2Price (stripProfile true hd hs U) (stripProfile false hd hs V) ≤
      pairCost delta U V 1 := primary_price true false false false hd hs
        (by norm_num) (by norm_num) (by norm_num)
  have hp₂ : p2Price (stripProfile false hd hs U) (stripProfile true hd hs V) ≤
      pairCost delta U V 1 := primary_price false false true false hd hs
        (by norm_num) (by norm_num) (by norm_num)
  have hP : P ≤ 2*pairCost delta U V 1 := (add_le_add hp₁ hp₂).trans_eq (by ring)
  have hLp := log_product_bound hx0 hlog hU hV hUx hVx
  have hLp0 := mul_nonneg (zero_le_one.trans (logSize_one_le U))
    (zero_le_one.trans (logSize_one_le V))
  have hmoment : momentBudget D ≤ (2*8^16 : ℝ)*(D : ℝ)^(3/2 : ℝ)*ell^16 :=
    moment_log_budget hD hlog hDx
  have hrecip : reciprocalMoment D ≤ 8^16*ell^16 :=
    P4BOriginalE3LogPrices.reciprocalMoment_log hD hlog hDx
  have hm0 := momentBudget_nonneg D
  have hr0 := reciprocalMoment_nonneg D
  have hc0 := pairCost_nonneg delta U V 1
  have hsize := sizeConstant_nonneg
  have hstrip := stripPrice_nonneg
  have hdl0 : 0 ≤ densityLog x := zero_le_one.trans (densityLog_one_le hx.le)
  have hdl : densityLog x ≤ 8*ell := by unfold densityLog; dsimp only [ell]; linarith
  have hpoly : logSize U*logSize V*(P*(Y^2*μ)*momentBudget D) ≤
      (256*8^16*sizeConstant)*pairCost delta U V 1*
        (M*Y^2*(D : ℝ)^(3/2 : ℝ))*ell^24 := by
    calc
      _ ≤ (sizeConstant*ell^2)*((2*pairCost delta U V 1)*
          (Y^2*(64*M*ell^6))*((2*8^16 : ℝ)*(D : ℝ)^(3/2 : ℝ)*ell^16)) := by
        gcongr <;> first
          | exact hLp
          | exact hP
          | exact hμb
          | exact hmoment
          | positivity
      _ = _ := by ring
  let A := 32*delta*U*V*(densityLog x)^2 +
    4*stripPrice/delta^2*(U+V)*Y*densityLog x + 2*stripPrice^2/delta^4*Y^2
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hA : A ≤ 2048*delta*U*V*ell^2 +
      32*stripPrice/delta^2*(U+V)*Y*ell + 2*stripPrice^2/delta^4*Y^2 := by
    calc
      _ ≤ 32*delta*U*V*(8*ell)^2 +
          4*stripPrice/delta^2*(U+V)*Y*(8*ell) + 2*stripPrice^2/delta^4*Y^2 := by
        dsimp only [A]
        gcongr <;> first
          | exact hdl
          | positivity
      _ = _ := by ring
  have hfactor : logSize U*logSize V*(2*μ*reciprocalMoment D) ≤
      (128*8^16*sizeConstant)*M*ell^24 := by
    calc
      _ ≤ (sizeConstant*ell^2)*(2*(64*M*ell^6)*(8^16*ell^16)) := by
        gcongr <;> first
          | exact hLp
          | exact hμb
          | exact hrecip
          | positivity
      _ = _ := by ring
  have hmean : logSize U*logSize V*(2*μ*reciprocalMoment D*A) ≤
      (262144*8^16*sizeConstant)*x*delta*ell^26 +
        (4096*8^16*sizeConstant*stripPrice)*(M*(U+V)*Y)*ell^(25+2*smoothOrder) +
        (256*8^16*sizeConstant*stripPrice^2)*(M*Y^2)*ell^(24+4*smoothOrder) := by
    calc
      _ = (logSize U*logSize V*(2*μ*reciprocalMoment D))*A := by ring
      _ ≤ ((128*8^16*sizeConstant)*M*ell^24)*
          (2048*delta*U*V*ell^2 + 32*stripPrice/delta^2*(U+V)*Y*ell +
            2*stripPrice^2/delta^4*Y^2) := mul_le_mul hfactor hA hA0 (by positivity)
      _ = (262144*8^16*sizeConstant)*(M*U*V)*delta*ell^26 +
          (4096*8^16*sizeConstant*stripPrice)*(M*(U+V)*Y)*ell^(25+2*smoothOrder) +
          (256*8^16*sizeConstant*stripPrice^2)*(M*Y^2)*ell^(24+4*smoothOrder) := by
        rw [show 25+2*smoothOrder = 25+smoothOrder*2 by omega,
          show 24+4*smoothOrder = 24+smoothOrder*4 by omega]
        dsimp only [delta]
        simp only [inv_pow, div_inv_eq_mul, pow_add, pow_mul]
        ring
      _ = _ := by rw [hprod]
  calc
    _ = logSize U*logSize V*(P*(Y^2*μ)*momentBudget D) +
        logSize U*logSize V*(2*μ*reciprocalMoment D*A) := by
      unfold endpointInvoice
      dsimp only [P, μ, A, delta, ell]
      ring
    _ ≤ _ := (add_le_add hpoly hmean).trans_eq (by
      unfold endpointFourTermBudget
      dsimp only [delta, ell]
      ring)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual original signed shortSequence, with its existing mass theorem
called from hcap. No proposed short-mass bound is a hypothesis. -/
theorem historical_shortSequence_endpoint_invoice
    (B : ℝ) (old fresh : List ℕ → Bool) (N cap D : ℕ) (w z L : ℝ)
    (hlevel : ∀ q ∈ historicalModuli B old fresh N cap w z, q ≤ D)
    (log₁ log₂ : Bool) {delta U V Z x : ℝ}
    (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 < U) (hV : 0 < V) (hZ : 1 ≤ Z) (hx : 1 ≤ x)
    (t₁ t₂ : ℝ) (j : ℕ) (hy : Z^(2*j+1) ≤ x)
    (bs : ι → Block) (ys xi : ι → ℝ) (rs : ι → Role)
    (hcap : ∀ a, 2*(lower (bs a) : ℝ) ≤ x) :
    let alpha := shortSequence bs Z ys xi rs
    ‖historicalRoughSum B old fresh N cap w z L
        (sharpProfile log₁ U t₁) (sharpProfile log₂ V t₂) U V Z (shortSupport bs) alpha -
      historicalRoughSum B old fresh N cap w z L
        (profile false log₁ delta U t₁) (profile false log₂ delta V t₂)
        U V Z (shortSupport bs) alpha‖ ≤
      endpointInvoice hd hs U V x (Z^(2*j+1))
        ((shortScale bs : ℝ)*(1+Real.log x)^Fintype.card ι) D := by
  have H := historical_finite_endpoint_invoice B old fresh N cap D w z L hlevel
    log₁ log₂ hd hs hU hV hZ hx t₁ t₂ j hy (shortSupport bs) (shortSequence bs Z ys xi rs)
  exact H.trans (endpointInvoice_mono hd hs hU.le hV.le hx
    (pow_nonneg (zero_le_one.trans hZ) _) D (shortSequence_mass bs Z ys xi rs hx hcap))

/-- The actual finite shortSequence pays precisely the four local
prices, at its exact complete product scale. No U,V >= x^(1/3) premise. -/
theorem historical_shortSequence_endpoint_four_terms
    (B : ℝ) (old fresh : List ℕ → Bool) (N cap D : ℕ) (w z L : ℝ)
    (hlevel : ∀ q ∈ historicalModuli B old fresh N cap w z, q ≤ D)
    (smoothOrder : ℕ) (log₁ log₂ : Bool) {U V Z x : ℝ}
    (hx : 1 < x) (hlog : 1 ≤ Real.log x)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUx : U ≤ 4*x) (hVx : V ≤ 4*x)
    (hZ : 1 ≤ Z) (hD : 1 ≤ D) (hDx : (D : ℝ) ≤ x)
    (hd : 0 < ((Real.log x)^smoothOrder)⁻¹)
    (hs : ((Real.log x)^smoothOrder)⁻¹ ≤ 1/4)
    (t₁ t₂ : ℝ) (j : ℕ) (hy : Z^(2*j+1) ≤ x)
    (bs : ι → Block) (ys xi : ι → ℝ) (rs : ι → Role)
    (hcard : Fintype.card ι ≤ 6) (hcap : ∀ a, 2*(lower (bs a) : ℝ) ≤ x)
    (hprod : (shortScale bs : ℝ)*U*V = x) :
    let delta := ((Real.log x)^smoothOrder)⁻¹
    let alpha := shortSequence bs Z ys xi rs
    ‖historicalRoughSum B old fresh N cap w z L
        (sharpProfile log₁ U t₁) (sharpProfile log₂ V t₂) U V Z (shortSupport bs) alpha -
      historicalRoughSum B old fresh N cap w z L
        (profile false log₁ delta U t₁) (profile false log₂ delta V t₂)
        U V Z (shortSupport bs) alpha‖ ≤
      endpointFourTermBudget smoothOrder x U V (Z^(2*j+1)) (shortScale bs) D := by
  have H := historical_shortSequence_endpoint_invoice B old fresh N cap D w z L hlevel
    log₁ log₂ hd hs (zero_lt_one.trans_le hU) (zero_lt_one.trans_le hV) hZ hx.le
    t₁ t₂ j hy bs ys xi rs hcap
  exact H.trans (endpointInvoice_le_four_terms smoothOrder (Fintype.card ι) D
    hcard hx hlog hU hV hUx hVx hD hDx (pow_nonneg (zero_le_one.trans hZ) _)
    (Nat.cast_nonneg _) hprod hd hs)

end
end ImbalancedChen.P1OriginalHistoricalTwoLongSharpComparison
