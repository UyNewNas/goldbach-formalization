import ImbalancedChen.Part5OriginalH430ClassicalSmoothArithmeticPayment

/-! Apply the fixed positive-family price to its original ordinary mass.
The separately proved physical density statement is consumed on the very
coefficient remaining in the one complete transformed signed PP. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothDensityPrice
noncomputable section
open Finset Real Filter Wu2008DoubleSieve
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFiniteFallbackPolicy (rho)
open P2SeedOmegaLiteralFunctional (switchCost)
open Part5OriginalH430RootIntervalTheta (clampLevel clampMass)
open Part5OriginalH430ClassicalSmallSwitchedIntegers (testWeight)
open Part5OriginalH430ClassicalSeedIntegralCap (words_mono words_const)
open Part5OriginalH430ClassicalFixedClampMarks (count)
open Part5OriginalH430ClassicalFixedClampSeedPrice (J)
open Part5OriginalH430ClassicalSmoothRankSupport (W_bounds)
open Part5OriginalH430ClassicalSmoothRankAccounting (smoothRank tails)
open Part5OriginalH430ClassicalSmoothMarkedFamily (smoothCount)
open Part5OriginalH430ClassicalSmoothFamilyLicence (original_positive_family)
open Part5OriginalH430ClassicalSmoothPositiveSieve (whole signedPart)
open Part5OriginalH430ClassicalSmoothArithmeticPayment (tested_le_density_signed)
open scoped Classical Topology BigOperators

theorem smooth_ordinary_nonneg (N : ℕ) (ν δ h c : ℝ) : 0≤smoothCount false N ν δ h c := by
  have H := words_mono (F:=fun _ => 0) (G:=fun cs => ∑ r∈tails cs.length,smoothRank false N ν δ h c cs r)
    (fun _ cs _ => sum_nonneg (fun r _ => sum_nonneg (fun t _ => by
      simpa only [testWeight,Bool.false_eq_true,if_false,mul_one] using (W_bounds cs t ν δ h c).1)))
  simpa only [smoothCount,words_const,mul_zero] using H

theorem choose_outer {n₀ : ℕ} {t₀ κ ε : ℝ} (ht : 0≤t₀) (ht' : t₀≤1/12)
    (hn : 1/((n₀:ℝ)+1)≤11/384) (hk : 0<κ) (hk' : κ≤1/112) (he : 0<ε) :
    let ν := clampLevel n₀ t₀
    ∃ h δ c : ℝ,0<h ∧ h≤1/8 ∧ 0<δ ∧ 0<c ∧ c≤1/8 ∧
      ∀ᶠ N : ℕ in atTop,Even N → ∀ (B : Bank) (round n : ℕ) (e : ℚ) (q : ℕ) (a ω τ L : ℝ),
        1<L → (N:ℝ)^ω≤L → (N:ℝ)^ω≤cutoff N → cutoff N≤(N:ℝ) →
        let D := moduli N ((N:ℝ)^ω)
        let R := rho B round n e q a ω N τ L
        physicalDensitySum D R≤currentK*(singularSeries N/log (N:ℝ)) →
        count true 1 N ν κ≤switchCost*clampMass N n₀ t₀+ε*clampMass N n₀ t₀+
          whole (signedPart N ν δ h c D R) := by
  let ν := clampLevel n₀ t₀
  obtain ⟨h,δ,c,η,γ,hh,hh',hd,hc,hc',hη,hγ,_,hordinary,hprice⟩ :=
    original_positive_family ht ht' hn hk hk' (half_pos he)
  have hK : 0<currentK := by norm_num [currentK]
  have herr := tested_le_density_signed (ν:=ν) ht ht' hn rfl hk' hd hh hh' hc hc' (half_pos he)
  refine ⟨h,δ,c,hh,hh',hd,hc,hc',?_⟩
  filter_upwards [herr,hordinary _ (div_pos hγ hK),hprice,eventually_ge_atTop (2:ℕ)]
    with N htest hraw hprice hN
  intro heven B round n e q a ω τ L hL hwL hwz hz hden
  let D := moduli N ((N:ℝ)^ω)
  let R := rho B round n e q a ω N τ L
  let S := smoothCount false N ν δ h c
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have h0 := zero_lt_one.trans hNr
  have hlog := log_pos hNr
  have hs : S≤(J ν+η+γ/currentK)*((N:ℝ)/log (N:ℝ)) := by
    have hm := mul_le_mul_of_nonneg_right hraw (div_nonneg h0.le hlog.le)
    change ((log (N:ℝ)/(N:ℝ))*S)*((N:ℝ)/log (N:ℝ))≤_ at hm
    convert hm using 1 <;> field_simp [h0.ne',hlog.ne'] <;> ring
  have hphysical : S*physicalDensitySum D R≤(currentK*(J ν+η)+γ)*singularNormalization N := by
    apply (mul_le_mul_of_nonneg_left hden (smooth_ordinary_nonneg N ν δ h c)).trans
    apply (mul_le_mul_of_nonneg_right hs (mul_nonneg hK.le (densityScale_pos hN).le)).trans_eq
    rw [←sourceMassScale_mul_densityScale N]
    field_simp [hK.ne'] <;> ring
  have H := htest heven B round n e q a ω τ L hL hwL hwz hz
  change count true 1 N ν κ≤S*physicalDensitySum D R+whole (signedPart N ν δ h c D R)+
    (ε/2)*clampMass N n₀ t₀ at H
  change (currentK*(J ν+η)+γ)*singularNormalization N≤switchCost*clampMass N n₀ t₀+
    (ε/2)*clampMass N n₀ t₀ at hprice
  change count true 1 N ν κ≤switchCost*clampMass N n₀ t₀+ε*clampMass N n₀ t₀+
    whole (signedPart N ν δ h c D R)
  linarith only [H,hphysical,hprice]

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothDensityPrice

