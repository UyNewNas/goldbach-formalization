import ImbalancedChen.P5ActualHBAuxiliaryPrefixes
import ImbalancedChen.Part3ActualRoughContourParameters

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Uniform payment of the auxiliary filter at the ORIGINAL cutoff
x^(1/(loglog x)^3).  The threshold is chosen before every role, real
Mobius cutoff, integer height, interval, frequency and auxiliary modulus.
The displayed log-role amplitude remains explicit.  This is not a
Siegel--Walfisz theorem for the k=1 rough prefix.
-/
namespace ImbalancedChen.P5Z.ActualHBChartAuxiliaryPayment
noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open ImbalancedChen.Part3
open ImbalancedChen.Part3.ActualRoughContourParameters20261026b
open ActualRoughHeathBrownWords ActualHBAuxiliaryPrefixes

/-- The real chart cutoff dominates EVERY fixed logarithmic power.  This
uses the existing proved loglog-envelope limit, with no sampled threshold. -/
theorem eventually_chart_dominates_logPower (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ x : ℝ in atTop, 0 < Real.log x ∧ 0 < roughZ x ∧
      Real.log x^B ≤ roughZ x := by
  have hpay := eventually_loglog_envelope_le B 1 1 1 hB (by norm_num)
    (by norm_num) (by norm_num)
  have hll : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log (Real.log x) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hpay,hll,eventually_gt_atTop (1 : ℝ)] with x hp hl hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hL : 0 < Real.log x := Real.log_pos hx
  have hl0 : 0 < Real.log (Real.log x) := zero_lt_one.trans_le hl
  have hz : 0 < roughZ x := Real.rpow_pos_of_pos hx0 _
  have hp' : B*Real.log (Real.log x)^3*(1+Real.log (Real.log x)) ≤ Real.log x := by
    apply (div_le_one hL).mp
    simpa only [Real.rpow_one] using hp
  have hfour : B*Real.log (Real.log x)^4 ≤ Real.log x := by
    nlinarith [mul_nonneg hB (pow_nonneg hl0.le 3)]
  have hcompare : B*Real.log (Real.log x) ≤
      Real.log x / Real.log (Real.log x)^3 := by
    apply (le_div_iff₀ (pow_pos hl0 3)).mpr
    nlinarith only [hfour]
  refine ⟨hL,hz,?_⟩
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hL B) hz).mp
  rw [Real.log_rpow hL,roughZ,Real.log_rpow hx0]
  convert hcompare using 1 <;> ring

/-- Finite auxiliary removal has arbitrary logarithmic saving at the
literal chart cutoff.  No threshold depends on H,k,q,b,y or the role. -/
theorem eventually_actual_chart_auxiliary_removal (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, ∀ role : Role,
      ∀ S : Finset ℕ, ∀ H k q b : ℕ,
        S ⊆ Finset.Ioc 0 H → 0 < k → 0 < q →
        ‖auxiliarySWError S (actual (roughZ x) y role) k q b -
          auxiliarySWError S (actual (roughZ x) y role) 1 q b‖ ≤
          2*roleAmplitude role H*(k.divisors.card : ℝ)*(H : ℝ)/Real.log x^A := by
  filter_upwards [eventually_chart_dominates_logPower A hA] with x hx
  intro y role S H k q b hS hk hq
  have hM := roleAmplitude_nonneg role H
  refine (actual_auxiliary_removal (roughZ x) y role S H k q b hS hx.2.1 hk hq).trans ?_
  exact div_le_div_of_nonneg_left (by positivity)
    (Real.rpow_pos_of_pos hx.1 A) hx.2.2

theorem eventually_actual_chart_mellin_auxiliary_removal (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop, ∀ y t U : ℝ, ∀ role : Role,
      ∀ S : Finset ℕ, ∀ H k q b : ℕ,
        S ⊆ Finset.Ioc 0 H → 0 < k → 0 < q →
        ‖auxiliarySWError S
            (fun n => PrimeMellinProfileVariation20261026b.phase t ((n : ℝ)/U)*
              actual (roughZ x) y role n) k q b -
          auxiliarySWError S
            (fun n => PrimeMellinProfileVariation20261026b.phase t ((n : ℝ)/U)*
              actual (roughZ x) y role n) 1 q b‖ ≤
          2*roleAmplitude role H*(k.divisors.card : ℝ)*(H : ℝ)/Real.log x^A := by
  filter_upwards [eventually_chart_dominates_logPower A hA] with x hx
  intro y t U role S H k q b hS hk hq
  have hM := roleAmplitude_nonneg role H
  refine (actual_mellin_auxiliary_removal (roughZ x) y t U role S H k q b
    hS hx.2.1 hk hq).trans ?_
  exact div_le_div_of_nonneg_left (by positivity)
    (Real.rpow_pos_of_pos hx.1 A) hx.2.2

end
end ImbalancedChen.P5Z.ActualHBChartAuxiliaryPayment
