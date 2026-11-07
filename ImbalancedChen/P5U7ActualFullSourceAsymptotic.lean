import ImbalancedChen.P5U7InteriorIntegralEtaZero
import ImbalancedChen.P5U7ActualInteriorProductMass
import Mathlib.Topology.Order.LiminfLimsup

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Complete eta-zero asymptotic of the actual original U7 arithmetic source.
Eta is selected FIRST from the proved literal integral limit; N is then
selected from its actual fixed-interior arithmetic asymptotic. The upper
direction uses the actual prime-window collar reserve, never an arithmetic
null-wall deletion. No hLimit, integral positivity, or numerical J7 bound.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology
open scoped BigOperators
open Classical

def p5U7ActualFullSourceMass (N : ℕ) : ℝ :=
  ((p5U7ArithmeticThree N).card : ℝ) + ((p5U7ArithmeticFour N).card : ℝ)

theorem p5U7ActualInteriorSourceMass_le_full (N : ℕ) (eta : ℝ) :
    p5U7ActualInteriorSourceMass N eta ≤ p5U7ActualFullSourceMass N := by
  unfold p5U7ActualFullSourceMass
  rw [p5U7Original_arithmetic_mass_eq_rows]
  unfold p5U7ActualInteriorSourceMass
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun t ht _ => p5U7OriginalRowMass_nonneg N t)

/-- For each requested error eta>0 is fixed BEFORE the eventual N.
The actual strict interior remains a literal subset of the full source. -/
theorem p5U7ActualFullSource_eventually_normalized_lower (epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, p5U7InteriorOmegaIntegral 0 - epsilon ≤
      (Real.log (N : ℝ) / (N : ℝ)) * p5U7ActualFullSourceMass N := by
  have hI : Tendsto p5U7InteriorOmegaIntegral (𝓝[Ioi (0 : ℝ)] 0)
      (𝓝 (p5U7InteriorOmegaIntegral 0)) :=
    tendsto_p5U7InteriorOmegaIntegral_eta_zero.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hnear : ∀ᶠ eta : ℝ in 𝓝[Ioi 0] 0,
      p5U7InteriorOmegaIntegral 0 - epsilon / 2 < p5U7InteriorOmegaIntegral eta :=
    hI.eventually (Ioi_mem_nhds (by linarith only [he]))
  have hpos : ∀ᶠ eta : ℝ in 𝓝[Ioi 0] 0, 0 < eta := self_mem_nhdsWithin
  obtain ⟨eta, heta, hIntegral⟩ := (hpos.and hnear).exists
  have hFixed := (tendsto_p5U7ActualInteriorSourceMass_normalized eta heta).eventually
    (Ioi_mem_nhds (show p5U7InteriorOmegaIntegral eta - epsilon / 2 < p5U7InteriorOmegaIntegral eta by
      linarith only [he]))
  filter_upwards [hFixed, eventually_ge_atTop (2 : ℕ)] with N hInterior hN
  have hNorm : 0 ≤ Real.log (N : ℝ) / (N : ℝ) :=
    div_nonneg (Real.log_natCast_nonneg N) (Nat.cast_nonneg N)
  have hSub := mul_le_mul_of_nonneg_left (p5U7ActualInteriorSourceMass_le_full N eta) hNorm
  linarith only [hIntegral, hInterior, hSub]

/-- Full arithmetic upper transport is the existing actual collar budget
followed by the genuine marked double-prime main; no J7 bound is used. -/
theorem p5U7ActualFullSource_eventually_normalized_upper (epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, (Real.log (N : ℝ) / (N : ℝ)) * p5U7ActualFullSourceMass N ≤
      p5U7InteriorOmegaIntegral 0 + epsilon := by
  have hSource := p5U7Original_eventually_arithmetic_mass_le_main (epsilon / 2) (by positivity)
  have hMain := tendsto_p5U7MassBuchstabMain_normalized.eventually
    (Iio_mem_nhds (show p5U7InteriorOmegaIntegral 0 < p5U7InteriorOmegaIntegral 0 + epsilon / 2 by
      linarith only [he]))
  filter_upwards [hSource, hMain, eventually_ge_atTop (2 : ℕ)] with N hs hm hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hBound := mul_le_mul_of_nonneg_left hs (div_nonneg hLog.le hNR.le)
  have hEq : (Real.log (N : ℝ) / (N : ℝ)) *
      (p5U7MassBuchstabMain N + (epsilon / 2) * ((N : ℝ) / Real.log (N : ℝ))) =
      (Real.log (N : ℝ) / (N : ℝ)) * p5U7MassBuchstabMain N + epsilon / 2 := by
    field_simp [hNR.ne', hLog.ne']
    <;> ring
  rw [hEq] at hBound
  change (Real.log (N : ℝ) / (N : ℝ)) *
    (((p5U7ArithmeticThree N).card : ℝ) + ((p5U7ArithmeticFour N).card : ℝ)) ≤ _
  linarith only [hBound, hm]

/-- Actual full original prime/ordered-semiprime source mean. Both
directions are supplied mathematically, with eta fixed before N in the
lower direction and the real arithmetic collar paid in the upper one. -/
theorem tendsto_p5U7ActualFullSourceMass_normalized :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / (N : ℝ)) * p5U7ActualFullSourceMass N)
      atTop (𝓝 (p5U7InteriorOmegaIntegral 0)) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    have he : 0 < (p5U7InteriorOmegaIntegral 0 - l) / 2 := by linarith only [hl]
    filter_upwards [p5U7ActualFullSource_eventually_normalized_lower _ he] with N hN
    linarith only [hN, hl]
  · intro u hu
    have he : 0 < (u - p5U7InteriorOmegaIntegral 0) / 2 := by linarith only [hu]
    filter_upwards [p5U7ActualFullSource_eventually_normalized_upper _ he] with N hN
    linarith only [hN, hu]

theorem p5U7ActualFullSource_liminf_ge_integral :
    p5U7InteriorOmegaIntegral 0 ≤ liminf
      (fun N : ℕ => (Real.log (N : ℝ) / (N : ℝ)) * p5U7ActualFullSourceMass N) atTop := by
  rw [tendsto_p5U7ActualFullSourceMass_normalized.liminf_eq]

/-- The literal full product-fibre weight retains all marked multiplicity
and every repeated terminal-prime label. No product injectivity is used. -/
theorem tendsto_p5U7ActualFullProductWeight_mass :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / (N : ℝ)) *
      (∑ m ∈ Finset.range N, p5U7ArithmeticProductWeight N m)) atTop
        (𝓝 (p5U7InteriorOmegaIntegral 0)) := by
  simpa only [p5U7Arithmetic_product_weight_mass, p5U7ActualFullSourceMass] using
    tendsto_p5U7ActualFullSourceMass_normalized

/-- Original manuscript integral form. Only the existing genuine
Lebesgue/Fubini dictionary identifies the closed integral; arithmetic
source boundaries are retained and paid by the actual source reserve. -/
theorem tendsto_p5U7ActualFullProductWeight_mass_original :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / (N : ℝ)) *
      (∑ m ∈ Finset.range N, p5U7ArithmeticProductWeight N m)) atTop
        (𝓝 (p5U7OriginalOmegaIntegral 1)) := by
  simpa only [p5U7InteriorOmegaIntegral_zero_eq_original] using tendsto_p5U7ActualFullProductWeight_mass

end

end ImbalancedChen
