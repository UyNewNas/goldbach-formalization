import ImbalancedChen.P2EnhancedNonunitLastDictionary
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeClosedQuadrature
import ImbalancedChen.P2SeedOmegaFourSwitchBounds

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact complete-word nonunit identities for Gamma16--19, followed by
the existing hidden supplier's literal caps. No count/PP licence.
-/
namespace ImbalancedChen.P2EnhancedFourWordDictionary
noncomputable section
open Real Finset Set MeasureTheory Wu2008DoubleSieve
open P2EnhancedNonunitPhysicalQuadrature P2EnhancedNonunitLabelGeometry
open P2EnhancedNonunitWordMass P2EnhancedNonunitMarkedMass
open P2SeedOmegaLiteralFibre (a1 a2 a3 b)
open scoped Classical BigOperators

theorem word16_rows (t : Fin 4 → ℝ) :
    (∀ q, (∑ i, rows 3 q i*t i) ≤ wordIntercept 3 [2,2,2,2] q) ↔
      t ∈ FourPrimeContinuous.D16 a2 a3 := by
  rw [rows_iff]
  constructor
  · rintro ⟨hm,hb⟩
    have h0 := hb 0
    have h3 := hb 3
    norm_num [bandLo,bandHi] at h0 h3
    exact ⟨h0.1,hm 0,hm 1,hm 2,h3.2⟩
  · rintro ⟨h0,h01,h12,h23,h3⟩
    constructor
    · intro k; fin_cases k <;> assumption
    · intro k
      fin_cases k <;> norm_num [bandLo,bandHi] <;> constructor <;> linarith

theorem word17_rows (t : Fin 4 → ℝ) :
    (∀ q, (∑ i, rows 3 q i*t i) ≤ wordIntercept 3 [2,2,2,3] q) ↔
      t ∈ FourPrimeContinuous.D17 a2 a3 b := by
  rw [rows_iff]
  constructor
  · rintro ⟨hm,hb⟩
    have h0 := hb 0
    have h2 := hb 2
    have h3 := hb 3
    norm_num [bandLo,bandHi] at h0 h2 h3
    exact ⟨h0.1,hm 0,hm 1,h2.2,h3.1,h3.2⟩
  · rintro ⟨h0,h01,h12,h2,h3l,h3u⟩
    constructor
    · intro k; fin_cases k <;> dsimp <;> linarith
    · intro k
      fin_cases k <;> norm_num [bandLo,bandHi] <;> constructor <;> linarith

theorem word18_rows (t : Fin 4 → ℝ) :
    (∀ q, (∑ i, rows 3 q i*t i) ≤ wordIntercept 3 [2,2,3,3] q) ↔
      t ∈ FourPrimeContinuous.D18 a2 a3 b := by
  rw [rows_iff]
  constructor
  · rintro ⟨hm,hb⟩
    have h0 := hb 0
    have h1 := hb 1
    have h2 := hb 2
    have h3 := hb 3
    norm_num [bandLo,bandHi] at h0 h1 h2 h3
    exact ⟨h0.1,hm 0,h1.2,h2.1,hm 2,h3.2⟩
  · rintro ⟨h0,h01,h1,h2,h23,h3⟩
    constructor
    · intro k; fin_cases k <;> dsimp <;> linarith
    · intro k
      fin_cases k <;> norm_num [bandLo,bandHi] <;> constructor <;> linarith

theorem word19_rows (t : Fin 4 → ℝ) :
    (∀ q, (∑ i, rows 3 q i*t i) ≤ wordIntercept 3 [1,3,3,3] q) ↔
      t ∈ FourPrimeContinuous.D19 a1 a2 a3 b := by
  rw [rows_iff]
  have h23 : a2 ≤ a3 := by norm_num [a2,a3]
  constructor
  · rintro ⟨hm,hb⟩
    have h0 := hb 0
    have h1 := hb 1
    have h3 := hb 3
    norm_num [bandLo,bandHi] at h0 h1 h3
    exact ⟨h0.1,h0.2,h23,h1.1,hm 1,hm 2,h3.2⟩
  · rintro ⟨h0l,h0u,_,h1,h12,h23',h3⟩
    constructor
    · intro k; fin_cases k <;> dsimp <;> linarith
    · intro k
      fin_cases k <;> norm_num [bandLo,bandHi] <;> constructor <;> linarith

private theorem native_compact : FourPrimeContinuous.CompactParameters a1 a2 a3 b := by
  norm_num [FourPrimeContinuous.CompactParameters,a1,a2,a3,b]

theorem nonunitIntegral16_eq_K16 (alpha : ℝ) :
    nonunitIntegral [2,2,2,2] alpha = FourPrimeContinuous.K16 a2 a3 alpha := by
  rw [FourPrimeContinuous.K16,FourPrimeContinuous.integral_mask_literal _
    (FourPrimeContinuous.D16_measurable a2 a3) (FourPrimeContinuous.D16_subset_cube native_compact)]
  unfold nonunitIntegral wordIntegral closedIntegral
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [← word16_rows t,Set.indicator_apply,FourPrimeContinuous.G]
  rfl

theorem nonunitIntegral17_eq_K17 (alpha : ℝ) :
    nonunitIntegral [2,2,2,3] alpha = FourPrimeContinuous.K17 a2 a3 b alpha := by
  rw [FourPrimeContinuous.K17,FourPrimeContinuous.integral_mask_literal _
    (FourPrimeContinuous.D17_measurable a2 a3 b) (FourPrimeContinuous.D17_subset_cube native_compact)]
  unfold nonunitIntegral wordIntegral closedIntegral
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [← word17_rows t,Set.indicator_apply,FourPrimeContinuous.G]
  rfl

theorem nonunitIntegral18_eq_K18 (alpha : ℝ) :
    nonunitIntegral [2,2,3,3] alpha = FourPrimeContinuous.K18 a2 a3 b alpha := by
  rw [FourPrimeContinuous.K18,FourPrimeContinuous.integral_mask_literal _
    (FourPrimeContinuous.D18_measurable a2 a3 b) (FourPrimeContinuous.D18_subset_cube native_compact)]
  unfold nonunitIntegral wordIntegral closedIntegral
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [← word18_rows t,Set.indicator_apply,FourPrimeContinuous.G]
  rfl

theorem nonunitIntegral19_eq_K19 (alpha : ℝ) :
    nonunitIntegral [1,3,3,3] alpha = FourPrimeContinuous.K19 a1 a2 a3 b alpha := by
  rw [FourPrimeContinuous.K19,FourPrimeContinuous.integral_mask_literal _
    (FourPrimeContinuous.D19_measurable a1 a2 a3 b) (FourPrimeContinuous.D19_subset_cube native_compact)]
  unfold nonunitIntegral wordIntegral closedIntegral
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [← word19_rows t,Set.indicator_apply,FourPrimeContinuous.G]
  rfl

/-- Reuse the existing actual-integral log caps after the genuinely
missing complete-word dictionary. The old source is materialized EXACTLY
in reuse/, not represented as a new analytic cap proof. -/
theorem original_four_word_log_caps (alpha : ℝ) :
    nonunitIntegral [2,2,2,2] alpha ≤ P2SeedOmegaLiteralFunctional.switchedMass 7 ∧
    nonunitIntegral [2,2,2,3] alpha ≤ P2SeedOmegaLiteralFunctional.switchedMass 8 ∧
    nonunitIntegral [2,2,3,3] alpha ≤ P2SeedOmegaLiteralFunctional.switchedMass 9 ∧
    nonunitIntegral [1,3,3,3] alpha ≤ P2SeedOmegaLiteralFunctional.switchedMass 10 := by
  have h := P2SeedOmegaFourSwitchBounds.original_four_masses_log_caps alpha
  rw [nonunitIntegral16_eq_K16,nonunitIntegral17_eq_K17,
    nonunitIntegral18_eq_K18,nonunitIntegral19_eq_K19]
  convert h using 1 <;>
    norm_num [P2SeedOmegaFourSwitchBounds.originalFourMass,P2SeedOmegaFourSwitchBounds.p,
      Wu2008DoubleSieve.SecondFunctionalJointTail.massDomainFour,
      FourPrimeContinuous.K16,FourPrimeContinuous.K17,FourPrimeContinuous.K18,FourPrimeContinuous.K19,
      P2SeedOmegaLiteralFibre.s,P2SeedOmegaLiteralFibre.phi1,
      P2SeedOmegaLiteralFibre.phi2,P2SeedOmegaLiteralFibre.phi3,a1,a2,a3,b]

end
end ImbalancedChen.P2EnhancedFourWordDictionary
