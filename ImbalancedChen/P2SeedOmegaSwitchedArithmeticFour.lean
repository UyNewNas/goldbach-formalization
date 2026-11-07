import ImbalancedChen.P2SeedOmegaSwitchedMassFour
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleKThetaDensity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual original Gamma12..15 count bounds from the actual native source,
true-li Theta and supported-d phi. The new proved static omega masses are
inserted into the pinned arithmetic density theorem, with its original
coefficient 2/(1-2delta) retained. The threshold precedes N, the source
box and the four labels. No denominator is cancelled against total mass;
sigma, C(dN), phi(d), log(R/d) and the same total level are preserved.
This is NOT the stronger manuscript K/4 licence, which remains OPEN.
-/

namespace ImbalancedChen.P2SeedOmegaSwitchedArithmeticFour

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open Wu2008DoubleSieve
open Wu2008DoubleSieve.LowerTripleSourceK
open P2SeedOmegaSwitchedKernelFour
open P2SeedOmegaSwitchedMassFour
open P2SeedOmegaLiteralFibre (s s0 phi1 phi2 phi3 a0 a1 a2 a3 b)
open P2SeedOmegaLiteralFunctional (switchedMass)

def gammaIndex : Fin 4 → ℕ := ![12,13,14,15]

/-- The source supplies its own actual alpha lower bound. No uniform
cap assumption or artificial alpha reset is attached to the payload. -/
theorem supported_payload_le_literal {k i N d : ℕ} {delta Delta : ℝ}
    {V : Fin i → ℝ} (hN : 4≤N) (hd : 0<delta) (hdhi : delta<1/2)
    (hb : wuSourceBox k delta N i Delta V)
    (hds : d ∈ boxConvolutionSupport (convolutionWuWindows N Delta V)) (j : Fin 4) :
    0≤sourceIntegralK N d delta nativeParameters (nativeIndex j) ∧
      sourceIntegralK N d delta nativeParameters (nativeIndex j)≤switchedMass (functionalIndex j) := by
  have hphi := omega3XPhi_source_bounds (by omega : 2≤N) hd hdhi hb hds
  have hcorrection : 0≤2*delta/(1/2-delta) :=
    div_nonneg (by positivity) (by linarith only [hdhi])
  have ha : 2≤omega3XPhi N d delta := by
    linarith only [hphi.2.2.1,hcorrection]
  have hactual := original_native_K_le_literal (omega3XPhi N d delta) ha j
  have hupper : sourceIntegralK N d delta nativeParameters (nativeIndex j)≤
      switchedMass (functionalIndex j) := by
    unfold sourceIntegralK
    convert hactual using 1 <;>
      norm_num [nativeParameters,s,s0,phi1,phi2,phi3,a0,a1,a2,a3,b]
  exact ⟨(sourceIntegralK_bounds N d delta nativeParameters native_mother
    (by norm_num [nativeParameters,s] : 2≤nativeParameters.s) (nativeIndex j)).1,hupper⟩

/-- The exact original true-li Theta receives the new literal cap, on
the original coefficient support. This includes empty/zero-mass boxes. -/
theorem original_sourceKTheta_le_literal {k i N : ℕ} {delta Delta : ℝ}
    {V : Fin i → ℝ} (hN : 4≤N) (hd : 0<delta) (hdhi : delta<1/2)
    (hb : wuSourceBox k delta N i Delta V) (j : Fin 4) :
    0≤sourceKTheta N delta Delta V nativeParameters (nativeIndex j) ∧
      sourceKTheta N delta Delta V nativeParameters (nativeIndex j)≤
        switchedMass (functionalIndex j)*
          boxTheta N ((N:ℝ)^(1/2-delta)) (convolutionWuWindows N Delta V) := by
  exact HighSourcePayload.theta_bounds hN hd hdhi hb
    (fun d hds => supported_payload_le_literal hN hd hdhi hb hds j)

/-- Every epsilon chooses one threshold for the four original arithmetic
source families, before N, all admitted source boxes, and the label. -/
theorem original_primeMass_uniform_threshold (k : ℕ) {delta epsilon : ℝ}
    (hd : 0<delta) (hdhi : delta<1/2) (he : 0<epsilon) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N →
      ∀ (i : ℕ) (Delta : ℝ) (V : Fin i → ℝ),wuSourceBox k delta N i Delta V →
        ∀ j : Fin 4,
        (LowerTripleGrouped.sourceFamily N delta Delta V nativeParameters (nativeIndex j)).primeMass≤
          ((2/(1-2*delta))*switchedMass (functionalIndex j)+epsilon)*
            boxTheta N ((N:ℝ)^(1/2-delta)) (convolutionWuWindows N Delta V) := by
  obtain ⟨T,hT,hsource⟩ := source_six_kTheta_density k hd hdhi he
  have hcoef : 0≤2/(1-2*delta) := div_nonneg (by norm_num) (by linarith only [hdhi])
  refine ⟨T,hT,?_⟩
  intro N hN hn i Delta V hb j
  have hN4 := hT.trans hN
  have hs := (hsource N hN hn i Delta V hb nativeParameters native_mother
    (by norm_num [nativeParameters,s] : 2≤nativeParameters.s)).1 (nativeIndex j)
  have hbound := (original_sourceKTheta_le_literal hN4 hd hdhi hb j).2
  have hmult := mul_le_mul_of_nonneg_left hbound hcoef
  calc
    _ ≤ (2/(1-2*delta))*sourceKTheta N delta Delta V nativeParameters (nativeIndex j)+
        epsilon*boxTheta N ((N:ℝ)^(1/2-delta)) (convolutionWuWindows N Delta V) := hs
    _ ≤ (2/(1-2*delta))*(switchedMass (functionalIndex j)*
        boxTheta N ((N:ℝ)^(1/2-delta)) (convolutionWuWindows N Delta V))+
        epsilon*boxTheta N ((N:ℝ)^(1/2-delta)) (convolutionWuWindows N Delta V) :=
      add_le_add_right hmult _
    _ = _ := by ring

/-- The actual Gamma12..15 sums themselves, not a replacement measure.
All finite/source hypotheses are the pinned original ones. The stronger
K/4 switching bound is deliberately not inserted into this conclusion. -/
theorem original_Gamma12_to_15_uniform_threshold (k : ℕ) {delta epsilon : ℝ}
    (hd : 0<delta) (hdhi : delta<1/2) (he : 0<epsilon) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N →
      ∀ (i : ℕ) (Delta : ℝ) (V : Fin i → ℝ),wuSourceBox k delta N i Delta V →
        ∀ j : Fin 4,
        secondFunctionalMotherGammaSum nativeParameters N delta
          (convolutionWuWindows N Delta V) (gammaIndex j)≤
          ((2/(1-2*delta))*switchedMass (functionalIndex j)+epsilon)*
            boxTheta N ((N:ℝ)^(1/2-delta)) (convolutionWuWindows N Delta V) := by
  obtain ⟨T,hT,hsource⟩ := original_primeMass_uniform_threshold k hd hdhi he
  refine ⟨T,hT,?_⟩
  intro N hN hn i Delta V hb j
  have hN4 := hT.trans hN
  have hphysical : secondFunctionalMotherGammaSum nativeParameters N delta
      (convolutionWuWindows N Delta V) (gammaIndex j)≤
      (LowerTripleGrouped.sourceFamily N delta Delta V nativeParameters (nativeIndex j)).primeMass := by
    fin_cases j
    · exact LowerTripleGrouped.gamma12_source_upper hN4 hn hd hdhi hb nativeParameters native_mother
    · exact LowerTripleGrouped.gamma13_source_upper hN4 hn hd hdhi hb nativeParameters native_mother
    · exact LowerTripleGrouped.gamma14_source_upper hN4 hn hd hdhi hb nativeParameters native_mother
    · exact LowerTripleGrouped.gamma15_source_upper hN4 hn hd hdhi hb nativeParameters native_mother
  exact hphysical.trans (hsource N hN hn i Delta V hb j)

end
end ImbalancedChen.P2SeedOmegaSwitchedArithmeticFour
