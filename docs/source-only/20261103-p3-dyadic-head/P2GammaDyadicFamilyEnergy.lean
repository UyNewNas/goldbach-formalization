import ImbalancedChen.P2GammaDyadicHeadSource
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Summed beta norms and disjoint head energy on the SAME dyadic source.
The complete inherited high-conductor/quotient ledger is summed using
Cauchy before taking a worst-case energy. No selectorMass, pair count,
headMultiplicity or number-of-blocks factor is inserted or suppressed.
-/

namespace ImbalancedChen.P2GammaDyadicFamilyEnergy
noncomputable section
open scoped Classical BigOperators
open P2GammaDyadicHeadIntervals P2GammaDyadicHeadSource
open P2GammaJointRetainedComplement P2GammaJointComplementBlockNorms
open P2GammaRetainedActualNorms P2GammaSmoothLogGrid
open P2GammaSmallConductorIntervalBridge P2GammaConvolutionLargeConductor
open P2GammaDyadicConductorSum P2GammaConductorScaleThreshold
open P2GammaPrimeCharacterSW P2GammaVariablePrimeProfile
open P5OriginalU5CausalFinite (pairSupport)

/-- Gating a selector by its actual endpoint digit preserves its height. -/
theorem selectedSigma_bound (N d : ℕ) (endpoint : (ℕ × ℕ) → ℕ)
    (sigma : (ℕ × ℕ) → ℂ) {height : ℝ} (hh : 0 ≤ height)
    (hs : ∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) :
    ∀ t ∈ pairSupport N,‖selectedSigma d endpoint sigma t‖ ≤ height := by
  intro t ht
  by_cases ha : Active d (endpoint t)
  · simpa only [selectedSigma,if_pos ha] using hs t ht
  · simpa only [selectedSigma,if_neg ha,norm_zero] using hh

def betaRow (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l d : ℕ)
    (endpoint : (ℕ × ℕ) → ℕ) (sigma : (ℕ × ℕ) → ℂ) (b : ℕ) : ℤ → ℂ :=
  paddedRow (jointRetainedProducts N c cs H δ j l)
    (dyadicBeta N c cs H δ j l d endpoint sigma b)

def betaBound (cs : List ℕ) (height V : ℝ) : ℝ :=
  height^2*(2*V)*(1+Real.log (2*V))^((cs.length+3)^2-1)

theorem betaBound_nonneg (cs : List ℕ) (height : ℝ) {V : ℝ} (hV : 1 ≤ V) :
    0 ≤ betaBound cs height V := by
  have hX : 1 ≤ 2*V := by linarith
  have hl := Real.log_nonneg hX
  unfold betaBound
  positivity

/-- Each prefix lane selects ONE block per pair at each head scale. The
previous whole-family norm supplier is invoked with that exact selector. -/
theorem dyadic_beta_norms (N c : ℕ) (cs : List ℕ) (H : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l d : ℕ)
    (hV : 1 ≤ lower δ l) (endpoint : (ℕ × ℕ) → ℕ)
    (sigma : (ℕ × ℕ) → ℂ) {height : ℝ} (hh : 0 ≤ height)
    (hs : ∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) :
    (∑ b ∈ dyadicKeys N d endpoint,
      rowMass (jointRetainedProducts N c cs H δ j l)
        (dyadicBeta N c cs H δ j l d endpoint sigma b)) ≤
      height*(2*lower δ l)*(1+Real.log (2*lower δ l))^(cs.length+2) ∧
    (∑ b ∈ dyadicKeys N d endpoint,
      rowEnergy (betaRow N c cs H δ j l d endpoint sigma b) 0 (ambientHi δ l)) ≤
      betaBound cs height (lower δ l) :=
  actual_block_raw_norms N c cs H hδ hwidth j l hV
    (selectedKey d endpoint) (selectedSigma d endpoint sigma) hh
    (selectedSigma_bound N d endpoint sigma hh hs)

/-- No old head-window overlap remains in the new same-scale basis. -/
theorem dyadic_head_energy_le (N : ℕ) (δ : ℝ) (j d : ℕ) (K : Finset ℕ) :
    (∑ b ∈ K,rowEnergy (dyadicAlpha N δ j d b) 0 (ambientHi δ j)) ≤
      (ambientHi δ j : ℝ) := by
  have heq (b : ℕ) : rowEnergy (dyadicAlpha N δ j d b) 0 (ambientHi δ j) =
      ∑ p ∈ clippedCell (ambientLo δ j) (ambientHi δ j) d b,
        ‖primeHeadCoefficient N δ j p‖^2 :=
    paddedRow_energy _ _ _ (clippedCell_subset _ _ _ _)
  simp_rw [heq]
  calc
    _ ≤ ∑ p ∈ Finset.Icc 1 (ambientHi δ j),‖primeHeadCoefficient N δ j p‖^2 :=
      sum_clipped_cells_le _ _ _ K _ (fun p => sq_nonneg _)
    _ ≤ ∑ _p ∈ Finset.Icc 1 (ambientHi δ j),(1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
        (primeHeadCoefficient_norm_le_one N δ j p) 2
    _ = _ := by simp

/-- Ordinary finite Cauchy on total energies. No large-sieve premise. -/
theorem sum_sqrt_energy_le {ι : Type*} (S : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i,0 ≤ a i) (hb : ∀ i,0 ≤ b i) :
    (∑ i ∈ S,Real.sqrt (a i)*Real.sqrt (b i)) ≤
      Real.sqrt (∑ i ∈ S,a i)*Real.sqrt (∑ i ∈ S,b i) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun i => Real.sqrt (a i)) (fun i => Real.sqrt (b i))
  simp_rw [Real.sq_sqrt (ha _),Real.sq_sqrt (hb _)] at h
  have hA : 0 ≤ ∑ i ∈ S,a i := Finset.sum_nonneg (fun i _ => ha i)
  have hB : 0 ≤ ∑ i ∈ S,b i := Finset.sum_nonneg (fun i _ => hb i)
  have hs : 0 ≤ ∑ i ∈ S,Real.sqrt (a i)*Real.sqrt (b i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hr : 0 ≤ Real.sqrt (∑ i ∈ S,a i)*Real.sqrt (∑ i ∈ S,b i) := by positivity
  apply (sq_le_sq₀ hs hr).mp
  simpa only [mul_pow,Real.sq_sqrt hA,Real.sq_sqrt hB] using h

/-- This is the actual sum consumed by the full high ledger. Cauchy is
applied after total beta mass and disjoint head energy, not to old pairs. -/
theorem dyadic_energy_products_le (N c : ℕ) (cs : List ℕ) (H : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l d : ℕ)
    (hV : 1 ≤ lower δ l) (endpoint : (ℕ × ℕ) → ℕ)
    (sigma : (ℕ × ℕ) → ℂ) {height : ℝ} (hh : 0 ≤ height)
    (hs : ∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) :
    (∑ b ∈ dyadicKeys N d endpoint,
      energyProduct (dyadicAlpha N δ j d b) (betaRow N c cs H δ j l d endpoint sigma b)
        0 0 (ambientHi δ j) (ambientHi δ l)) ≤
      Real.sqrt (ambientHi δ j)*Real.sqrt (betaBound cs height (lower δ l)) := by
  have hA := dyadic_head_energy_le N δ j d (dyadicKeys N d endpoint)
  have hB := (dyadic_beta_norms N c cs H hδ hwidth j l d hV endpoint sigma hh hs).2
  apply (sum_sqrt_energy_le (dyadicKeys N d endpoint)
    (fun b => rowEnergy (dyadicAlpha N δ j d b) 0 (ambientHi δ j))
    (fun b => rowEnergy (betaRow N c cs H δ j l d endpoint sigma b) 0 (ambientHi δ l))
    (fun b => rowEnergy_nonneg _ _ _) (fun b => rowEnergy_nonneg _ _ _)).trans
  exact mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Explicit scalar from the existing full quotient-and-conductor sum,
including its actual logarithmic large-sieve loss. -/
def highFactor (P V Q b0 : ℕ) (ell : ℝ) : ℝ :=
  8*Real.sqrt P*Real.sqrt V*ell/(2 : ℝ)^b0+
  8*(lsLogCoefficient+1)*dyadicCountCoefficient*
    (Real.sqrt P+Real.sqrt V)*ell^3+
  64*lsLogCoefficient*(Q : ℝ)*ell

theorem highFactor_nonneg (P V Q b0 : ℕ) {ell : ℝ} (hell : 0 ≤ ell) :
    0 ≤ highFactor P V Q b0 ell := by
  have hc := lsLogCoefficient_pos
  have hd := dyadicCountCoefficient_pos
  unfold highFactor
  positivity

/-- All high conductors and every quotient k are already included in the
imported theorem. Summing its homogeneous energy term is exact. -/
theorem family_high_le {ι : Type*} (S : Finset ι)
    (a b : ι → ℤ → ℂ) (P V Q b0 : ℕ) {ell : ℝ}
    (hell : 1 ≤ ell) (hg : logGauge Q ≤ ell) :
    (∑ i ∈ S,highConductorTotal (a i) (b i) 0 0 P V Q b0) ≤
      (∑ i ∈ S,energyProduct (a i) (b i) 0 0 P V)*highFactor P V Q b0 ell := by
  calc
    _ ≤ ∑ i ∈ S,energyProduct (a i) (b i) 0 0 P V*highFactor P V Q b0 ell := by
      apply Finset.sum_le_sum
      intro i hi
      convert highConductorTotal_polynomial_le (a i) (b i) 0 0 P V Q b0 ell hell hg using 1
      unfold highFactor
      ring
    _ = _ := (Finset.sum_mul _ _ _).symm

def levelHigh (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l d : ℕ)
    (endpoint : (ℕ × ℕ) → ℕ) (sigma : (ℕ × ℕ) → ℂ) (Q b0 : ℕ) : ℝ :=
  ∑ b ∈ dyadicKeys N d endpoint,
    highConductorTotal (dyadicAlpha N δ j d b)
      (betaRow N c cs H δ j l d endpoint sigma b) 0 0
      (ambientHi δ j) (ambientHi δ l) Q b0

/-- No head-family estimate, source-mass estimate or energy licence is an
input. The remaining parameters are the actual source and finite cutoffs. -/
theorem actual_level_high_le (N c : ℕ) (cs : List ℕ) (H : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l d : ℕ)
    (hV : 1 ≤ lower δ l) (endpoint : (ℕ × ℕ) → ℕ)
    (sigma : (ℕ × ℕ) → ℂ) {height : ℝ} (hh : 0 ≤ height)
    (hs : ∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) (Q b0 : ℕ) :
    levelHigh N c cs H δ j l d endpoint sigma Q b0 ≤
      (Real.sqrt (ambientHi δ j)*Real.sqrt (betaBound cs height (lower δ l)))*
        highFactor (ambientHi δ j) (ambientHi δ l) Q b0 (logGauge Q) := by
  apply (family_high_le (dyadicKeys N d endpoint) _ _ _ _ Q b0
    (logGauge_one_le Q) (le_refl _)).trans
  exact mul_le_mul_of_nonneg_right
    (dyadic_energy_products_le N c cs H hδ hwidth j l d hV endpoint sigma hh hs)
    (highFactor_nonneg _ _ _ _ (zero_le_one.trans (logGauge_one_le Q)))

/-- Both actual endpoints and ALL binary head scales. Their only family
cost is 2*depth(P); the previous logarithmic depth theorem is reused. -/
theorem actual_all_scales_high_le (N c : ℕ) (cs : List ℕ) (H : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ)
    (hV : 1 ≤ lower δ l) (sigma : (ℕ × ℕ) → ℂ) {height : ℝ}
    (hh : 0 ≤ height) (hs : ∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) (Q b0 : ℕ) :
    (∑ d ∈ Finset.range (depth (ambientHi δ j)),
      (levelHigh N c cs H δ j l d (endpointHi N c cs H δ j l) sigma Q b0+
       levelHigh N c cs H δ j l d (endpointLo N c cs H δ j l) sigma Q b0)) ≤
      (2*(depth (ambientHi δ j) : ℝ))*
        (Real.sqrt (ambientHi δ j)*Real.sqrt (betaBound cs height (lower δ l)))*
        highFactor (ambientHi δ j) (ambientHi δ l) Q b0 (logGauge Q) := by
  calc
    _ ≤ ∑ _d ∈ Finset.range (depth (ambientHi δ j)),
        2*((Real.sqrt (ambientHi δ j)*Real.sqrt (betaBound cs height (lower δ l)))*
          highFactor (ambientHi δ j) (ambientHi δ l) Q b0 (logGauge Q)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hh1 := actual_level_high_le N c cs H hδ hwidth j l d hV
        (endpointHi N c cs H δ j l) sigma hh hs Q b0
      have hh2 := actual_level_high_le N c cs H hδ hwidth j l d hV
        (endpointLo N c cs H δ j l) sigma hh hs Q b0
      linarith
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

end
end ImbalancedChen.P2GammaDyadicFamilyEnergy
