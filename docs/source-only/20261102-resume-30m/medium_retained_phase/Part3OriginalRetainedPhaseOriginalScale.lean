import ImbalancedChen.Part3OriginalRetainedPhaseBoundaryVariation
import ImbalancedChen.Part3OriginalGevreyPoissonPacket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
SOURCE ONLY / NOT COMPILED / ZERO FORMAL CREDIT.
The SmoothInput is constructed from the manuscript's paperPsiSchwartz and
its Fourier transform, with fixed first-five-derivative seminorms. The
original actual tight block therefore has no smoothness or variation
premise. Q/q0 and D/d remain in the amplitudes until the original block
inequalities pay them. The final log^25 is absorbed uniformly in x^epsilon.
-/

noncomputable section
open Classical Finset Filter
open scoped BigOperators SchwartzMap FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumPhysicalFiveAbelTower
open ImbalancedChen.Part3.OriginalMediumPhysicalShiftReindex
open ImbalancedChen.Part3.OriginalMediumOneTimeVariationTransfer
open ImbalancedChen.Part3.OriginalMediumSmoothWeightInput
open ImbalancedChen.Part3.OriginalMediumPhysicalFiveJets
open ImbalancedChen.Part3.OriginalMediumCompleteWOneDifference
open ImbalancedChen.Part3.OriginalMediumCompleteWDegreeBound
open ImbalancedChen.Part3.OriginalActualRetainedPhaseCost20261028
open ImbalancedChen.Part3.OriginalActualPoissonTightH20261028
open ImbalancedChen.Part3.OriginalActualAbelPrefixCost20261028
open ImbalancedChen.Part3.OriginalSourcePhysicalAbelCaller20261028
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3.OriginalGevreyActualPsiFourierIBP20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.OriginalRetainedPhaseBoundaryVariation20261102

namespace ImbalancedChen.Part3.OriginalRetainedPhaseOriginalScale20261102

def firstFiveSeminorm (f : 𝓢(ℝ, ℂ)) : ℝ :=
  ∑ j ∈ range 6, SchwartzMap.seminorm ℂ 0 j f

theorem firstFiveSeminorm_nonneg (f : 𝓢(ℝ, ℂ)) :
    0 ≤ firstFiveSeminorm f := by
  apply sum_nonneg
  intro j hj
  exact (SchwartzMap.seminorm ℂ 0 j).nonneg f

theorem iteratedDeriv_le_firstFive (f : 𝓢(ℝ, ℂ)) (j : ℕ)
    (hj : j ≤ 5) (u : ℝ) :
    ‖iteratedDeriv j f u‖ ≤ firstFiveSeminorm f := by
  have hpoint : ‖iteratedDeriv j f u‖ ≤ SchwartzMap.seminorm ℂ 0 j f := by
    simpa only [pow_zero, one_mul] using SchwartzMap.le_seminorm' ℂ 0 j f u
  exact hpoint.trans (single_le_sum
    (fun k hk => (SchwartzMap.seminorm ℂ 0 k).nonneg f)
    (mem_range.mpr (by omega)))

/-- Generic packaging only of primitive fixed Schwartz functions. The
actual specialization below proves the source identities definitionally. -/
def smoothInputOfSchwartz (B : FixedBlock) (f g : 𝓢(ℝ, ℂ))
    (hf : B.psi0 = (f : ℝ → ℂ)) (hg : B.psiHat0 = (g : ℝ → ℂ)) :
    SmoothInput B where
  psi0_contDiff := by rw [hf]; exact f.smooth 5
  psiHat0_contDiff := by rw [hg]; exact g.smooth 5
  psi0Seminorm := firstFiveSeminorm f
  psiHat0Seminorm := firstFiveSeminorm g
  psi0Seminorm_nonneg := firstFiveSeminorm_nonneg f
  psiHat0Seminorm_nonneg := firstFiveSeminorm_nonneg g
  psi0_deriv_bound := by
    intro j hj u; rw [hf]; exact iteratedDeriv_le_firstFive f j hj u
  psiHat0_deriv_bound := by
    intro j hj u; rw [hg]; exact iteratedDeriv_le_firstFive g j hj u

def paperSmooth (B : FixedBlock) : SmoothInput (actualProfile B) :=
  smoothInputOfSchwartz (actualProfile B) paperPsiSchwartz (𝓕 paperPsiSchwartz)
    rfl (by rw [SchwartzMap.fourier_coe]; rfl)

def tightSmooth {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    SmoothInput (tightPoissonAtlasBlock atom z y k hA Csep j small hd negative) :=
  smoothInputOfSchwartz
    (tightPoissonAtlasBlock atom z y k hA Csep j small hd negative)
    paperPsiSchwartz (𝓕 paperPsiSchwartz)
    rfl (by rw [SchwartzMap.fourier_coe]; rfl)

/-- A single absolute profile constant, independent of x,a,d,q0 and
all original family/rectangle/colour/polarization indices. -/
def retainedConstant : ℝ :=
  48 * (243 * (2 * firstFiveSeminorm paperPsiSchwartz) *
    (15 * firstFiveSeminorm (𝓕 paperPsiSchwartz))) *
      (52 * (3 + 4 * Real.pi)) ^ 5

theorem retainedConstant_nonneg : 0 ≤ retainedConstant := by
  unfold retainedConstant
  have h1 := firstFiveSeminorm_nonneg paperPsiSchwartz
  have h2 := firstFiveSeminorm_nonneg (𝓕 paperPsiSchwartz)
  positivity

theorem tight_envelope_original_scale
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (hκ : 0 ≤ κ) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    let T := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
    48 * fifthEnvelope T (tightSmooth atom z y k hA Csep j small hd negative)
      (poissonAmplitude T) (phaseAmplitude T) ≤
      retainedConstant * atom.scale ^ (5 * κ) * Real.log atom.scale ^ 25 := by
  dsimp only
  have h := actual_tight_commonScale_fifth_le atom z y k hA hκ Csep j small hd negative
  dsimp only at h
  have h1 := firstFiveSeminorm_nonneg paperPsiSchwartz
  have h2 := firstFiveSeminorm_nonneg (𝓕 paperPsiSchwartz)
  have hc : 0 ≤ 48 * (243 * (2 * firstFiveSeminorm paperPsiSchwartz) *
      (15 * firstFiveSeminorm (𝓕 paperPsiSchwartz))) := by positivity
  have hh := mul_le_mul_of_nonneg_left h hc
  simpa only [fifthEnvelope,tightSmooth,smoothInputOfSchwartz,
    retainedConstant,mul_assoc] using hh

/-- The actual source weight5 variation, with no smoothness or variation
premise. These two guards only select a nonempty original physical box;
the unconditional E3 theorem below handles the complementary zero cases. -/
theorem tight_variation_original_scale
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (hκ : 0 ≤ κ) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (ho : OrderedBox (poissonAtlasBlock atom z y k hA Csep j small hd negative))
    (hH : 1 ≤ (poissonAtlasBlock atom z y k hA Csep j small hd negative).H) :
    let T := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
    variation T (weight5 T) ≤
      retainedConstant * atom.scale ^ (5 * κ) * Real.log atom.scale ^ 25 := by
  dsimp only
  exact (actual_weight5_variation_le _
    (tightPoissonAtlasBlock_physicalBox atom z y k hA Csep j small hd negative ho hH)
    (tightSmooth atom z y k hA Csep j small hd negative)).trans
      (tight_envelope_original_scale atom z y k hA hκ Csep j small hd negative)

/-- Original E3, all empty and H<1 branches included. There is exactly
one factor x^(5*kappa), before the reciprocal-product Abel or Cauchy step. -/
theorem actual_E3_original_scale
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (hκ : 0 ≤ κ) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
    let T := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
    ‖B.E3‖ ≤ actualPrefixEnvelope T *
      (retainedConstant * atom.scale ^ (5 * κ) * Real.log atom.scale ^ 25) := by
  dsimp only
  let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
  let T := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
  have hx := admissible_scale_gt_one hA
  have hnonneg : 0 ≤ actualPrefixEnvelope T *
      (retainedConstant * atom.scale ^ (5*κ) * Real.log atom.scale ^ 25) := by
    exact mul_nonneg (actualPrefixEnvelope_nonneg T)
      (mul_nonneg (mul_nonneg retainedConstant_nonneg (Real.rpow_nonneg (zero_le_one.trans hx.le) _))
        (pow_nonneg (Real.log_nonneg hx.le) _))
  by_cases ho : OrderedBox B
  · by_cases hH : 1 ≤ B.H
    · have hp := tightPoissonAtlasBlock_physicalBox atom z y k hA Csep j small hd negative ho hH
      rw [← tightPoissonAtlasBlock_E3 atom z y k hA Csep j small hd negative]
      exact (E3_le_prefix_times_variation T hp.toOrderedBox (actualPrefixEnvelope T)
        (actualPrefixEnvelope_nonneg T) (actual_coeff5_le_prefixEnvelope T)).trans
          (mul_le_mul_of_nonneg_left
            (tight_variation_original_scale atom z y k hA hκ Csep j small hd negative ho hH)
            (actualPrefixEnvelope_nonneg T))
    · rw [E3_zero_of_H_lt_one B (lt_of_not_ge hH), norm_zero]
      exact hnonneg
  · rw [E3_zero_of_not_ordered B ho, norm_zero]
    exact hnonneg

theorem log25_eventually_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ 25 ≤ x ^ ε := by
  have hh := (Real.isLittleO_log_rpow_rpow_atTop (25 : ℝ) hε).eventuallyLE
  filter_upwards [hh, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  simpa only [Real.rpow_natCast,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (Real.log_nonneg hx1) 25),
    abs_of_nonneg (Real.rpow_nonneg hx0 ε)] using hx

/-- Uniform epsilon formulation of x^(5*kappa+o(1)). The threshold is
chosen before every atom, block, divisor, sign or rectangle. No variation
bound is hypothesized and no target spectral bound is concluded. -/
theorem actual_E3_original_scale_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ (b : ℕ) (σ κ c0 : ℝ) (atom : MediumAtom) (z y : ℝ) (k : Key)
      (hA : MediumAdmissible b σ κ c0 atom) (hκ : 0 ≤ κ) (Csep : ℕ)
      (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool),
      X ≤ atom.scale →
      let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
      let T := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
      ‖B.E3‖ ≤ actualPrefixEnvelope T *
        (retainedConstant * atom.scale ^ (5 * κ + ε)) := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp (log25_eventually_le_rpow hε)
  refine ⟨X, ?_⟩
  intro b σ κ c0 atom z y k hA hκ Csep j small hd negative hxX
  dsimp only
  have hx : 0 < atom.scale := zero_lt_one.trans (admissible_scale_gt_one hA)
  have hlog := hX atom.scale hxX
  apply (actual_E3_original_scale atom z y k hA hκ Csep j small hd negative).trans
  apply mul_le_mul_of_nonneg_left _ (actualPrefixEnvelope_nonneg _)
  rw [Real.rpow_add hx]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlog
    (mul_nonneg retainedConstant_nonneg (Real.rpow_nonneg hx.le _))

end ImbalancedChen.Part3.OriginalRetainedPhaseOriginalScale20261102
