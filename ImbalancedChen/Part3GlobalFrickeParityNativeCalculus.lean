import ImbalancedChen.Part3GlobalFrickeParityFormDomain
import ImbalancedChen.Part3Gamma0ActualSigmaContinuousCFC
import ImbalancedChen.Part3Gamma0ActualHeatGenerator
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

Actual R=JJ* commutation with global Fricke, already derived by Riesz
uniqueness, is propagated through pinned genuine continuous CFC. Real
and complex native continuous multipliers, actual heat and actual shifted
resolvents therefore reduce the CLOSED global Fricke +/- channels. Full
mixed scalar coefficients split into two diagonal channel coefficients;
cross-channel terms vanish. No spectral-representation, cusp/Eisenstein
completeness or native-calculus commutation premise is assumed.
-/

noncomputable section

namespace ImbalancedChen.Part3.GlobalFrickeParityNativeCalculus20261026b

open Set MeasureTheory
open ImbalancedChen.Part3.ActualHeckeSecondL220261026b
open ImbalancedChen.Part3.GlobalFrickeHilbertInvolution20261026b
open ImbalancedChen.Part3.GlobalFrickeFriedrichsIntertwining20261026b
open ImbalancedChen.Part3.GlobalFrickeParityProjections20261026b
open ImbalancedChen.Part3.InvolutiveHilbertProjection20261026b
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualWeakRieszResolvent20261025a
open ImbalancedChen.Part3.Gamma0ActualSigmaContinuousCFC20261025a
open ImbalancedChen.Part3.Gamma0ActualHeatGenerator20261025a
open ImbalancedChen.Part3.Gamma0ActualShiftedFriedrichsResolvent20261025a
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.GenericPositiveResolventHeat20261025a
open ImbalancedChen.Part3.PositiveContractionResolventCalculus20261025a

theorem actualResolvent_commute_fricke (N : ℕ) [NeZero N] (hN : 0 < N) :
    Commute (actualGammaResolvent N) (frickeL2 N hN).toContinuousLinearMap := by
  change actualGammaResolvent N * (frickeL2 N hN).toContinuousLinearMap =
    (frickeL2 N hN).toContinuousLinearMap * actualGammaResolvent N
  ext f
  exact (actualGammaResolvent_fricke N hN f).symm

/-- Genuine pinned cfcHom commutation, on the actual physical operator. -/
theorem actualRealCFC_fricke (N : ℕ) [NeZero N] (hN : 0 < N)
    (φ : C(ResolventSpectrum (actualGammaResolvent N), ℝ)) (f : QuotientL2 N) :
    frickeL2 N hN (resolventCFC (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) φ f) =
      resolventCFC (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) φ (frickeL2 N hN f) := by
  have hR := actualResolvent_commute_fricke N hN
  have h := hR.cfcHom (actualGammaResolvent_selfAdjoint N)
    (by simpa only [(actualGammaResolvent_selfAdjoint N).star_eq] using hR) φ
  have he := congrArg (fun A : QuotientL2 N →L[ℂ] QuotientL2 N => A f) h.eq
  change resolventCFC (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) φ (frickeL2 N hN f) =
    frickeL2 N hN (resolventCFC (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) φ f) at he
  exact he.symm

/-- The existing COMPLEX native resolvent-spectrum calculus, using its
proved real/imaginary decomposition; no abstract spectral coordinates. -/
theorem actualContinuousCFC_fricke (N : ℕ) [NeZero N] (hN : 0 < N)
    (φ : C(ResolventSpectrum (actualGammaResolvent N), ℂ)) (f : QuotientL2 N) :
    frickeL2 N hN (actualGammaContinuousCFC N φ f) =
      actualGammaContinuousCFC N φ (frickeL2 N hN f) := by
  change frickeL2 N hN (complexResolventCFC (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) φ f) = _
  simp only [actualGammaContinuousCFC, complexResolventCFC_decomposition,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, map_add, map_smul]
  rw [actualRealCFC_fricke, actualRealCFC_fricke]

theorem actualHeat_fricke (N : ℕ) [NeZero N] (hN : 0 < N) (t : ℝ) (f : QuotientL2 N) :
    frickeL2 N hN (actualGammaHeat N t f) = actualGammaHeat N t (frickeL2 N hN f) := by
  change frickeL2 N hN (resolventCFC (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) (heatScalar (actualGammaHeatData N) t) f) = _
  exact actualRealCFC_fricke N hN _ f

theorem actualShiftedResolvent_fricke (N : ℕ) [NeZero N] (hN : 0 < N)
    (a : ℝ) (f : QuotientL2 N) :
    frickeL2 N hN (actualGammaShiftedResolvent N a f) =
      actualGammaShiftedResolvent N a (frickeL2 N hN f) := by
  have h := (actualResolvent_commute_fricke N hN).cfc_real (resolventRatio a)
  have he := congrArg (fun A : QuotientL2 N →L[ℂ] QuotientL2 N => A f) h.eq
  exact he.symm

/-- Actual reducing projection algebra, for any native bounded operator
whose commutation was proved, not assumed for a requested calculus. -/
theorem operator_plus (N : ℕ) [NeZero N] (hN : 0 < N)
    (T : QuotientL2 N →L[ℂ] QuotientL2 N)
    (hT : ∀ f, frickeL2 N hN (T f) = T (frickeL2 N hN f)) (f : QuotientL2 N) :
    T (frickePlus N hN f) = frickePlus N hN (T f) := by
  change T ((1 / 2 : ℂ) • (f + frickeL2 N hN f)) =
    (1 / 2 : ℂ) • (T f + frickeL2 N hN (T f))
  rw [map_smul, map_add, ← hT f]

theorem operator_minus (N : ℕ) [NeZero N] (hN : 0 < N)
    (T : QuotientL2 N →L[ℂ] QuotientL2 N)
    (hT : ∀ f, frickeL2 N hN (T f) = T (frickeL2 N hN f)) (f : QuotientL2 N) :
    T (frickeMinus N hN f) = frickeMinus N hN (T f) := by
  change T ((1 / 2 : ℂ) • (f - frickeL2 N hN f)) =
    (1 / 2 : ℂ) • (T f - frickeL2 N hN (T f))
  rw [map_smul, map_sub, ← hT f]

theorem operator_cross_zero (N : ℕ) [NeZero N] (hN : 0 < N)
    (T : QuotientL2 N →L[ℂ] QuotientL2 N)
    (hT : ∀ f, frickeL2 N hN (T f) = T (frickeL2 N hN f)) (f g : QuotientL2 N) :
    inner ℂ (frickePlus N hN f) (T (frickeMinus N hN g)) = 0 ∧
    inner ℂ (frickeMinus N hN f) (T (frickePlus N hN g)) = 0 := by
  constructor
  · rw [operator_minus N hN T hT]
    exact fricke_parity_orthogonal N hN _ _
  · rw [operator_plus N hN T hT]
    have h := congrArg star (fricke_parity_orthogonal N hN (T g) f)
    simpa only [inner_conj_symm, star_zero] using h

/-- ALL mixed coefficients decompose into the two genuine reducing
channels. This is stronger than a scalar commutator wrapper. -/
theorem operator_coefficient_split (N : ℕ) [NeZero N] (hN : 0 < N)
    (T : QuotientL2 N →L[ℂ] QuotientL2 N)
    (hT : ∀ f, frickeL2 N hN (T f) = T (frickeL2 N hN f)) (f g : QuotientL2 N) :
    inner ℂ f (T g) =
      inner ℂ (frickePlus N hN f) (T (frickePlus N hN g)) +
        inner ℂ (frickeMinus N hN f) (T (frickeMinus N hN g)) := by
  have hf : f = frickePlus N hN f + frickeMinus N hN f := (plus_add_minus _ f).symm
  have hg : T g = T (frickePlus N hN g) + T (frickeMinus N hN g) := by
    rw [← map_add, plus_add_minus]
  calc
    _ = inner ℂ (frickePlus N hN f + frickeMinus N hN f)
        (T (frickePlus N hN g) + T (frickeMinus N hN g)) := congrArg₂ (inner ℂ) hf hg
    _ = _ := by
      rw [inner_add_left, inner_add_right, inner_add_right,
        (operator_cross_zero N hN T hT f g).1, (operator_cross_zero N hN T hT f g).2]
      simp only [add_zero, zero_add]

theorem actualCFC_parity_reduce (N : ℕ) [NeZero N] (hN : 0 < N)
    (φ : C(ResolventSpectrum (actualGammaResolvent N), ℂ)) (f : QuotientL2 N) :
    actualGammaContinuousCFC N φ (frickePlus N hN f) = frickePlus N hN (actualGammaContinuousCFC N φ f) ∧
    actualGammaContinuousCFC N φ (frickeMinus N hN f) = frickeMinus N hN (actualGammaContinuousCFC N φ f) :=
  ⟨operator_plus N hN _ (actualContinuousCFC_fricke N hN φ) f,
    operator_minus N hN _ (actualContinuousCFC_fricke N hN φ) f⟩

theorem actualHeat_parity_reduce (N : ℕ) [NeZero N] (hN : 0 < N) (t : ℝ) (f : QuotientL2 N) :
    actualGammaHeat N t (frickePlus N hN f) = frickePlus N hN (actualGammaHeat N t f) ∧
    actualGammaHeat N t (frickeMinus N hN f) = frickeMinus N hN (actualGammaHeat N t f) :=
  ⟨operator_plus N hN _ (actualHeat_fricke N hN t) f,
    operator_minus N hN _ (actualHeat_fricke N hN t) f⟩

theorem actualShiftedResolvent_parity_reduce (N : ℕ) [NeZero N] (hN : 0 < N)
    (a : ℝ) (f : QuotientL2 N) :
    actualGammaShiftedResolvent N a (frickePlus N hN f) =
      frickePlus N hN (actualGammaShiftedResolvent N a f) ∧
    actualGammaShiftedResolvent N a (frickeMinus N hN f) =
      frickeMinus N hN (actualGammaShiftedResolvent N a f) :=
  ⟨operator_plus N hN _ (actualShiftedResolvent_fricke N hN a) f,
    operator_minus N hN _ (actualShiftedResolvent_fricke N hN a) f⟩

theorem actualHeat_coefficient_parity_split (N : ℕ) [NeZero N] (hN : 0 < N)
    (t : ℝ) (f g : QuotientL2 N) :
    inner ℂ f (actualGammaHeat N t g) =
      inner ℂ (frickePlus N hN f) (actualGammaHeat N t (frickePlus N hN g)) +
        inner ℂ (frickeMinus N hN f) (actualGammaHeat N t (frickeMinus N hN g)) :=
  operator_coefficient_split N hN _ (actualHeat_fricke N hN t) f g

theorem actualCFC_coefficient_parity_split (N : ℕ) [NeZero N] (hN : 0 < N)
    (φ : C(ResolventSpectrum (actualGammaResolvent N), ℂ)) (f g : QuotientL2 N) :
    inner ℂ f (actualGammaContinuousCFC N φ g) =
      inner ℂ (frickePlus N hN f) (actualGammaContinuousCFC N φ (frickePlus N hN g)) +
        inner ℂ (frickeMinus N hN f) (actualGammaContinuousCFC N φ (frickeMinus N hN g)) :=
  operator_coefficient_split N hN _ (actualContinuousCFC_fricke N hN φ) f g

end ImbalancedChen.Part3.GlobalFrickeParityNativeCalculus20261026b
