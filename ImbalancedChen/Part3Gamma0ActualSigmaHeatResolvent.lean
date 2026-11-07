import ImbalancedChen.Part3Gamma0ActualSigmaContinuousCFC
import ImbalancedChen.Part3Gamma0ActualHeatGenerator

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Full Fourier multiplier actions of the ACTUAL Gamma0 heat semigroup and
positive shifted Friedrichs resolvents in the true Sigma Plancherel model.
The scalar symbols are exp(-time*lambda) and 1/(a+lambda), respectively.

The Sigma zero-coordinate fiber is proved null from actual R injectivity.
Time zero is treated independently. The resolvent symbol is obtained by
solving the ACTUAL native shifted Friedrichs graph in the already proved
maximal Sigma multiplication model, rather than by assuming a symbolic
resolvent formula. All physical vectors are admitted. Standard automorphic
cusp/Eisenstein normalization and scalar RMK derivative formulas are outside
this module's scope.
-/

namespace ImbalancedChen.Part3.Gamma0ActualSigmaHeatResolvent20261025a

noncomputable section
open Set MeasureTheory Filter
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualShiftedFriedrichsResolvent20261025a
open Gamma0ActualHeatGenerator20261025a
open Gamma0ActualGlobalFriedrichsGraph20261025a
open Gamma0ActualSigmaPlancherel20261025a
open Gamma0ActualSigmaContinuousCFC20261025a
open GenericResolventScalarMeasure20261025a
open GenericResolventCyclicL2Representation20261025a
open GenericResolventUnboundedMultiplication20261025a
open GenericPositiveResolventHeat20261025a
open CountableSigmaMeasureBundle20261025a

theorem actualSigma_coordinate_pos_ae (N : ℕ) [NeZero N] :
    ∀ᵐ s : ActualSigmaSpectrum N∂actualSigmaMeasure N,0<(s.2:ℝ) := by
  apply (bundle_ae_iff (actualSigmaFiberMeasure N) _).mpr
  intro i
  exact scalarMeasure_coordinate_pos_ae (actualGammaHeatData N) (i:QuotientL2 N)

/-- A true null-fiber theorem on the whole countable Sigma measure,
not merely a separate zero-atom assertion supplied for each vector. -/
theorem actualSigma_zeroFiber (N : ℕ) [NeZero N] :
    actualSigmaMeasure N {s : ActualSigmaSpectrum N | (s.2:ℝ)=0}=0 := by
  have hn : ∀ᵐ s : ActualSigmaSpectrum N∂actualSigmaMeasure N,(s.2:ℝ)≠0 :=
    (actualSigma_coordinate_pos_ae N).mono fun _ hs => ne_of_gt hs
  rw [ae_iff] at hn
  simpa only [not_not] using hn

theorem actualSigmaLambda_nonneg (N : ℕ) [NeZero N] (s : ActualSigmaSpectrum N) :
    0≤actualSigmaLambda N s := by
  have h := spectrum_coordinate_mem_unitInterval (actualGammaHeatData N) s.2
  exact div_nonneg (sub_nonneg.mpr h.2) h.1

theorem actualSigmaLambda_eq_heatLambda (N : ℕ) [NeZero N]
    (s : ActualSigmaSpectrum N) (hs : 0<(s.2:ℝ)) :
    actualSigmaLambda N s=spectralLambda (actualGammaHeatData N) s.2 := by
  dsimp [actualSigmaLambda,lambdaCoordinate,spectralLambda]
  field_simp [hs.ne']
  <;> ring

def actualSigmaHeatContinuousSymbol (N : ℕ) [NeZero N] (time : ℝ) :
    C(ResolventSpectrum (actualGammaResolvent N),ℂ) :=
  complexOfReal (actualGammaResolvent N) (heatScalar (actualGammaHeatData N) time)

theorem actualGammaHeat_eq_continuousCFC (N : ℕ) [NeZero N] (time : ℝ) :
    actualGammaHeat N time=
      actualGammaContinuousCFC N (actualSigmaHeatContinuousSymbol N time) :=
  (complexResolventCFC_ofReal (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
    (heatScalar (actualGammaHeatData N) time)).symm

/-- At time zero the identity symbol is proved directly. At strictly
positive time the proved null zero fiber justifies the inverse-ratio
formula for the continuous heat symbol. -/
theorem actualSigmaHeat_symbol_ae (N : ℕ) [NeZero N] {time : ℝ} (htime : 0≤time) :
    (fun s : ActualSigmaSpectrum N => actualSigmaHeatContinuousSymbol N time s.2)=ᵐ[
      actualSigmaMeasure N] (fun s => (Real.exp (-time*actualSigmaLambda N s):ℂ)) := by
  by_cases ht0 : time=0
  · subst time
    exact Filter.Eventually.of_forall fun s => by
      simp [actualSigmaHeatContinuousSymbol,complexOfReal,heatScalar_zero]
  · have ht : 0<time := lt_of_le_of_ne htime (Ne.symm ht0)
    filter_upwards [actualSigma_coordinate_pos_ae N] with s hs
    change (heatScalar (actualGammaHeatData N) time s.2:ℂ)=_
    rw [heatScalar_apply_of_pos (actualGammaHeatData N) ht hs,
      actualSigmaLambda_eq_heatLambda N s hs]

def actualSigmaHeatProduct (N : ℕ) [NeZero N] (time : ℝ) (g : ActualSigmaL2 N) :
    ActualSigmaSpectrum N→ℂ := fun s => (Real.exp (-time*actualSigmaLambda N s):ℂ)*g s

/-- ALL physical vectors have the literal exponential Fourier action,
including time zero; there is no physical operator-domain restriction. -/
theorem actualGammaHeat_sigma_action_ae (N : ℕ) [NeZero N]
    {time : ℝ} (htime : 0≤time) (u : QuotientL2 N) :
    actualSigmaPlancherel N (actualGammaHeat N time u)=ᵐ[actualSigmaMeasure N]
      actualSigmaHeatProduct N time (actualSigmaPlancherel N u) := by
  have hact := actualSigmaPlancherel_cfc_ae N (actualSigmaHeatContinuousSymbol N time) u
  rw [← actualGammaHeat_eq_continuousCFC N time] at hact
  filter_upwards [hact,actualSigmaHeat_symbol_ae N htime] with s hactS hsymbol
  change actualSigmaPlancherel N (actualGammaHeat N time u) s=
    (Real.exp (-time*actualSigmaLambda N s):ℂ)*actualSigmaPlancherel N u s
  change actualSigmaPlancherel N (actualGammaHeat N time u) s=
    actualSigmaHeatContinuousSymbol N time s.2*actualSigmaPlancherel N u s at hactS
  rw [hactS,hsymbol]

theorem actualGammaHeat_sigma_operator_conjugacy (N : ℕ) [NeZero N] (time : ℝ) :
    actualGammaHeat N time=
      (actualSigmaPlancherel N).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((actualSigmaContinuousMultiplier N (actualSigmaHeatContinuousSymbol N time)).comp
          (actualSigmaPlancherel N).toContinuousLinearEquiv.toContinuousLinearMap) := by
  rw [actualGammaHeat_eq_continuousCFC]
  exact actualGammaContinuousCFC_sigma_conjugacy N _

theorem actualGammaHeat_sigma_coefficient (N : ℕ) [NeZero N]
    {time : ℝ} (htime : 0≤time) (u v : QuotientL2 N) :
    inner ℂ u (actualGammaHeat N time v)=
      ∫ s,star (actualSigmaPlancherel N u s)*
        (Real.exp (-time*actualSigmaLambda N s):ℂ)*actualSigmaPlancherel N v s
        ∂actualSigmaMeasure N := by
  rw [actualGammaHeat_eq_continuousCFC,actualGammaContinuousCFC_sigma_coefficient]
  apply integral_congr_ae
  filter_upwards [actualSigmaHeat_symbol_ae N htime] with s hs
  rw [hs]

theorem actualGammaHeat_sigma_norm_sq (N : ℕ) [NeZero N]
    {time : ℝ} (htime : 0≤time) (u : QuotientL2 N) :
    ‖actualGammaHeat N time u‖^2=
      ∫ s,(Real.exp (-time*actualSigmaLambda N s))^2*
        ‖actualSigmaPlancherel N u s‖^2∂actualSigmaMeasure N := by
  rw [actualGammaHeat_eq_continuousCFC,actualGammaContinuousCFC_sigma_norm_sq]
  apply integral_congr_ae
  filter_upwards [actualSigmaHeat_symbol_ae N htime] with s hs
  rw [hs]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

def actualSigmaShiftedProduct (N : ℕ) [NeZero N] (a : ℝ) (g : ActualSigmaL2 N) :
    ActualSigmaSpectrum N→ℂ := fun s => ((1/(a+actualSigmaLambda N s):ℝ):ℂ)*g s

theorem actualSigmaShiftedSymbol_bounds (N : ℕ) [NeZero N] {a : ℝ} (ha : 0<a)
    (s : ActualSigmaSpectrum N) :
    0≤1/(a+actualSigmaLambda N s) ∧ 1/(a+actualSigmaLambda N s)≤1/a := by
  have hl := actualSigmaLambda_nonneg N s
  exact ⟨one_div_nonneg.mpr (add_nonneg ha.le hl),
    one_div_le_one_div_of_le ha (le_add_of_nonneg_right hl)⟩

/-- The ACTUAL shifted native graph forces the inverse multiplier.
No shifted-symbol CFC identity is supplied as an input. -/
theorem actualGammaShiftedResolvent_sigma_action_ae (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (u : QuotientL2 N) :
    actualSigmaPlancherel N (actualGammaShiftedResolvent N a u)=ᵐ[actualSigmaMeasure N]
      actualSigmaShiftedProduct N a (actualSigmaPlancherel N u) := by
  let w := actualGammaShiftedResolvent N a u
  have hgraph := (actualGammaFriedrichs_sigma_graph_iff_lambda N w (u-(a:ℂ)•w)).mp
    (actualGammaShiftedResolvent_graph_pair N ha u)
  rw [map_sub,map_smul] at hgraph
  filter_upwards [hgraph,Lp.coeFn_sub (actualSigmaPlancherel N u)
    ((a:ℂ)•actualSigmaPlancherel N w),Lp.coeFn_smul (a:ℂ) (actualSigmaPlancherel N w)]
      with s hg hsub hsmul
  change (actualSigmaPlancherel N u-(a:ℂ)•actualSigmaPlancherel N w) s=
    (actualSigmaLambda N s:ℂ)*actualSigmaPlancherel N w s at hg
  rw [hsub,hsmul] at hg
  have hden : a+actualSigmaLambda N s≠0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg ha (actualSigmaLambda_nonneg N s))
  have hdenC : ((a+actualSigmaLambda N s:ℝ):ℂ)≠0 := by exact_mod_cast hden
  have hout : actualSigmaPlancherel N w s=
      actualSigmaPlancherel N u s/((a+actualSigmaLambda N s:ℝ):ℂ) := by
    apply (eq_div_iff hdenC).mpr
    push_cast
    change actualSigmaPlancherel N u s-(a:ℂ)*actualSigmaPlancherel N w s=
      (actualSigmaLambda N s:ℂ)*actualSigmaPlancherel N w s at hg
    linear_combination -hg
  change actualSigmaPlancherel N w s=
    ((1/(a+actualSigmaLambda N s):ℝ):ℂ)*actualSigmaPlancherel N u s
  rw [hout]
  push_cast
  ring

/-- Arbitrary one-measure spectral input: this is a full unitary
operator action, not just a formula for the cyclic seed coefficients. -/
theorem actualSigmaShiftedResolvent_all_inputs (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (g : ActualSigmaL2 N) :
    actualSigmaPlancherel N (actualGammaShiftedResolvent N a
      ((actualSigmaPlancherel N).symm g))=ᵐ[actualSigmaMeasure N]
      actualSigmaShiftedProduct N a g := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    actualGammaShiftedResolvent_sigma_action_ae N ha ((actualSigmaPlancherel N).symm g)

theorem actualGammaShiftedResolvent_sigma_coefficient (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (u v : QuotientL2 N) :
    inner ℂ u (actualGammaShiftedResolvent N a v)=
      ∫ s,star (actualSigmaPlancherel N u s)*((1/(a+actualSigmaLambda N s):ℝ):ℂ)*
        actualSigmaPlancherel N v s∂actualSigmaMeasure N := by
  rw [← (actualSigmaPlancherel N).inner_map_map u (actualGammaShiftedResolvent N a v),
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [actualGammaShiftedResolvent_sigma_action_ae N ha v] with s hs
  simp only [actualSigmaShiftedProduct] at hs
  simp only [RCLike.inner_apply',hs]
  ring

end
end ImbalancedChen.Part3.Gamma0ActualSigmaHeatResolvent20261025a
