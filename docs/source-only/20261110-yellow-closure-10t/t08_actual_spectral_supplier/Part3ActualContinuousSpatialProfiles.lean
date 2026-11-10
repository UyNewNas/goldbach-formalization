import ImbalancedChen.Part3ActualContinuousClassFourier
import ImbalancedChen.Part3ComplexOrderKQCalculus
import ImbalancedChen.Part3CompletedEisensteinSpatialMaass
import ImbalancedChen.Part3Gamma0QuotientCellPushforward

/-! Spatial representatives of the genuine critical Eisenstein families.
Local normal convergence in the upper half-plane gives continuity in
both spatial coordinates. This permits compact Poincare testing even
though individual Eisenstein functions need not lie in quotient L². -/
namespace ImbalancedChen.Part3.ActualContinuousSpatialProfiles20261110

noncomputable section
open Complex Set Filter Topology UpperHalfPlane MeasureTheory Matrix
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualContinuousClassFourier20261110 ActualOrdinaryContinuousModes20261110
open ActualCharacterCompletedFourier20261110 ActualCharacterCriticalFamily20261110
open ActualCharacterOriginalCuspFourier20261110 ActualCriticalCuspEvaluation20261110
open ActualYoungFormalClass20261110 ActualYoungCriticalD20261110
open ActualYoungDilationInverse20261110 ActualYoungCriticalCusps20261110
open ActualCuspDenominatorClasses20261110 Gamma0DegeneracyMapSourceOnly
open ComplexOrderKQCalculus ComplexOrderKBridgeSourceOnly ComplexOrderKUniformStripDecay20261025a
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
open CompletedEisensteinReflection20261025a CompletedActualEisensteinIdentity20261025a
open Gamma0QuotientCellPushforward20261025a

local instance {N : ℕ} [NeZero N] (i : CharacterSlots N) : NeZero i.2.conductor :=
  ⟨i.2.conductor_ne_zero⟩
local instance (N : ℕ) [NeZero N] (f : Div N) : NeZero (band N f.1) :=
  ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp f.2).1 (NeZero.pos N))).ne'⟩

private theorem kernel_cont (ν : ℂ) {c : ℝ} (hc : 0 < c) :
    Continuous (fun z : ℍ => complexOrderK ν (c*z.im)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (complexOrderK_hasDerivAt_q ν (mul_pos hc z.im_pos)).continuousAt.comp
    (continuous_const.mul UpperHalfPlane.continuous_im).continuousAt

private theorem signed_term_cont {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℤ) :
    Continuous (fun z : ℍ => continuedCoefficient χ n z.im s*fourier n (z.re : UnitAddCircle)) := by
  by_cases hn : n = 0
  · simp [continuedCoefficient,hn]
  · have hp : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
    have hk := kernel_cont (s-1/2) (show 0 < 2*Real.pi*|(n : ℝ)| by positivity)
    simp only [continuedCoefficient,if_neg hn]
    exact (((continuous_const.mul (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp UpperHalfPlane.continuous_im))).mul continuous_const).mul hk).mul
      ((fourier n).continuous.comp (show Continuous (fun z : ℍ => (z.re : UnitAddCircle)) by fun_prop))

private def bandBound (a b : ℝ) (n : ℤ) : ℝ :=
  (2*Real.sqrt b*stripDecayConstant 0 (2*Real.pi*a) 1) *
    ((n.natAbs : ℝ)*Real.exp (-(Real.pi*a)*(n.natAbs : ℝ)))

private theorem band_summable {a : ℝ} (ha : 0 < a) (b : ℝ) : Summable (bandBound a b) := by
  have hp : Summable (fun k : ℕ => bandBound a b (k : ℤ)) := by
    simpa only [bandBound,Int.natAbs_natCast,pow_one] using
      (Real.summable_pow_mul_exp_neg_nat_mul 1 (mul_pos Real.pi_pos ha)).const_mul
        (2*Real.sqrt b*stripDecayConstant 0 (2*Real.pi*a) 1)
  apply Summable.of_nat_of_neg_add_one hp
  simpa [bandBound,Int.natAbs_negSucc] using (summable_nat_add_iff 1).mpr hp

private theorem signed_term_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℤ)
    {a b : ℝ} (ha : 0 < a) (z : ℍ) (hz : z.im ∈ Icc a b) :
    ‖continuedCoefficient χ n z.im (criticalPoint t)*fourier n (z.re : UnitAddCircle)‖ ≤ bandBound a b n := by
  by_cases hn : n = 0
  · simp [continuedCoefficient,bandBound,hn]
  have hN : 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast (Int.natAbs_pos.mpr hn)
  have hAbs : (n.natAbs : ℝ) = |(n : ℝ)| := by simp
  have hA : ‖amplitude χ n (criticalPoint t)‖ ≤ (n.natAbs : ℝ) := by
    have H := (realized_amplitude_critical_bound χ n t).trans
      (show (n.natAbs.divisors.card : ℝ) ≤ n.natAbs by exact_mod_cast Nat.card_divisors_le_self n.natAbs)
    simpa only [criticalPoint,mul_comm I] using H
  have harg : 2*Real.pi*a ≤ 2*Real.pi*(n.natAbs : ℝ)*z.im := by
    have HI := hz.1.trans (le_mul_of_one_le_left z.im_pos.le hN)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left HI (show 0 ≤ 2*Real.pi by positivity)
  have hν : |(criticalPoint t-1/2).re| ≤ (1 : ℝ) := by norm_num [criticalPoint,Complex.mul_re]
  have HK := complexOrderK_uniform_exp_bound (show 0 < 2*Real.pi*a by positivity) harg hν
  have hE : Real.exp (-(2*Real.pi*(n.natAbs : ℝ)*z.im/2)) ≤
      Real.exp (-(Real.pi*a)*(n.natAbs : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hz.1 (show 0 ≤ Real.pi*(n.natAbs : ℝ) by positivity)]
  have HK' := HK.trans (mul_le_mul_of_nonneg_left hE (stripDecayConstant_pos _ _ _).le)
  simp only [continuedCoefficient,if_neg hn,← hAbs,norm_mul,fourier_apply,Circle.norm_coe,mul_one,
    Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsize := mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hz.2) (by norm_num : (0:ℝ) ≤ 2))
    hA (norm_nonneg _) (by positivity : 0 ≤ 2*Real.sqrt b)
  calc
    _ ≤ (2*Real.sqrt b*(n.natAbs : ℝ)) *
        (stripDecayConstant 0 (2*Real.pi*a) 1*Real.exp (-(Real.pi*a)*(n.natAbs : ℝ))) :=
      mul_le_mul hsize HK' (norm_nonneg _) (by positivity)
    _ = _ := by unfold bandBound; ring

theorem completed_character_spatial {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    Continuous (completedFamily χ (criticalPoint t)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let a := z.im/2
  let b := z.im+1
  have ha : 0 < a := half_pos z.im_pos
  have haz : a < z.im := half_lt_self z.im_pos
  have hzb : z.im < b := lt_add_one _
  have hloc : ContinuousOn (completedFamily χ (criticalPoint t)) (UpperHalfPlane.im ⁻¹' Icc a b) :=
    continuousOn_tsum (fun n => (signed_term_cont χ (criticalPoint t) n).continuousOn)
      (band_summable ha b) (fun n w hw => signed_term_bound χ t n ha w hw)
  exact hloc.continuousAt (UpperHalfPlane.continuous_im.continuousAt (Icc_mem_nhds haz hzb))

/-- R22's genuine completed family is already C² in both spatial
coordinates, including the resolved central sqrt(y) log(y) term. -/
theorem principal_spatial (t : ℝ) : Continuous (principalOrdinary (criticalPoint t)) := by
  apply continuous_const.mul
  exact (CompletedEisensteinSpatialMaass.completedEisensteinFourier_contDiffOn_two
    (criticalPoint t)).continuousOn.comp_continuous
      (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im) (fun z : ℍ => z.im_pos)

theorem incoming_spatial {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (d : ℕ+) (t : ℝ) :
    Continuous (incoming χ d t) := by
  have hg : Continuous (fun z : ℍ => degeneracyDiagonal d d.pos • z) := by
    change Continuous (fun z : ℍ => SpecialLinearGroup.mapGL ℝ (degeneracyDiagonal d d.pos) • z)
    exact continuous_const_smul _
  unfold incoming ordinary
  by_cases h : q = 1
  · simpa only [if_pos h] using (principal_spatial t).comp hg
  · simpa only [if_neg h,primitiveFamily] using
      (continuous_const.mul (completed_character_spatial χ t)).comp hg

theorem channel_spatial {N : ℕ} [NeZero N] (i : CharacterSlots N) (t : ℝ) :
    Continuous (channelFunction i.1 i.2 (criticalPoint t)) := by
  rw [original_expansion]
  exact continuous_finsetSum _ (fun b _ => continuous_const.mul (incoming_spatial _ _ t))

theorem native_spatial {N : ℕ} [NeZero N] (a : Parameters N) (t : ℝ) :
    Continuous (physicalFamily N t a) := by
  classical
  rcases a with ⟨f,u⟩
  change Continuous (fun z => parameterFamily ⟨f,u⟩ (criticalPoint t) z)
  simp_rw [inverse_cusp]
  apply continuous_const.mul
  exact continuous_finsetSum _ (fun ξ _ => continuous_const.mul (channel_spatial (⟨f,ξ⟩ : CharacterSlots N) t))

/-- The descended function on the given level quotient uses the
actual invariant ordinary cusp series at this t, including t=0. -/
def quotientProfile {N : ℕ} [NeZero N] (a : Parameters N) (t : ℝ) : Gamma0OrbitSpace N → ℂ :=
  Quotient.lift (physicalFamily N t a) (by
    intro z w h
    obtain ⟨γ,hγ⟩ := MulAction.orbitRel_apply.mp h
    rw [← hγ]
    exact native_invariant a t γ.val γ.property w)

@[simp] theorem quotientProfile_projection {N : ℕ} [NeZero N] (a : Parameters N) (t : ℝ) (z : ℍ) :
    quotientProfile a t (orbitProjection N z) = physicalFamily N t a z := rfl

end
end ImbalancedChen.Part3.ActualContinuousSpatialProfiles20261110
