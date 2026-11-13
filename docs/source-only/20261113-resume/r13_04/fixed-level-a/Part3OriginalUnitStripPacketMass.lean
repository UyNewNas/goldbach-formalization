import ImbalancedChen.Part3OriginalExceptionalHeightWindow
import ImbalancedChen.Part3ActualHighStripCircleMeasure
import ImbalancedChen.Part3NormalizedCuspCompactPoincare
import ImbalancedChen.Part3Gamma0CompactSeedSharpL2Budget
import Mathlib.Analysis.Fourier.AddCircle

/-! Spatial mass of a coherent signed Fourier polynomial in one unit strip.
The horizontal integral is performed before bounding the vertical profiles. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalUnitStripPacketMass20261113
open Set Filter MeasureTheory Complex UpperHalfPlane
open scoped UpperHalfPlane MatrixGroups BigOperators ENNReal
open OriginalExceptionalHeightWindow20261112 ActualHighStripCircleMeasure20261026b
open MaassWeightedCoordinateL220261024zz ActualCuspStripCutoff20261025a
open ActualInfinityKloostermanSeed20261025a CompactCuspParabolicL220261025a
open GammaInfinityTranslationStrip20261025a Gamma0GeneralCuspUnitPeriod20261025a
open NormalizedCuspCompactPoincare20261026b Gamma0CompactSeedSharpL2Budget20261025a

local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩

def coeffMass (s : Finset ℤ) (a : ℤ→ℂ) := ∑ m∈s, ‖a m‖^2
theorem coeffMass_nonneg (s : Finset ℤ) (a : ℤ→ℂ) : 0≤coeffMass s a :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

def polynomial (s : Finset ℤ) (a : ℤ→ℂ) (x : UnitAddCircle) : ℂ :=
  ∑ m∈s,a m*_root_.fourier m x

theorem lp_square_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : Lp ℂ 2 μ) : (∫ x, ‖v x‖^2 ∂μ)=‖v‖^2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ) (x:=v),L2.inner_def,
    ← integral_re (L2.integrable_inner v v)]
  exact integral_congr_ae (ae_of_all _ (fun x =>
    InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ) (v x)))

/-- Exact finite Parseval on the normalized Haar probability circle. -/
theorem polynomial_mass (s : Finset ℤ) (a : ℤ→ℂ) :
    (∫⁻ x : UnitAddCircle, ENNReal.ofReal (‖polynomial s a x‖^2) ∂AddCircle.haarAddCircle)
      = ENNReal.ofReal (coeffMass s a) := by
  let v := fun m : ℤ => _root_.fourierLp (T:=1) 2 m
  let V := ∑ m∈s,a m • v m
  have aeTerm (m : ℤ) : ⇑(a m • v m) =ᵐ[AddCircle.haarAddCircle]
      (fun x => a m*_root_.fourier m x) := by
    filter_upwards [Lp.coeFn_smul (a m) (v m),_root_.coeFn_fourierLp (T:=1) 2 m] with x hx hy
    simpa only [Pi.smul_apply,smul_eq_mul,← hy] using hx
  have rep : ⇑V =ᵐ[AddCircle.haarAddCircle] polynomial s a := by
    filter_upwards [Lp.coeFn_fun_finsetSum s (fun m => a m • v m),ae_all_iff.mpr aeTerm] with x hx h
    exact hx.trans (Finset.sum_congr rfl (fun m _ => h m))
  have E := (_root_.orthonormal_fourier (T:=1)).inner_sum a a s
  change inner ℂ V V = _ at E
  simp_rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq] at E
  rw [inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow,← Complex.ofReal_sum,Complex.ofReal_inj] at E
  have q := V.memLp.integrable_norm_pow (by decide : (2:ℕ)≠0)
  calc
    _ = ∫⁻ x : UnitAddCircle, ENNReal.ofReal (‖V x‖^2) ∂AddCircle.haarAddCircle :=
      lintegral_congr_ae (rep.mono (fun _ h => by rw [h]))
    _ = ENNReal.ofReal (∫ x,‖V x‖^2 ∂AddCircle.haarAddCircle) :=
      (ofReal_integral_eq_lintegral_ofReal q (ae_of_all _ fun _ => sq_nonneg _)).symm
    _ = _ := by simpa only [lp_square_integral,E,coeffMass]

def heightCoeff (H : ℝ) (a : ℤ→ℂ) (y : ℝ) (m : ℤ) : ℂ :=
  a m*(seed (H*|(m:ℝ)|)).toFun y

def cylinder (H : ℝ) (s : Finset ℤ) (a : ℤ→ℂ) (p : UnitAddCircle×ℝ) :=
  polynomial s (heightCoeff H a p.2) p.1

private theorem cylinder_continuous (H : ℝ) (s : Finset ℤ) (a : ℤ→ℂ) :
    Continuous (cylinder H s a) := by
  apply continuous_finsetSum
  intro m hm
  exact (continuous_const.mul ((seed (H*|(m:ℝ)|)).continuous.comp continuous_snd)).mul
    ((_root_.fourier m).continuous.comp continuous_fst)

def stripPacket (H : ℝ) (s : Finset ℤ) (a : ℤ→ℂ) (z : ℍ) : ℂ :=
  ∑ m∈s,a m*cuspStripSeed m (seed (H*|(m:ℝ)|)).toFun z

def framePacket (N : ℕ) (hN : 0<N) (g : SL(2,ℤ)) (H : ℝ) (s : Finset ℤ) (a : ℤ→ℂ)
    (z : ℍ) : ℂ := stripPacket H s a ((normalizedScaling N hN g)⁻¹ • z)

theorem stripPacket_measurable (H : ℝ) (s : Finset ℤ) (a : ℤ→ℂ) :
    Measurable (stripPacket H s a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [stripPacket,Finset.sum_empty] using (measurable_const :
      Measurable (fun _ : ℍ => (0:ℂ)))
  | @insert m s hm ih =>
    have each : Measurable (fun z : ℍ => a m*cuspStripSeed m (seed (H*|(m:ℝ)|)).toFun z) :=
      measurable_const.mul (cuspStripSeed_measurable m _ (seed (H*|(m:ℝ)|)).continuous)
    simpa only [stripPacket,Finset.sum_insert hm] using each.add ih

theorem framePacket_measurable (N : ℕ) (hN : 0<N) (g : SL(2,ℤ)) (H : ℝ)
    (s : Finset ℤ) (a : ℤ→ℂ) : Measurable (framePacket N hN g H s a) :=
  (stripPacket_measurable H s a).comp (inverseFrame_measurePreserving N hN g).measurable

theorem mode_off {H L : ℝ} (hH : 0<H) (hL : 0<L) {m : ℤ}
    (lo : L≤|(m:ℝ)|) (hi : |(m:ℝ)|≤2*L) {z : ℍ}
    (hz : z∉highWidthStrip 1 (bottom H L)) : cuspStripSeed m (seed (H*|(m:ℝ)|)).toFun z=0 := by
  by_cases hs : z∈strip
  · have zero : (seed (H*|(m:ℝ)|)).toFun z.im=0 := by
      by_contra ne
      exact hz ⟨hs,(seed_band hH hL lo hi z.im_pos ne).1⟩
    simp [cuspStripSeed,hs,fourierRadialSeed,zero]
  · simp [cuspStripSeed,hs]

theorem stripPacket_at {H L : ℝ} (hH : 0<H) (hL : 0<L) (s : Finset ℤ) (a : ℤ→ℂ)
    (band : ∀ m∈s,L≤|(m:ℝ)| ∧ |(m:ℝ)|≤2*L) (z : ℍ) :
    stripPacket H s a z=(highWidthStrip 1 (bottom H L)).indicator
      (fun z => cylinder H s a (highStripCircleCoordinate z)) z := by
  classical
  by_cases h : z∈highWidthStrip 1 (bottom H L)
  · have hs : z∈strip := h.1
    rw [indicator_of_mem h]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [cuspStripSeed,indicator_of_mem hs,fourierRadialSeed,heightCoeff,
      highStripCircleCoordinate]
    ring
  · rw [indicator_of_notMem h]
    exact Finset.sum_eq_zero (fun m hm => by
      rw [mode_off hH hL (band m hm).1 (band m hm).2 h,mul_zero])

/-- Full strip y≥Y has hyperbolic area 1/Y. All unit-mass Fourier modes
are evaluated in the same horizontal period before this area is used. -/
theorem strip_mass {H L : ℝ} (hH : 0<H) (hL : 0<L) (s : Finset ℤ) (a : ℤ→ℂ)
    (band : ∀ m∈s,L≤|(m:ℝ)| ∧ |(m:ℝ)|≤2*L) :
    (∫⁻ z : ℍ, seedSquareMass (stripPacket H s a) z) ≤ ENNReal.ofReal (4*coeffMass s a) := by
  let Y := bottom H L
  let T := highWidthStrip 1 Y
  let μ := verticalWeightedMeasure.restrict (Ici Y)
  letI : SigmaFinite verticalWeightedMeasure := by unfold verticalWeightedMeasure; infer_instance
  let F : UnitAddCircle×ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (‖cylinder H s a p‖^2)
  let B := ENNReal.ofReal (4*Y*coeffMass s a)
  have Fm : Measurable F := ENNReal.measurable_ofReal.comp ((cylinder_continuous H s a).norm.pow 2).measurable
  have yPos : 0<Y := bottom_pos hH hL
  have point : seedSquareMass (stripPacket H s a) = T.indicator (F ∘ highStripCircleCoordinate) := by
    funext z
    rw [seedSquareMass,stripPacket_at hH hL s a band]
    change ENNReal.ofReal (‖T.indicator (fun w => cylinder H s a (highStripCircleCoordinate w)) z‖^2) = _
    by_cases hz : z∈T <;> simp [hz,F,Function.comp_apply]
  have totals : (∫⁻ _ : ℍ in T,(1:ℝ≥0∞)) =
      ∫⁻ _ : UnitAddCircle×ℝ,(1:ℝ≥0∞) ∂(AddCircle.haarAddCircle.prod μ) :=
    (highStripCircleCoordinate_measurePreserving Y).lintegral_comp measurable_const
  have hμ : μ univ=ENNReal.ofReal (1/Y) := by
    have product : (AddCircle.haarAddCircle.prod μ) (univ : Set (UnitAddCircle×ℝ))=μ univ := by
      rw [← univ_prod_univ,Measure.prod_prod,measure_univ,one_mul]
    simpa only [lintegral_const,one_mul,Measure.restrict_apply_univ,product,T,
      highWidthStrip_volume zero_le_one yPos] using totals.symm
  have fiber (y : ℝ) (hy : Y≤y) : (∫⁻ x : UnitAddCircle,F (x,y) ∂AddCircle.haarAddCircle)≤B := by
    change (∫⁻ x : UnitAddCircle,ENNReal.ofReal (‖polynomial s (heightCoeff H a y) x‖^2)
      ∂AddCircle.haarAddCircle)≤_
    rw [polynomial_mass]
    apply ENNReal.ofReal_le_ofReal
    unfold coeffMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    rw [heightCoeff,norm_mul,mul_pow,mul_comm (4*Y)]
    exact mul_le_mul_of_nonneg_left
      (seed_sq_le hH hL (band m hm).1 (band m hm).2 (yPos.trans_le hy)) (sq_nonneg _)
  calc
    _ = ∫⁻ z in T,F (highStripCircleCoordinate z) := by
      rw [point,lintegral_indicator (highWidthStrip_measurable 1 Y)]
    _ = ∫⁻ p,F p ∂(AddCircle.haarAddCircle.prod μ) :=
      (highStripCircleCoordinate_measurePreserving Y).lintegral_comp Fm
    _ = ∫⁻ y,(∫⁻ x,F (x,y) ∂AddCircle.haarAddCircle) ∂μ := lintegral_prod_symm _ Fm.aemeasurable
    _ ≤ ∫⁻ _y,B ∂μ := lintegral_mono_ae ((ae_restrict_mem (μ:=verticalWeightedMeasure)
      (measurableSet_Ici : MeasurableSet (Ici Y))).mono (fun y hy => fiber y hy))
    _ = _ := by
      rw [lintegral_const,hμ,← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) yPos.le)
        (coeffMass_nonneg s a))]
      congr 1
      field_simp [yPos.ne'] <;> ring

theorem physical_mass (N : ℕ) (hN : 0<N) (g : SL(2,ℤ)) {H L : ℝ} (hH : 0<H) (hL : 0<L)
    (s : Finset ℤ) (a : ℤ→ℂ) (band : ∀ m∈s,L≤|(m:ℝ)| ∧ |(m:ℝ)|≤2*L) :
    (∫⁻ z : ℍ, seedSquareMass (framePacket N hN g H s a) z) ≤ ENNReal.ofReal (4*coeffMass s a) :=
  ((inverseFrame_measurePreserving N hN g).lintegral_comp
    (seedSquareMass_measurable _ (stripPacket_measurable H s a))).le.trans (strip_mass hH hL s a band)

end ImbalancedChen.Part3.OriginalUnitStripPacketMass20261113
end
