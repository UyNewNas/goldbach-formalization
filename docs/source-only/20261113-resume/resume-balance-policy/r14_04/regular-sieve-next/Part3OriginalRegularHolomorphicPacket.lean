import ImbalancedChen.Part3OriginalRegularPeterssonStrip
import ImbalancedChen.Part3OriginalHighStripFourierMass
import Mathlib.Analysis.Fourier.AddCircle
import Batteries.Tactic.OpenPrivate

/-! The full finite frequency restriction, rather than separate horizontal
coefficient bounds. The same Petersson mass is used once for the packet. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularHolomorphicPacket20261113
open Set MeasureTheory Matrix Complex UpperHalfPlane AddCircle
open scoped MatrixGroups UpperHalfPlane ModularForm ENNReal
open OriginalHolomorphicCuspFrames20261110 OriginalHolomorphicPeterssonSpace20261112
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalPeterssonPretrace20261112 OriginalPeterssonHighStrip20261112
open OriginalHeckeStripPairing20261112 (q)
open ActualCuspStripCutoff20261025a (highWidthStrip)
open CanonicalPlanarL2UnitarySourceOnly (chartMap chartMap_measurableEmbedding)
open MaassWeightedCoordinateL220261024zz (verticalWeightedMeasure verticalWeight verticalWeight_measurable)
open ActualHighStripCircleMeasure20261026b (highStrip_chart_map_measure)
open OriginalHighStripFourierMass20261112
open private point point_cont plane plane_meas plane_at unitMeasure from ImbalancedChen.Part3OriginalHighStripFourierMass

private def idx : ℕ ↪ ℤ := ⟨fun n => n,fun _ _ h => Int.ofNat_inj.mp h⟩

private theorem horizontal_packet (N r : ℕ) [NeZero N] (f : Forms N r) (g : SL(2,ℤ))
    (S : Finset ℕ) {y : ℝ} (hy : 0<y) :
    (∑ n∈S,Real.exp (-(4*Real.pi*n*y))*‖raw N (NeZero.pos N) r g n f‖^2) ≤
      ∫ x,‖frameForm N (NeZero.pos N) r f g (point x y hy)‖^2 ∂unitMeasure := by
  let F := frameForm N (NeZero.pos N) r f g
  let u := fun x : ℝ => F (point x y hy)
  have uc : Continuous u := (ModularFormClass.holo F).continuous.comp (point_cont y hy)
  have coeff (n : ℕ) : fourierCoeffOn (by norm_num : (0:ℝ)<1) u (n:ℤ)=
      (Real.exp (-(2*Real.pi*n*y)):ℂ)*raw N (NeZero.pos N) r g n f := by
    let a := Real.exp (-(2*Real.pi*n*y))
    have phase (x : ℝ) : fourier (-(n:ℤ)) (x:UnitAddCircle)=(a:ℂ)*(1/q (point x y hy)^n) := by
      have ex : (a:ℂ)=Complex.exp ((-(2*Real.pi*n*y):ℝ):ℂ) := Complex.ofReal_exp _
      rw [mul_one_div,eq_div_iff (pow_ne_zero _ (Function.Periodic.qParam_ne_zero 1 _))]
      simp only [fourier_coe_apply,q,Function.Periodic.qParam,Complex.ofReal_one,div_one,point,ex,←Complex.exp_nat_mul,
        ←Complex.exp_add]
      push_cast; simp only [div_one]
      congr 1
      ring_nf <;> simp [Complex.I_sq] <;> ring
    have E := ModularFormClass.qExpansion_coeff_eq_intervalIntegral F (by norm_num : (0:ℝ)<1)
      (normalized_frame_unit_strictPeriod N (NeZero.pos N) g) n hy
    simp only [Complex.ofReal_one,div_one,one_mul] at E
    change raw N (NeZero.pos N) r g n f =
      ∫ x in (0:ℝ)..1,(1/q (point x y hy)^n)*u x at E
    rw [fourierCoeffOn_eq_integral,sub_zero,div_one,one_smul,E,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    change fourier (-(n:ℤ)) (x:UnitAddCircle)*u x=(a:ℂ)*((1/q (point x y hy)^n)*u x)
    rw [phase,mul_assoc]
  have value (n : ℕ) : ‖fourierCoeffOn (by norm_num : (0:ℝ)<1) u (idx n)‖^2=
      Real.exp (-(4*Real.pi*n*y))*‖raw N (NeZero.pos N) r g n f‖^2 := by
    change ‖fourierCoeffOn _ u (n:ℤ)‖^2=_
    rw [coeff,norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,
      ←Real.exp_nat_mul]
    congr 2 <;> push_cast <;> ring
  have iu : MemLp u 2 (volume.restrict (Ioc (0:ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm uc.aestronglyMeasurable).mpr (uc.norm.pow 2).integrableOn_Ioc
  have H := hasSum_sq_fourierCoeffOn (by norm_num : (0:ℝ)<1) iu
  simp only [sub_zero,inv_one,one_smul] at H
  have bound := (H.summable.sum_le_tsum (S.map idx) (fun _ _ => sq_nonneg _)).trans_eq H.tsum_eq
  rw [Finset.sum_map] at bound
  simp_rw [value] at bound
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] at bound
  exact bound.trans_eq integral_Ico_eq_integral_Ioc.symm

private def packets {N r : ℕ} [NeZero N] (f : Forms N r) (g : SL(2,ℤ)) (S : Finset ℕ) (y : ℝ) : ℝ :=
  ∑ n∈S,Real.exp (-(4*Real.pi*n*y))*‖raw N (NeZero.pos N) r g n f‖^2

private theorem fibers {N r : ℕ} [NeZero N] (f : Forms N r) (g : SL(2,ℤ)) (S : Finset ℕ)
    {y : ℝ} (hy : 0<y) :
    ENNReal.ofReal (y^(2*r)*packets f g S y)≤∫⁻ x,plane f g (x,y) ∂unitMeasure := by
  let u := fun x => ‖frameForm N (NeZero.pos N) r f g (point x y hy)‖^2
  have uc : Continuous u := (((ModularFormClass.holo _).continuous.comp (point_cont y hy)).norm).pow 2
  have ui : Integrable u unitMeasure := (uc.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self
  apply (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (horizontal_packet N r f g S hy)
    (pow_nonneg hy.le (2*r)))).trans_eq
  change ENNReal.ofReal (y^(2*r)*∫ x,u x ∂unitMeasure)=_
  rw [← integral_const_mul,ofReal_integral_eq_lintegral_ofReal (ui.const_mul _) (ae_of_all _ fun _ => by dsimp [u]; positivity)]
  apply lintegral_congr
  intro x
  have hp : chartMap (point x y hy)=(x,y) := by ext <;> simp [point,chartMap]
  rw [←hp,plane_at]
  simp [frameEnergy,u,point]

/-- Horizontal Parseval and the actual hyperbolic Jacobian, on one moving
strip for all the positive frequencies at once. -/
theorem strip_packet (N r : ℕ) [NeZero N] (hr : 0<r) (f : Forms N r) (g : SL(2,ℤ))
    (S : Finset ℕ) {Y : ℝ} (hY : 0<Y) :
    (∑ n∈S,∫⁻ y in Ici Y,ENNReal.ofReal (y^(2*r-2)*Real.exp (-(4*Real.pi*n*y))*
      ‖raw N (NeZero.pos N) r g n f‖^2)) ≤ ∫⁻ w in highWidthStrip 1 Y,frameEnergy f g w := by
  letI : SigmaFinite verticalWeightedMeasure := by unfold verticalWeightedMeasure; infer_instance
  let B := fun y : ℝ => ENNReal.ofReal (y^(2*r)*packets f g S y)
  have Bm : Measurable B := by dsimp [B,packets]; fun_prop
  have mapE := chartMap_measurableEmbedding.lintegral_map
    (μ:=(volume:Measure ℍ).restrict (highWidthStrip 1 Y)) (plane f g)
  rw [highStrip_chart_map_measure,lintegral_prod_symm _ (plane_meas f g).aemeasurable] at mapE
  simp_rw [plane_at] at mapE
  apply le_trans _ mapE.le
  calc
    _ = ∫⁻ y in Ici Y,∑ n∈S,ENNReal.ofReal (y^(2*r-2)*Real.exp (-(4*Real.pi*n*y))*
        ‖raw N (NeZero.pos N) r g n f‖^2) := by
        symm
        exact lintegral_finsetSum _ (fun n _ => by fun_prop)
    _ = ∫⁻ y in Ici Y,B y ∂verticalWeightedMeasure := by
      unfold verticalWeightedMeasure
      rw [setLIntegral_withDensity_eq_setLIntegral_mul _ verticalWeight_measurable.coe_nnreal_ennreal
        Bm measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici,
        inter_eq_left.mpr (show Ici Y⊆Ioi 0 from fun _ hy => hY.trans_le hy)]
      apply setLIntegral_congr_fun measurableSet_Ici
      intro y hy
      have yp : 0<y := hY.trans_le hy
      have w : (verticalWeight y:ℝ≥0∞)=ENNReal.ofReal ((y⁻¹)^2) := by
        rw [verticalWeight,ENNReal.ofReal_eq_coe_nnreal (sq_nonneg _)]
      change _=(verticalWeight y:ℝ≥0∞)*B y
      rw [w,B,←ENNReal.ofReal_mul (sq_nonneg _),←ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
      apply congrArg ENNReal.ofReal
      have powers : y^(2*r)=y^(2*r-2)*y^2 := by rw [←pow_add]; congr 1 <;>omega
      rw [powers,packets,←mul_assoc,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      field_simp [yp.ne'] <;> ring
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
      exact fibers f g S (hY.trans_le hy)

end ImbalancedChen.Part3.OriginalRegularHolomorphicPacket20261113
end
