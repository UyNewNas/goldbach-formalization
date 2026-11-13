import ImbalancedChen.Part3ActualPositiveTensorIntegral
import ImbalancedChen.Part3ActualOppositeBesselTransform
import ImbalancedChen.Part3OriginalAbelOrbit
import Batteries.Tactic.OpenPrivate

/-! Summation of the exact compact packet's native physical probes.
The conjugate spectral order on the first factor works for complex order. -/
namespace ImbalancedChen.Part3.ActualPositiveTensorProbes20261112
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology
open ActualPositiveTensorIntegral20261112 OriginalPositiveHeightTest20261112
open PrescribedLogTensorExpansion20261112 (productAt)
open PrescribedLogTensorCoefficients20261112 (Modes)
open PrescribedLogTensorWindows20261112
open ActualOppositeBesselTransform20261112 ActualOppositeBruhatCoordinates20261112 (amp posMeasure)
open ActualPositiveScalarPacket20261112 ActualPositivePacketHighFrequency20261112 (coords coords_measure)
open RadialSchrodingerL2Form20261025a ComplexOrderKBridgeSourceOnly
open OriginalCuspidalPoincareTrace20261110
open private coefficient probe probe_left from ImbalancedChen.Part3ActualOppositeBesselTransform
open private height_integral from ImbalancedChen.Part3OriginalAbelOrbit

private def wave (ν : ℂ) (x : ℝ) : ℂ := (Real.exp (-x/2):ℂ)*complexOrderK ν (2*Real.pi*Real.exp x)
private theorem wave_cont (ν : ℂ) : Continuous (wave ν) := by
  have e (x : ℝ) : 2*Real.pi*Real.exp x=2*Real.exp (Real.log Real.pi+x) := by rw [Real.exp_add,Real.exp_log Real.pi_pos]; ring
  simp_rw [wave,e]
  exact (by fun_prop : Continuous fun x : ℝ => (Real.exp (-x/2):ℂ)).mul
    ((Klog_cont ν).comp (continuous_const.add continuous_id))

private theorem log_coefficient (ν : ℂ) (ψ : ℝ→ℂ) :
    (∫ a,coefficient ν ψ a ∂posMeasure)=∫ x : ℝ,ψ (Real.exp x)*wave ν x := by
  rw [height_integral (p:=1) (by norm_num)]
  apply integral_congr_ae; filter_upwards with x
  have sq : Real.sqrt (Real.exp x)=Real.exp (x/2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.exp_pos _).le).mp
    rw [Real.sq_sqrt (Real.exp_pos _).le,←Real.exp_nat_mul]; norm_num
  have e : Real.exp x*amp (Real.exp x)=Real.exp (-x/2) := by
    rw [amp,sq,← Real.exp_neg,← Real.exp_nat_mul,←Real.exp_add,←Real.exp_add]; congr 1; ring
  simp only [OriginalAbelGaussian.dilation,Real.sqrt_one,one_mul,Complex.real_smul,
    coefficient,wave,←Complex.ofReal_mul] at *
  linear_combination (ψ (Real.exp x)*complexOrderK ν (2*Real.pi*Real.exp x))*congrArg Complex.ofReal e

def probeProduct (ν : ℂ) (v : Modes) := star (orderProbe 1 (pattern v.1.1 v.2.1) (star ν))*
    orderProbe 1 (rightPattern v.1.2 v.2.2) ν

private theorem atom (ν : ℂ) (v : Modes) :
    probeProduct ν v=∫ z : ℝ×ℝ,productAt v (Real.exp z.1) (Real.exp z.2)*(4*wave ν z.1*wave ν z.2) := by
  rw [probeProduct,probe_left,probe,log_coefficient,log_coefficient]
  let f := fun x : ℝ => pattern v.1.1 v.2.1 (Real.exp x)*wave ν x
  let g := fun y : ℝ => star (rightPattern v.1.2 v.2.2 (Real.exp y))*wave ν y
  calc
    _ = 4*((∫ x,f x)*(∫ y,g y)) := by dsimp [f,g]; ring
    _ = 4*∫ z : ℝ×ℝ,f z.1*g z.2 := by rw [integral_prod_mul]
    _ = _ := by rw [← integral_const_mul]; apply integral_congr_ae; exact ae_of_all _ fun z => by dsimp [f,g,productAt]; ring

private theorem full_packet (η H : RadialTest) (R : ℝ) (ν : ℂ) :
    (∫ z : ℝ×ℝ,height η H R (Real.exp z.1) (Real.exp z.2)*(4*wave ν z.1*wave ν z.2))=
      packet η H R ν := by
  let F := fun z : ℝ×ℝ => height η H R (Real.exp z.1) (Real.exp z.2)*(4*wave ν z.1*wave ν z.2)
  let b : ℝ×ℝ := (-R/2,-R/2)
  change (∫ z,F z)=_
  rw [← integral_add_right_eq_self F b,←coords_measure.integral_comp coords.measurableEmbedding]
  apply integral_congr_ae; filter_upwards with z
  let x := (z.1-R)/2+z.2
  let y := (z.1-R)/2-z.2
  have ex : (coords z+b).1=x := by dsimp [coords,b,x]; ring
  have ey : (coords z+b).2=y := by dsimp [coords,b,y]; ring
  have one : (Real.exp ((x+y)/2):ℂ)*(Real.exp (-x/2):ℂ)*(Real.exp (-y/2):ℂ)=1 := by
    rw [←ofReal_mul,←ofReal_mul,←Real.exp_add,←Real.exp_add,show (x+y)/2+-x/2+-y/2=0 by ring,Real.exp_zero,ofReal_one]
  have a (p : ℝ) : 2*Real.pi*Real.exp p=2*Real.exp (Real.log Real.pi+p) := by rw [Real.exp_add,Real.exp_log Real.pi_pos]; ring
  simp only [F,ex,ey,height_exp,logHeight,raw,wave,envelope,a,
    show x+y+R=z.1 by dsimp [x,y];ring,show (x-y)/2=z.2 by dsimp [x,y];ring,
    show Real.log Real.pi+x=logCenter R z.1+z.2 by dsimp [logCenter,x];ring,
    show Real.log Real.pi+y=logCenter R z.1-z.2 by dsimp [logCenter,y];ring]
  linear_combination 4*η.function z.1*H.function z.2*complexOrderK ν (2*Real.exp (logCenter R z.1+z.2))*
    complexOrderK ν (2*Real.exp (logCenter R z.1-z.2))*one

theorem probes (η H : RadialTest) (R : ℝ) (ν : ℂ) :
    HasSum (fun v : Modes => coeff η H R v*probeProduct ν v) (packet η H R ν) := by
  obtain ⟨B,_,C⟩ := box η H R
  let S := (Icc (-B) B) ×ˢ (Icc (-B) B)
  let W := fun z : ℝ×ℝ => 4*wave ν z.1*wave ν z.2
  have K : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have w : Continuous W := (continuous_const.mul ((wave_cont ν).comp continuous_fst)).mul ((wave_cont ν).comp continuous_snd)
  have I : Integrable (S.indicator (fun z => ‖W z‖)) :=
    (integrable_indicator_iff K.measurableSet).mpr (w.norm.continuousOn.integrableOn_compact K)
  have E := exchange volume η H R (fun z : ℝ×ℝ => Real.exp z.1) (fun z : ℝ×ℝ => Real.exp z.2) W _
    (Real.continuous_exp.comp continuous_fst).measurable (Real.continuous_exp.comp continuous_snd).measurable
    w.aestronglyMeasurable I (fun z => indicator_nonneg (fun _ _ => norm_nonneg _) z) (by
      intro v hv z h
      obtain ⟨a,b⟩ := C v hv _ _ h
      have inc : z∈S := ⟨⟨Real.exp_le_exp.mp a.1,Real.exp_le_exp.mp a.2⟩,⟨Real.exp_le_exp.mp b.1,Real.exp_le_exp.mp b.2⟩⟩
      rw [indicator_of_mem inc])
  simpa only [W,←atom,full_packet] using E.2.2

end
end ImbalancedChen.Part3.ActualPositiveTensorProbes20261112
