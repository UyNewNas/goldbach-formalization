import ImbalancedChen.Part3FiniteHeightModeGraphClosure
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual finite Fourier packets with one compact positive height support.
The real lift is C-infinity JOINTLY in horizontal and vertical variables.
Both literal first derivatives are displayed, smooth, and supported in
the same height set. The packet has exact Haar mean zero and defines an
actual physical classical graph pair, rather than just closure membership.
-/
namespace ImbalancedChen.Part3.JointSmoothFiniteCuspPackets20261026b
noncomputable section
open Set MeasureTheory
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanSmoothApproximationSourceOnly
open ClosedHorizontalCuspTail20261026a FiniteHeightModeGraphClosure20261026b
attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsFiniteMeasureOnCompacts rawCylinderMeasure := by
  unfold rawCylinderMeasure
  infer_instance

structure SmoothPacket where
  modes : Finset ℤ
  modes_nonzero : ∀ k ∈ modes, k ≠ 0
  profile : ℤ → ℝ → ℂ
  smooth_profile : ∀ k, ContDiff ℝ ∞ (profile k)
  heightSupport : Set ℝ
  compact_heightSupport : IsCompact heightSupport
  positive_heightSupport : heightSupport ⊆ Ioi (0 : ℝ)
  profile_support : ∀ k, tsupport (profile k) ⊆ heightSupport

def SmoothPacket.value (P : SmoothPacket) (z : CuspCylinder) : ℂ :=
  ∑ k ∈ P.modes, AddCircle.fourier k z.1 * P.profile k (z.2 : ℝ)

def SmoothPacket.dx (P : SmoothPacket) (z : CuspCylinder) : ℂ :=
  ∑ k ∈ P.modes, frequency k * AddCircle.fourier k z.1 * P.profile k (z.2 : ℝ)

def SmoothPacket.dy (P : SmoothPacket) (z : CuspCylinder) : ℂ :=
  ∑ k ∈ P.modes, AddCircle.fourier k z.1 * deriv (P.profile k) (z.2 : ℝ)

def SmoothPacket.realLift (P : SmoothPacket) (p : ℝ × ℝ) : ℂ :=
  ∑ k ∈ P.modes, AddCircle.fourier k (p.1 : UnitAddCircle) * P.profile k p.2

def SmoothPacket.realDx (P : SmoothPacket) (p : ℝ × ℝ) : ℂ :=
  ∑ k ∈ P.modes, frequency k * AddCircle.fourier k (p.1 : UnitAddCircle) * P.profile k p.2

def SmoothPacket.realDy (P : SmoothPacket) (p : ℝ × ℝ) : ℂ :=
  ∑ k ∈ P.modes, AddCircle.fourier k (p.1 : UnitAddCircle) * deriv (P.profile k) p.2

theorem SmoothPacket.joint_smooth (P : SmoothPacket) : ContDiff ℝ ∞ P.realLift := by
  apply ContDiff.sum
  intro k hk
  exact ((character_smooth k).comp contDiff_fst).mul ((P.smooth_profile k).comp contDiff_snd)

theorem SmoothPacket.joint_smooth_dx (P : SmoothPacket) : ContDiff ℝ ∞ P.realDx := by
  apply ContDiff.sum
  intro k hk
  exact (contDiff_const.mul ((character_smooth k).comp contDiff_fst)).mul
    ((P.smooth_profile k).comp contDiff_snd)

theorem SmoothPacket.joint_smooth_dy (P : SmoothPacket) : ContDiff ℝ ∞ P.realDy := by
  apply ContDiff.sum
  intro k hk
  exact ((character_smooth k).comp contDiff_fst).mul
    ((contDiff_infty_iff_deriv.mp (P.smooth_profile k)).2.comp contDiff_snd)

theorem SmoothPacket.horizontal_hasDerivAt (P : SmoothPacket) (y t : ℝ) :
    HasDerivAt (fun x : ℝ => P.realLift (x, y)) (P.realDx (t, y)) t := by
  apply HasDerivAt.fun_sum
  intro k hk
  simpa only [frequency, Complex.ofReal_one, div_one] using
    (AddCircle.hasDerivAt_fourier (1 : ℝ) k t).mul_const (P.profile k y)

theorem SmoothPacket.vertical_hasDerivAt (P : SmoothPacket) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => P.realLift (x, t)) (P.realDy (x, y)) y := by
  apply HasDerivAt.fun_sum
  intro k hk
  exact ((P.smooth_profile k).differentiable (by simp) y).hasDerivAt.const_mul _

theorem SmoothPacket.periodic (P : SmoothPacket) (y : ℝ) :
    Function.Periodic (fun x : ℝ => P.realLift (x, y)) 1 := by
  intro x
  simp only [SmoothPacket.realLift, AddCircle.coe_add_period]

theorem SmoothPacket.continuous_value (P : SmoothPacket) : Continuous P.value := by
  apply continuous_finsetSum
  intro k hk
  exact ((AddCircle.fourier k).continuous.comp continuous_fst).mul
    ((P.smooth_profile k).continuous.comp (continuous_subtype_val.comp continuous_snd))

theorem SmoothPacket.continuous_dx (P : SmoothPacket) : Continuous P.dx := by
  apply continuous_finsetSum
  intro k hk
  exact (continuous_const.mul ((AddCircle.fourier k).continuous.comp continuous_fst)).mul
    ((P.smooth_profile k).continuous.comp (continuous_subtype_val.comp continuous_snd))

theorem SmoothPacket.continuous_dy (P : SmoothPacket) : Continuous P.dy := by
  apply continuous_finsetSum
  intro k hk
  exact ((AddCircle.fourier k).continuous.comp continuous_fst).mul
    ((contDiff_infty_iff_deriv.mp (P.smooth_profile k)).2.continuous.comp
      (continuous_subtype_val.comp continuous_snd))

def SmoothPacket.supportCylinder (P : SmoothPacket) : Set CuspCylinder :=
  Set.univ ×ˢ {y : PositiveHeight | (y : ℝ) ∈ P.heightSupport}

theorem SmoothPacket.supportCylinder_compact (P : SmoothPacket) :
    IsCompact P.supportCylinder := by
  apply isCompact_univ.prod
  apply Subtype.isCompact_iff.mpr
  have he : ((↑) : PositiveHeight → ℝ) ''
      {y : PositiveHeight | (y : ℝ) ∈ P.heightSupport} = P.heightSupport := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, P.positive_heightSupport hy⟩, hy, rfl⟩
  rw [he]
  exact P.compact_heightSupport

theorem SmoothPacket.value_zero_outside (P : SmoothPacket) (z : CuspCylinder)
    (hz : (z.2 : ℝ) ∉ P.heightSupport) : P.value z = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  rw [image_eq_zero_of_notMem_tsupport (fun h => hz (P.profile_support k h)), mul_zero]

theorem SmoothPacket.dx_zero_outside (P : SmoothPacket) (z : CuspCylinder)
    (hz : (z.2 : ℝ) ∉ P.heightSupport) : P.dx z = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  rw [image_eq_zero_of_notMem_tsupport (fun h => hz (P.profile_support k h)), mul_zero]

theorem SmoothPacket.dy_zero_outside (P : SmoothPacket) (z : CuspCylinder)
    (hz : (z.2 : ℝ) ∉ P.heightSupport) : P.dy z = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  rw [deriv_of_notMem_tsupport (fun h => hz (P.profile_support k h)), mul_zero]

theorem SmoothPacket.compact_of_height_support (P : SmoothPacket)
    {F : CuspCylinder → ℂ} (hF : ∀ z, (z.2 : ℝ) ∉ P.heightSupport → F z = 0) :
    HasCompactSupport F := by
  apply P.supportCylinder_compact.of_isClosed_subset isClosed_tsupport
  apply closure_minimal _ P.supportCylinder_compact.isClosed
  intro z hz
  exact ⟨mem_univ _, by by_contra h; exact hz (hF z h)⟩

theorem SmoothPacket.value_memLp (P : SmoothPacket) (a : ℝ) :
    MemLp P.value 2 (functionMeasure a) :=
  (P.continuous_value.memLp_of_hasCompactSupport
    (P.compact_of_height_support P.value_zero_outside)).mono_measure Measure.restrict_le_self

theorem SmoothPacket.dx_memLp (P : SmoothPacket) (a : ℝ) :
    MemLp P.dx 2 (derivativeMeasure a) :=
  (P.continuous_dx.memLp_of_hasCompactSupport
    (P.compact_of_height_support P.dx_zero_outside)).mono_measure Measure.restrict_le_self

theorem SmoothPacket.dy_memLp (P : SmoothPacket) (a : ℝ) :
    MemLp P.dy 2 (derivativeMeasure a) :=
  (P.continuous_dy.memLp_of_hasCompactSupport
    (P.compact_of_height_support P.dy_zero_outside)).mono_measure Measure.restrict_le_self

theorem SmoothPacket.mean_zero (P : SmoothPacket) (y : PositiveHeight) :
    (∫ x : UnitAddCircle, P.value (x, y) ∂AddCircle.haarAddCircle) = 0 := by
  rw [show (fun x : UnitAddCircle => P.value (x, y)) =
    fun x => ∑ k ∈ P.modes, AddCircle.fourier k x * P.profile k (y : ℝ) from rfl]
  rw [integral_finsetSum _ (fun k hk =>
    ((AddCircle.fourier k).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).mul_const _)]
  apply Finset.sum_eq_zero
  intro k hk
  rw [integral_mul_const]
  have h := congrFun (AddCircle.fourierCoeff_fourier (T := (1 : ℝ)) k) 0
  have hz : (∫ x : UnitAddCircle, AddCircle.fourier k x ∂AddCircle.haarAddCircle) = 0 := by
    simpa [AddCircle.fourierCoeff, AddCircle.fourier_zero, P.modes_nonzero k hk,
      Ne.symm (P.modes_nonzero k hk)] using h
  rw [hz, zero_mul]

def SmoothPacket.classicalPair (P : SmoothPacket) (a : ℝ) : ClassicalPair 1 a where
  function := P.value
  derivative := P.dx
  continuous_function := P.continuous_value
  continuous_derivative := P.continuous_dx
  hasDeriv := fun y hy t => by
    simpa only [Complex.ofReal_one, one_mul, SmoothPacket.realLift, SmoothPacket.realDx,
      SmoothPacket.value, SmoothPacket.dx] using P.horizontal_hasDerivAt (y : ℝ) t
  mean_zero := fun y hy => P.mean_zero y
  function_memLp := P.value_memLp a
  derivative_memLp := P.dx_memLp a

def SmoothPacket.coordinates (P : SmoothPacket) (a : ℝ) : FunctionL2 a × DerivativeL2 a :=
  (P.classicalPair a).coordinates

def smoothPacketCore (a : ℝ) : Set (FunctionL2 a × DerivativeL2 a) :=
  Set.range (fun P : SmoothPacket => P.coordinates a)

end
end ImbalancedChen.Part3.JointSmoothFiniteCuspPackets20261026b
