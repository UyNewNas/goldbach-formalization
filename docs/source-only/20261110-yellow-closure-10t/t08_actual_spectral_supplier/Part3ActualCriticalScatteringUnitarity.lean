import ImbalancedChen.Part3ActualReflectedCuspSpans
import ImbalancedChen.Part3ActualContinuousSpatialProfiles
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! The functional equation and both unitarity identities of the critical
scattering matrix of the original positive level. The entries are the
continued physical outgoing constants of the same normalized parabolics. -/
namespace ImbalancedChen.Part3.ActualCriticalScatteringUnitarity20261110

noncomputable section
open Set Filter Topology Complex Matrix Matrix.SpecialLinearGroup UpperHalfPlane MeasureTheory
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualCharacterCuspExpansion20261110 ActualCuspDenominatorClasses20261110
open ActualReflectedCuspSpans20261110 ActualCriticalScatteringReciprocity20261110
open ActualCriticalScatteringEntry20261110 ActualCriticalCuspEvaluation20261110
open ActualParabolicScatteringRows20261110 ActualYoungCriticalCusps20261110
open ActualContinuousSpatialProfiles20261110 CompletedEisensteinSpatialMaass
open Gamma0GeneralCuspUnitPeriod20261025a ActualEisensteinFourierInterchange20261025a

local instance (N : ℕ) : DecidableEq (CuspRowClass N) := Classical.decEq _

def scatteringMatrix (N : ℕ) [NeZero N] (t : ℝ) : Matrix (CuspRowClass N) (CuspRowClass N) ℂ :=
  fun a b => continuedEntry N (NeZero.pos N) (classFrame a) (classFrame b) (criticalPoint t)

private theorem critical_regular (t : ℝ) :
    1/2 ≤ (criticalPoint t).re ∧ criticalPoint t ≠ 0 ∧ criticalPoint t ≠ 1 := by
  have h : (criticalPoint t).re = 1/2 := by norm_num [criticalPoint,Complex.mul_re]
  refine ⟨h.ge,?_,?_⟩ <;> intro e <;> norm_num [e] at h

private theorem reflected_point (t : ℝ) : criticalPoint (-t) = 1-criticalPoint t := by
  unfold criticalPoint
  push_cast
  ring

private theorem separate_powers {s a b c d : ℂ} (hs : s ≠ 0) (h1 : 1-s ≠ 0) (hd : 2*s-1 ≠ 0)
    (h : ∀ y : ℝ, 0 < y → a*(y : ℂ)^s+b*(y : ℂ)^(1-s) =
      c*(y : ℂ)^s+d*(y : ℂ)^(1-s)) : a = c ∧ b = d := by
  have hv : a+b = c+d := by simpa using h 1 zero_lt_one
  have p := heightPower_hasDerivAt s hs (y := 1) zero_lt_one
  have q := heightPower_hasDerivAt (1-s) h1 (y := 1) zero_lt_one
  have hL := (p.const_mul a).add (q.const_mul b)
  have hR := (p.const_mul c).add (q.const_mul d)
  have he : (fun y : ℝ => c*(y : ℂ)^s+d*(y : ℂ)^(1-s)) =ᶠ[𝓝 1]
      (fun y : ℝ => a*(y : ℂ)^s+b*(y : ℂ)^(1-s)) := by
    filter_upwards [eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)] with y hy using (h y hy).symm
  have hv' : a*s+b*(1-s) = c*s+d*(1-s) := by
    simpa [heightFirst] using (hL.congr_of_eventuallyEq he).unique hR
  have hk : (a-c)*(2*s-1) = 0 := by linear_combination hv' - (1-s)*hv
  have hac := sub_eq_zero.mp ((mul_eq_zero.mp hk).resolve_right hd)
  rw [hac] at hv
  exact ⟨hac,add_left_cancel hv⟩

private theorem column_mean (N : ℕ) [NeZero N] (t : ℝ) (a b : CuspRowClass N)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, nativeColumn N t a
      (normalizedScaling N (NeZero.pos N) (classFrame b) • horizontalPoint y hy x)) =
      (1 : Matrix (CuspRowClass N) (CuspRowClass N) ℂ) a b*(y : ℂ)^(criticalPoint t) +
        scatteringMatrix N t a b*(y : ℂ)^(1-criticalPoint t) := by
  classical
  have HG : nativeFrameOrbit N (classFrame b) = nativeFrameOrbit N (classFrame a) ↔ b = a :=
    (nativeCuspEquiv N).injective.eq_iff
  have hI : ActualParabolicScatteringRows20261110.incoming N (classFrame a) (classFrame b)
      (criticalPoint t) y = (1 : Matrix (CuspRowClass N) (CuspRowClass N) ℂ) a b*
        (y : ℂ)^(criticalPoint t) := by
    by_cases e : a = b <;> simp [ActualParabolicScatteringRows20261110.incoming,HG,Matrix.one_apply,e,eq_comm]
  simpa only [nativeColumn,scatteringMatrix,hI] using
    critical_native_constant_term N (NeZero.pos N) (classFrame a) (classFrame b) t y hy

private theorem row_equations (N : ℕ) [NeZero N] (t : ℝ) (ht : t ≠ 0)
    (a : CuspRowClass N) (u : CuspRowClass N → ℂ)
    (h : ∀ z : ℍ, nativeColumn N t a z = ∑ k, u k*nativeColumn N (-t) k z)
    (b : CuspRowClass N) :
    (1 : Matrix (CuspRowClass N) (CuspRowClass N) ℂ) a b =
        ∑ k, u k*scatteringMatrix N (-t) k b ∧ scatteringMatrix N t a b = u b := by
  let s := criticalPoint t
  obtain ⟨_,hs,h1⟩ := critical_regular t
  have hd : 2*s-1 ≠ 0 := by
    intro e
    have H := congrArg Complex.im e
    simp [s,criticalPoint,Complex.mul_im,Complex.mul_re] at H
    exact ht (by linarith)
  apply separate_powers hs (sub_ne_zero.mpr (Ne.symm h1)) hd
  intro y hy
  let Z := fun x : ℝ => normalizedScaling N (NeZero.pos N) (classFrame b) • horizontalPoint y hy x
  have hZ : Continuous Z := by
    change Continuous (fun x : ℝ => SpecialLinearGroup.mapGL ℝ
      (normalizedScaling N (NeZero.pos N) (classFrame b)) • horizontalPoint y hy x)
    apply (continuous_const_smul _).comp
    unfold horizontalPoint
    fun_prop
  have hc (k : CuspRowClass N) : Continuous (nativeColumn N (-t) k) :=
    native_spatial ((youngCuspEquiv N).symm (nativeCuspEquiv N k)) (-t)
  have hlin : (∫ x in (0 : ℝ)..1, nativeColumn N t a (Z x)) =
      ∑ k, u k*(∫ x in (0 : ℝ)..1, nativeColumn N (-t) k (Z x)) := by
    simp_rw [h]
    rw [intervalIntegral.integral_finsetSum (fun k _ =>
      (((hc k).comp hZ).const_mul (u k)).intervalIntegrable 0 1)]
    simp only [intervalIntegral.integral_const_mul]
  change (∫ x in (0 : ℝ)..1, nativeColumn N t a
      (normalizedScaling N (NeZero.pos N) (classFrame b) • horizontalPoint y hy x)) =
    ∑ k, u k*(∫ x in (0 : ℝ)..1, nativeColumn N (-t) k
      (normalizedScaling N (NeZero.pos N) (classFrame b) • horizontalPoint y hy x)) at hlin
  rw [column_mean] at hlin
  simp_rw [column_mean N (-t) _ b y hy,reflected_point,show 1-(1-criticalPoint t) = criticalPoint t by ring] at hlin
  rw [hlin,Finset.sum_mul]
  conv_rhs => rw [add_comm]
  simp_rw [mul_add,← mul_assoc,Finset.sum_add_distrib]
  congr 1
  simp [Matrix.one_apply,ite_mul,mul_ite]

private theorem off_center (N : ℕ) [NeZero N] (t : ℝ) (ht : t ≠ 0) (a : CuspRowClass N) :
    (∀ z : ℍ, nativeColumn N t a z =
      ∑ b, scatteringMatrix N t a b*nativeColumn N (-t) b z) ∧
    (∀ c : CuspRowClass N, (scatteringMatrix N t*scatteringMatrix N (-t)) a c =
      (1 : Matrix (CuspRowClass N) (CuspRowClass N) ℂ) a c) := by
  obtain ⟨u,H⟩ := reflected_columns N t ht a
  have J := row_equations N t ht a u H
  have E : u = fun b => scatteringMatrix N t a b := funext (fun b => (J b).2.symm)
  refine ⟨?_,?_⟩
  · intro z
    simpa only [E] using H z
  · intro c
    simpa only [Matrix.mul_apply,E] using (J c).1.symm

private theorem entry_continuous (N : ℕ) [NeZero N] (a b : CuspRowClass N) :
    Continuous (fun t : ℝ => scatteringMatrix N t a b) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have ht := critical_regular t
  exact ((continuedEntry_regularity N (NeZero.pos N) (classFrame a) (classFrame b)).2
    (criticalPoint t) ht.1 ht.2.2).continuousAt.comp (show Continuous criticalPoint by
      unfold criticalPoint
      fun_prop).continuousAt

private theorem column_continuous (N : ℕ) [NeZero N] (a : CuspRowClass N) (z : ℍ) :
    Continuous (fun t : ℝ => nativeColumn N t a z) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have ht := critical_regular t
  exact (parameterFamily_differentiable ((youngCuspEquiv N).symm (nativeCuspEquiv N a))
    z (criticalPoint t) ht.1 ht.2.2).continuousAt.comp (show Continuous criticalPoint by
      unfold criticalPoint
      fun_prop).continuousAt

/-- The original orbit-indexed Eisenstein functions satisfy their
physical functional equation pointwise in space at every critical
height. Continuity passes through the coalescing powers at the center. -/
theorem actual_critical_functional_equation (N : ℕ) [NeZero N] (t : ℝ) (a : CuspRowClass N)
    (z : ℍ) : nativeColumn N t a z =
      ∑ b, scatteringMatrix N t a b*nativeColumn N (-t) b z := by
  have E := Continuous.ext_on (dense_compl_singleton (0 : ℝ)) (column_continuous N a z)
    (continuous_finsetSum _ (fun b _ => (entry_continuous N a b).mul
      ((column_continuous N b z).comp continuous_neg))) (fun v hv => (off_center N v hv a).1 z)
  exact congrFun E t

/-- Exact matrix product of the physical native scattering and its
reflected parameter. This includes t=0 without dividing by 2it. -/
theorem reflected_product (N : ℕ) [NeZero N] (t : ℝ) :
    scatteringMatrix N t*scatteringMatrix N (-t) = 1 := by
  ext a c
  have hc : Continuous (fun v : ℝ => (scatteringMatrix N v*scatteringMatrix N (-v)) a c) := by
    simp only [Matrix.mul_apply]
    exact continuous_finsetSum _ (fun b _ => (entry_continuous N a b).mul
      ((entry_continuous N b c).comp continuous_neg))
  have E := Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hc
    (continuous_const (y := (1 : Matrix (CuspRowClass N) (CuspRowClass N) ℂ) a c))
    (fun v hv => (off_center N v hv a).2 c)
  exact congrFun E t

theorem reflected_adjoint (N : ℕ) [NeZero N] (t : ℝ) :
    scatteringMatrix N (-t) = (scatteringMatrix N t).conjTranspose := by
  ext a b
  exact critical_entry_adjoint N (NeZero.pos N) (classFrame a) (classFrame b) t

/-- Both unitary identities for the actual finite scattering matrix in
the unit-leading, width-normalized native cusp basis at original level. -/
theorem actual_critical_scattering_unitary (N : ℕ) [NeZero N] (t : ℝ) :
    scatteringMatrix N t*(scatteringMatrix N t).conjTranspose = 1 ∧
    (scatteringMatrix N t).conjTranspose*scatteringMatrix N t = 1 := by
  constructor
  · rw [← reflected_adjoint,reflected_product]
  · rw [← reflected_adjoint]
    simpa only [neg_neg] using reflected_product N (-t)

end
end ImbalancedChen.Part3.ActualCriticalScatteringUnitarity20261110
