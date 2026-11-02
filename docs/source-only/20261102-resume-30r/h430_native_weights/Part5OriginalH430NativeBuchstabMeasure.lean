import ImbalancedChen.Part5OriginalH430BuchstabPhysicalBudget
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual native prime coordinate is x, not w.  This file identifies its
Lebesgue integral with the Q Buchstab coefficient by an injective change
of variables, and transports integrability as well.  The native set has
the literal LocalDomain and closed FloorAtom filter.  It is not the full
Program Member set or the arithmetic parent-Theta measure.
-/

namespace ImbalancedChen.Part5OriginalH430NativeBuchstabMeasure

noncomputable section
open Set MeasureTheory Filter Topology Classical
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P5OriginalActionMassBound
open P5OriginalFeedbackTableKernels Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430PhysicalMassPerturbation
open Part5OriginalH430BuchstabPhysicalBudget
open Part5OriginalH430MovingBuchstabAtoms
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430DescendantLimits

/-- Only the one active native prime coordinate is integrated. -/
def nativePoint (x : ℝ) : Point := fun i => if i = 0 then x else 0

def nativeMap (p : PhysicalNode) (w : ℝ) : ℝ := residual p / (w+1)

def nativeAtomDomain (upper : Bool) (p : PhysicalNode) (b : FloorAtom) : Set ℝ :=
  {x | LocalDomain p (buchstabShape upper) (nativePoint x) ∧
    (perform p (buchstabShape upper) (nativePoint x)).argument ∈ tableAtomSet upper b}

def nativeAtomCoefficient (upper : Bool) (p : PhysicalNode) (b : FloorAtom) : ℝ :=
  ∫ x in nativeAtomDomain upper p b,
    physicalWeight (perform p (buchstabShape upper) (nativePoint x))

@[simp] theorem nativePoint_zero (x : ℝ) : nativePoint x 0 = x := by
  simp [nativePoint]

@[simp] theorem nativePoint_nativeMap (p : PhysicalNode) (w : ℝ) :
    nativePoint (nativeMap p w) = buchstabPoint p w := rfl

theorem nativeMap_left_inverse {p : PhysicalNode} (hL : 0 < residual p)
    {x : ℝ} (hx : 0 < x) :
    nativeMap p (buchstabArgument p (nativePoint x)) = x := by
  simp only [nativeMap, buchstabArgument, nativePoint_zero, sub_add_cancel]
  field_simp [hL.ne', hx.ne'] <;> ring

theorem native_local_query_bounds {upper : Bool} {p : PhysicalNode} {x : ℝ}
    (hd : LocalDomain p (buchstabShape upper) (nativePoint x)) :
    0 < x ∧ buchstabArgument p (nativePoint x) ∈ buchstabAmbient := by
  cases upper
  · change 0 < residual p ∧ 2 ≤ p.argument ∧
      OneGate p x ∧ buchstabArgument p (nativePoint x) ∈
        buchstabLowerDomain p.argument at hd
    refine ⟨hd.2.2.1.1, ?_⟩
    change 1 ≤ buchstabArgument p (nativePoint x) ∧
      buchstabArgument p (nativePoint x) ≤ 5
    have hq := hd.2.2.2
    change p.argument-1 ≤ buchstabArgument p (nativePoint x) ∧
      buchstabArgument p (nativePoint x) ≤ 5 at hq
    exact ⟨by linarith [hd.2.1, hq.1], hq.2⟩
  · change 0 < residual p ∧ OneGate p x ∧
      buchstabArgument p (nativePoint x) ∈ buchstabUpperDomain p.argument at hd
    refine ⟨hd.2.1.1, ?_⟩
    have hq := hd.2.2
    change max 2 (p.argument-1) ≤ buchstabArgument p (nativePoint x) ∧
      buchstabArgument p (nativePoint x) ≤ 5 at hq
    exact ⟨(by norm_num : (1 : ℝ) ≤ 2).trans
      ((le_max_left _ _).trans hq.1), hq.2⟩

/-- This is an equality of native sets, including the scalar knot atoms.
The lower direction requires s >= 2 and therefore includes s = 2. -/
theorem nativeAtomDomain_eq_image {upper : Bool} {p : PhysicalNode}
    (hL : 0 < residual p) (hC : 0 < p.ceiling) (hg : directionGuard upper p)
    (b : FloorAtom) :
    nativeAtomDomain upper p b =
      nativeMap p '' (Icc (physicalStart upper p) 5 ∩ tableAtomSet upper b) := by
  rw [← physicalAtomPullback_eq hL hC hg b]
  ext x
  constructor
  · rintro ⟨hd, hb⟩
    obtain ⟨hx, hw⟩ := native_local_query_bounds hd
    let w := buchstabArgument p (nativePoint x)
    have hinv : nativeMap p w = x := nativeMap_left_inverse hL hx
    refine ⟨w, ?_, hinv⟩
    have hp : buchstabPoint p w = nativePoint x := by
      rw [← nativePoint_nativeMap, hinv]
    exact ⟨hw, hp.symm ▸ hd, hp.symm ▸ hb⟩
  · rintro ⟨w, hw, rfl⟩
    change LocalDomain p (buchstabShape upper) (nativePoint (nativeMap p w)) ∧ _
    simpa only [nativePoint_nativeMap] using hw.2

theorem nativeMap_hasDerivAt {p : PhysicalNode} {w : ℝ} (hw : 1 ≤ w) :
    HasDerivAt (nativeMap p) (-(residual p/(w+1)^2)) w := by
  have hw0 : w+1 ≠ 0 := by linarith
  have hd := (hasDerivAt_const w (residual p)).div
    ((hasDerivAt_id w).add_const 1) hw0
  convert hd using 1 <;> simp [nativeMap] <;> ring

theorem nativeMap_injOn {p : PhysicalNode} (hL : 0 < residual p) :
    InjOn (nativeMap p) buchstabAmbient := by
  intro w hw v hv he
  have hw0 : w+1 ≠ 0 := by linarith [hw.1]
  have hv0 : v+1 ≠ 0 := by linarith [hv.1]
  have hcross := (div_eq_div_iff hw0 hv0).mp he
  exact (add_right_cancel (mul_left_cancel₀ hL.ne' hcross)).symm

/-- Absolute derivative of the actual decreasing native coordinate map. -/
theorem nativeMap_abs_deriv {p : PhysicalNode} (hL : 0 < residual p) (w : ℝ) :
    |-(residual p/(w+1)^2)| = residual p/(w+1)^2 := by
  rw [abs_neg, abs_of_nonneg (div_nonneg hL.le (sq_nonneg _))]

/-- Each original closed atom is measurable also in native coordinates.
The inverse query is totalized, while its valid image always has x > 0. -/
theorem nativeAtomDomain_measurable {upper : Bool} {p : PhysicalNode}
    (hL : 0 < residual p) (hC : 0 < p.ceiling) (hg : directionGuard upper p)
    (b : FloorAtom) : MeasurableSet (nativeAtomDomain upper p b) := by
  have he : nativeAtomDomain upper p b =
      Ioi (0 : ℝ) ∩ (fun x : ℝ => residual p/x-1) ⁻¹'
        (Icc (physicalStart upper p) 5 ∩ tableAtomSet upper b) := by
    rw [nativeAtomDomain_eq_image hL hC hg b]
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw1 := (physicalStart_ge_one hg).trans hw.1.1
      refine ⟨div_pos hL (by linarith), ?_⟩
      have hquery := buchstabPoint_query hL hw1
      have hq : residual p / nativeMap p w - 1 = w := by
        simpa only [buchstabArgument, buchstabPoint_zero, nativeMap] using hquery
      change residual p / nativeMap p w - 1 ∈ _
      rw [hq]
      exact hw
    · rintro ⟨hx, hw⟩
      refine ⟨residual p/x-1, hw, ?_⟩
      exact nativeMap_left_inverse hL hx
  rw [he]
  exact measurableSet_Ioi.inter
    ((measurableSet_Icc.inter (measurableSet_tableAtomSet upper b)).preimage
      ((measurable_const.div measurable_id).sub measurable_const))

/-- Integrability is transported through the derivative theorem, not
postulated from the desired native coefficient estimate. -/
theorem nativeAtom_integrable {upper : Bool} {p : PhysicalNode}
    (hL : 0 < residual p) (hC : 0 < p.ceiling) (hg : directionGuard upper p)
    (b : FloorAtom) :
    IntegrableOn (fun x => physicalWeight (perform p (buchstabShape upper) (nativePoint x)))
      (nativeAtomDomain upper p b) := by
  let S := Icc (physicalStart upper p) 5 ∩ tableAtomSet upper b
  have hS : MeasurableSet S := measurableSet_Icc.inter (measurableSet_tableAtomSet upper b)
  have hsub : S ⊆ buchstabAmbient := fun _ hw =>
    ⟨(physicalStart_ge_one hg).trans hw.1.1, hw.1.2⟩
  rw [nativeAtomDomain_eq_image hL hC hg b]
  apply (integrableOn_image_iff_integrableOn_abs_deriv_smul hS
    (fun w hw => (nativeMap_hasDerivAt (hsub hw).1).hasDerivWithinAt)
    ((nativeMap_injOn hL).mono hsub) _).mpr
  have hi : IntegrableOn (fun w => physicalWeight p * buchstabKernel w) S :=
    ((buchstabKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      inter_subset_left).const_mul _
  apply hi.congr_fun _ hS
  intro w hw
  simp only [smul_eq_mul, nativeMap_abs_deriv hL, nativePoint_nativeMap]
  exact (actual_buchstab_Jacobian hL (hsub hw)).symm

/-- Actual Lebesgue change of variables from x to w.  For two different
parents this theorem is applied with two different nativeMap functions. -/
theorem nativeAtomCoefficient_eq {upper : Bool} {p : PhysicalNode}
    (hL : 0 < residual p) (hC : 0 < p.ceiling) (hg : directionGuard upper p)
    (b : FloorAtom) : nativeAtomCoefficient upper p b = coefficient upper p b := by
  let S := Icc (physicalStart upper p) 5 ∩ tableAtomSet upper b
  have hS : MeasurableSet S := measurableSet_Icc.inter (measurableSet_tableAtomSet upper b)
  have hsub : S ⊆ buchstabAmbient := fun _ hw =>
    ⟨(physicalStart_ge_one hg).trans hw.1.1, hw.1.2⟩
  have hchange := integral_image_eq_integral_abs_deriv_smul hS
    (fun w hw => (nativeMap_hasDerivAt (hsub hw).1).hasDerivWithinAt)
    ((nativeMap_injOn hL).mono hsub)
    (fun x => physicalWeight (perform p (buchstabShape upper) (nativePoint x)))
  unfold nativeAtomCoefficient
  rw [nativeAtomDomain_eq_image hL hC hg b]
  calc
    _ = ∫ w in S, |-(residual p/(w+1)^2)| •
        physicalWeight (perform p (buchstabShape upper) (nativePoint (nativeMap p w))) := hchange
    _ = ∫ w in S, physicalWeight p * buchstabKernel w := by
      apply setIntegral_congr_fun hS
      intro w hw
      simp only [smul_eq_mul, nativeMap_abs_deriv hL, nativePoint_nativeMap]
      exact actual_buchstab_Jacobian hL (hsub hw)
    _ = coefficient upper p b := by
      rw [integral_const_mul]
      simp only [coefficient, atomMass, startAtomDensity, integral_indicator hS]

/-- A difference of two original native integrals, with the two actual
parent maps and physical weights.  This is not same-x L1 convergence. -/
theorem nativeAtomCoefficient_difference_le {upper : Bool} {p q : PhysicalNode}
    (hLp : 0 < residual p) (hCp : 0 < p.ceiling) (hgp : directionGuard upper p)
    (hLq : 0 < residual q) (hCq : 0 < q.ceiling) (hgq : directionGuard upper q)
    (b : FloorAtom) :
    |nativeAtomCoefficient upper p b-nativeAtomCoefficient upper q b| ≤
      4*|physicalWeight p-physicalWeight q| +
        |physicalWeight q|*|physicalStart upper p-physicalStart upper q| := by
  rw [nativeAtomCoefficient_eq hLp hCp hgp, nativeAtomCoefficient_eq hLq hCq hgq]
  exact coefficient_difference_le hgp b

/-- Along the actual same-Program physical parents, the original native
integrals converge.  The two native substitutions need not coincide.
Full Member-filtered native L1 and outer parent integration are not asserted. -/
theorem actual_upper_nativeAtomCoefficient_tendsto (b : FloorAtom)
    {k : Root} {t lo hi : ℝ} (ht : t ∈ rootBand k) {mesh depth : ℕ}
    {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (sourceRoot k 0 t) code z) :
    Tendsto (fun n => nativeAtomCoefficient true (frozenDescendant n k t code z) b)
      atTop (𝓝 (nativeAtomCoefficient true (idealDescendant k t code z) b)) := by
  have hL := idealDescendant_residual_pos ht hz
  have hC := idealDescendant_ceiling_pos ht hz
  have he := (frozenDescendant_residual_tendsto ht code z).eventually (eventually_gt_nhds hL)
  have hw := ((frozenDescendant_weight_tendsto ht hz).sub tendsto_const_nhds).abs
  have hs := ((frozenDescendant_physicalStart_tendsto ht hz true).sub tendsto_const_nhds).abs
  have hb : Tendsto (fun n =>
      4*|physicalWeight (frozenDescendant n k t code z)-physicalWeight (idealDescendant k t code z)| +
      |physicalWeight (idealDescendant k t code z)| *
        |physicalStart true (frozenDescendant n k t code z)-physicalStart true (idealDescendant k t code z)|)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hw).add (tendsto_const_nhds.mul hs)
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  filter_upwards [he, hb.eventually (eventually_lt_nhds hepsilon)] with n hn hsmall
  rw [Real.dist_eq]
  exact (nativeAtomCoefficient_difference_le hn
    (by simpa only [frozenDescendant_ceiling] using hC) trivial hL hC trivial b).trans_lt hsmall

end
end ImbalancedChen.Part5OriginalH430NativeBuchstabMeasure
