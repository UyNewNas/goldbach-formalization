import ImbalancedChen.Part3CuspModePhysicalCoreForm
import ImbalancedChen.Part3RadialClosedEnergyQuarterShear
import ImbalancedChen.Part3WeightedHeightNativeUnitary
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED. New physical closed-form construction.

The physical energy coordinates are (f, y*f', a*y*f), all in the actual
height L2(dy/y^2). Their compact-core span is closed in the native three
coordinate Hilbert space. The explicit coordinate shear and actual height
unitary identify this closure with the actual radial form domain.

The physical weak graph is defined by its physical energy pairing and
testing against the entire physical closed domain. It is NOT defined by
conjugating a radial operator. Its equality with the native graph of
A+1/4 is subsequently proved. No HOLD Liouville supplier is imported.
-/

namespace ImbalancedChen.Part3.CuspModeNativeClosedForm20261026a
noncomputable section
open Set MeasureTheory
open RadialSchrodingerL2Form20261025a
open CuspModePhysicalCoreForm20261026a
open RadialClosedEnergyQuarterShear20261026a
open WeightedHeightNativeUnitary20261026a
open CuspCylinderMeasure20261024z WeightedHeightLogMeasure20261026a

/-- The usual physical smooth compact height tests; values outside y>0
have no role. Compactness is in the positive-height subtype. -/
structure PhysicalHeightTest where
  function : ℝ → ℂ
  smooth : ContDiffOn ℝ ∞ function (Ioi 0)
  compact : HasCompactSupport (fun y : PositiveHeight => function y)

theorem physicalLift_smoothOn (a : ℝ) (ha : 0 < a) (T : RadialTest) :
    ContDiffOn ℝ ∞ (physicalLift a T.function) (Ioi 0) := by
  have hs : ContDiffOn ℝ ∞ (fun y : ℝ => Real.sqrt y) (Ioi 0) :=
    contDiffOn_id.sqrt (fun _ hy => ne_of_gt hy)
  have hl : ContDiffOn ℝ ∞ (fun y : ℝ => Real.log (a * y)) (Ioi 0) :=
    (contDiffOn_const.mul contDiffOn_id).log (fun _ hy => (mul_pos ha hy).ne')
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn hs).mul
    (T.smooth.comp_contDiffOn hl)

def physicalTestOfRadial (a : ℝ) (ha : 0 < a) (T : RadialTest) : PhysicalHeightTest :=
  ⟨physicalLift a T.function, physicalLift_smoothOn a ha T, physicalLift_compact ha T⟩

def radialTestOfPhysical (a : ℝ) (ha : 0 < a) (T : PhysicalHeightTest) : RadialTest where
  function := heightToRadialFunction a ha (fun y : PositiveHeight => T.function y)
  smooth := by
    have hc : ContDiff ℝ ∞ (heightChart a) := Real.contDiff_exp.div_const a
    have hf := T.smooth.comp_contDiff hc (heightChart_pos ha)
    have hw : ContDiff ℝ ∞ (fun r : ℝ => (heightForwardAmplitude a r : ℂ)) := by
      unfold heightForwardAmplitude
      fun_prop
    exact hw.mul hf
  compact := (T.compact.comp_homeomorph (heightHomeomorph a ha)).mul_left

/-- Every usual physical smooth compact profile occurs in the chosen
radial-image core. Thus the closure is not built from a smaller test class. -/
theorem physical_test_is_lift (a : ℝ) (ha : 0 < a) (T : PhysicalHeightTest)
    (y : PositiveHeight) :
    physicalLift a (radialTestOfPhysical a ha T).function y = T.function y :=
  congrFun (radialToHeightFunction_heightToRadialFunction a ha
    (fun z : PositiveHeight => T.function z)) y

abbrev PhysicalEnergyHilbert := PiLp 2 (fun _ : Fin 3 => PhysicalHeightL2)

/-- Inverse physical coordinate map, with the genuine sqrt(y) weight.
The middle coordinate is the affine derivative caused by that weight. -/
def physicalTripleEquiv (a : ℝ) (ha : 0 < a) :
    RadialEnergyHilbert ≃L[ℂ] PhysicalEnergyHilbert where
  toFun x := WithLp.toLp 2 ![
    (weightedHeightUnitary a ha).symm (x 0),
    (weightedHeightUnitary a ha).symm (x 1 + (1 / 2 : ℂ) • x 0),
    (weightedHeightUnitary a ha).symm (x 2)]
  invFun y := WithLp.toLp 2 ![
    weightedHeightUnitary a ha (y 0),
    weightedHeightUnitary a ha (y 1) - (1 / 2 : ℂ) • weightedHeightUnitary a ha (y 0),
    weightedHeightUnitary a ha (y 2)]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv y := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp <;> module
  map_smul' c x := by ext i; fin_cases i <;> simp <;> module
  continuous_toFun := PiLp.continuous_toLp.comp (continuous_pi fun i => by
    fin_cases i <;> fun_prop)
  continuous_invFun := PiLp.continuous_toLp.comp (continuous_pi fun i => by
    fin_cases i <;> fun_prop)

def physicalEnergyCoreVector (a : ℝ) (ha : 0 < a) (T : RadialTest) :
    PhysicalEnergyHilbert := physicalTripleEquiv a ha (radialEnergyCoreVector 1 T)

def physicalEnergyCoreSpan (a : ℝ) (ha : 0 < a) : Submodule ℂ PhysicalEnergyHilbert :=
  Submodule.span ℂ (range (physicalEnergyCoreVector a ha))

/-- Actual graph-norm closure of the physical compact-core coordinate vectors. -/
def physicalClosedEnergyDomain (a : ℝ) (ha : 0 < a) : Submodule ℂ PhysicalEnergyHilbert :=
  (physicalEnergyCoreSpan a ha).topologicalClosure

instance physicalClosedEnergyDomain_complete (a : ℝ) (ha : 0 < a) :
    CompleteSpace (physicalClosedEnergyDomain a ha) := inferInstance

theorem physical_core_span_eq_map (a : ℝ) (ha : 0 < a) :
    physicalEnergyCoreSpan a ha =
      (radialEnergyCoreSpan 1).map (physicalTripleEquiv a ha).toLinearMap := by
  rw [physicalEnergyCoreSpan, radialEnergyCoreSpan, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨radialEnergyCoreVector 1 T, ⟨T, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨T, rfl⟩, rfl⟩
    exact ⟨T, rfl⟩

/-- Closure commutes with this actual invertible continuous energy-coordinate
map. The conclusion identifies the form domains, not merely their cores. -/
theorem physical_closed_domain_eq_map (a : ℝ) (ha : 0 < a) :
    physicalClosedEnergyDomain a ha =
      (radialClosedEnergyDomain 1).map (physicalTripleEquiv a ha).toLinearMap := by
  apply SetLike.ext'
  simp only [physicalClosedEnergyDomain, radialClosedEnergyDomain,
    Submodule.topologicalClosure_coe, Submodule.map_coe]
  rw [(physicalTripleEquiv a ha).toHomeomorph.image_closure]
  congr 1
  exact congrArg (fun p : Submodule ℂ PhysicalEnergyHilbert => (p : Set PhysicalEnergyHilbert))
    (physical_core_span_eq_map a ha)

def physicalClosedEnergyEquiv (a : ℝ) (ha : 0 < a) :
    radialClosedEnergyDomain 1 ≃L[ℂ] physicalClosedEnergyDomain a ha :=
  (physicalTripleEquiv a ha).ofSubmodules _ _ (physical_closed_domain_eq_map a ha).symm

def physicalClosedEmbedding (a : ℝ) (ha : 0 < a) :
    physicalClosedEnergyDomain a ha →L[ℂ] PhysicalHeightL2 :=
  (PiLp.proj 2 (fun _ : Fin 3 => PhysicalHeightL2) 0).comp
    (physicalClosedEnergyDomain a ha).subtypeL

def physicalClosedVertical (a : ℝ) (ha : 0 < a) :
    physicalClosedEnergyDomain a ha →L[ℂ] PhysicalHeightL2 :=
  (PiLp.proj 2 (fun _ : Fin 3 => PhysicalHeightL2) 1).comp
    (physicalClosedEnergyDomain a ha).subtypeL

def physicalClosedPotential (a : ℝ) (ha : 0 < a) :
    physicalClosedEnergyDomain a ha →L[ℂ] PhysicalHeightL2 :=
  (PiLp.proj 2 (fun _ : Fin 3 => PhysicalHeightL2) 2).comp
    (physicalClosedEnergyDomain a ha).subtypeL

theorem physicalClosedEmbedding_equiv (a : ℝ) (ha : 0 < a)
    (e : radialClosedEnergyDomain 1) :
    physicalClosedEmbedding a ha (physicalClosedEnergyEquiv a ha e) =
      (weightedHeightUnitary a ha).symm (radialPhysicalEmbedding 1 e) := by
  change (weightedHeightUnitary a ha).symm ((e : RadialEnergyHilbert) 0) = _
  simp [radialPhysicalEmbedding, energyPhysicalCoordinate]

theorem physicalClosedVertical_equiv (a : ℝ) (ha : 0 < a)
    (e : radialClosedEnergyDomain 1) :
    physicalClosedVertical a ha (physicalClosedEnergyEquiv a ha e) =
      (weightedHeightUnitary a ha).symm (radialHalfShiftedDerivative e) := by
  change (weightedHeightUnitary a ha).symm
      ((e : RadialEnergyHilbert) 1 + (1 / 2 : ℂ) • (e : RadialEnergyHilbert) 0) = _
  simp [radialHalfShiftedDerivative, radialClosedDerivative, radialPhysicalEmbedding,
    energyDerivativeCoordinate, energyPhysicalCoordinate]

theorem physicalClosedPotential_equiv (a : ℝ) (ha : 0 < a)
    (e : radialClosedEnergyDomain 1) :
    physicalClosedPotential a ha (physicalClosedEnergyEquiv a ha e) =
      (weightedHeightUnitary a ha).symm (radialClosedExponential 1 e) := rfl

theorem physicalClosedEmbedding_injective (a : ℝ) (ha : 0 < a) :
    Function.Injective (physicalClosedEmbedding a ha) := by
  intro x y h
  obtain ⟨d, rfl⟩ := (physicalClosedEnergyEquiv a ha).surjective x
  obtain ⟨e, rfl⟩ := (physicalClosedEnergyEquiv a ha).surjective y
  rw [physicalClosedEmbedding_equiv, physicalClosedEmbedding_equiv] at h
  have hde := radialPhysicalEmbedding_injective 1 (by norm_num)
    ((weightedHeightUnitary a ha).symm.injective h)
  exact congrArg (physicalClosedEnergyEquiv a ha) hde

theorem physicalClosedEmbedding_denseRange (a : ℝ) (ha : 0 < a) :
    DenseRange (physicalClosedEmbedding a ha) := by
  have hd := (weightedHeightUnitary a ha).symm.surjective.denseRange.comp
    (radialPhysicalEmbedding_denseRange 1 (by norm_num))
      (weightedHeightUnitary a ha).symm.continuous
  apply hd.mono
  rintro x ⟨e, rfl⟩
  exact ⟨physicalClosedEnergyEquiv a ha e, physicalClosedEmbedding_equiv a ha e⟩

def physicalClosedForm (a : ℝ) (ha : 0 < a)
    (d e : physicalClosedEnergyDomain a ha) : ℂ :=
  inner ℂ (physicalClosedVertical a ha d) (physicalClosedVertical a ha e) +
    inner ℂ (physicalClosedPotential a ha d) (physicalClosedPotential a ha e)

theorem physicalClosedForm_equiv (a : ℝ) (ha : 0 < a)
    (d e : radialClosedEnergyDomain 1) :
    physicalClosedForm a ha (physicalClosedEnergyEquiv a ha d)
      (physicalClosedEnergyEquiv a ha e) = radialQuarterForm d e := by
  unfold physicalClosedForm
  rw [physicalClosedVertical_equiv, physicalClosedVertical_equiv,
    physicalClosedPotential_equiv, physicalClosedPotential_equiv,
    (weightedHeightUnitary a ha).symm.inner_map_map,
    (weightedHeightUnitary a ha).symm.inner_map_map]
  rfl

/-- The physical form is closed: its energy plus 3/4 physical L2 pairing
is the inner product of the genuine complete radial energy space, under
the proved continuous linear equivalence of closed domains. -/
theorem physicalClosedForm_complete_energy (a : ℝ) (ha : 0 < a)
    (d e : radialClosedEnergyDomain 1) :
    physicalClosedForm a ha (physicalClosedEnergyEquiv a ha d)
      (physicalClosedEnergyEquiv a ha e) + (3 / 4 : ℂ) *
      inner ℂ (physicalClosedEmbedding a ha (physicalClosedEnergyEquiv a ha d))
        (physicalClosedEmbedding a ha (physicalClosedEnergyEquiv a ha e)) =
      inner ℂ d e := by
  rw [physicalClosedForm_equiv, physicalClosedEmbedding_equiv,
    physicalClosedEmbedding_equiv, (weightedHeightUnitary a ha).symm.inner_map_map]
  exact radialQuarterForm_shift_threeQuarters d e

def physicalWeakGraph (a : ℝ) (ha : 0 < a) :
    Submodule ℂ (PhysicalHeightL2 × PhysicalHeightL2) where
  carrier := {p | ∃ e : physicalClosedEnergyDomain a ha,
    physicalClosedEmbedding a ha e = p.1 ∧
      ∀ d : physicalClosedEnergyDomain a ha,
        physicalClosedForm a ha d e = inner ℂ (physicalClosedEmbedding a ha d) p.2}
  zero_mem' := by refine ⟨0, by simp, ?_⟩; intro d; simp [physicalClosedForm]
  add_mem' := by
    rintro ⟨u, v⟩ ⟨u', v'⟩ ⟨e, he, hw⟩ ⟨e', he', hw'⟩
    refine ⟨e + e', by simpa [he, he'], fun d => ?_⟩
    change physicalClosedForm a ha d (e + e') = _
    simp only [physicalClosedForm, map_add, inner_add_right] at *
    linear_combination hw d + hw' d
  smul_mem' := by
    rintro c ⟨u, v⟩ ⟨e, he, hw⟩
    refine ⟨c • e, by simpa [he], fun d => ?_⟩
    change physicalClosedForm a ha d (c • e) = _
    simp only [physicalClosedForm, map_smul, inner_smul_right] at *
    linear_combination c * hw d

/-- The actual physical weak graph is derived from closed form testing.
The quarter and the specific actual radial graph are conclusions. -/
theorem physicalWeakGraph_iff_radial (a : ℝ) (ha : 0 < a) (u v : PhysicalHeightL2) :
    (u, v) ∈ physicalWeakGraph a ha ↔
      (weightedHeightUnitary a ha u,
        weightedHeightUnitary a ha v - (1 / 4 : ℂ) • weightedHeightUnitary a ha u) ∈
          actualRadialFriedrichs.graph := by
  rw [actualRadialFriedrichs_quarter_graph_iff]
  constructor
  · rintro ⟨e, he, hw⟩
    obtain ⟨eR, rfl⟩ := (physicalClosedEnergyEquiv a ha).surjective e
    have heR : radialPhysicalEmbedding 1 eR = weightedHeightUnitary a ha u := by
      rw [physicalClosedEmbedding_equiv] at he
      simpa using congrArg (weightedHeightUnitary a ha) he
    refine ⟨eR, heR, fun d => ?_⟩
    have h := hw (physicalClosedEnergyEquiv a ha d)
    rw [physicalClosedForm_equiv, physicalClosedEmbedding_equiv] at h
    rw [← (weightedHeightUnitary a ha).inner_map_map
      ((weightedHeightUnitary a ha).symm (radialPhysicalEmbedding 1 d)) v] at h
    simpa using h
  · rintro ⟨eR, heR, hw⟩
    refine ⟨physicalClosedEnergyEquiv a ha eR, ?_, ?_⟩
    · rw [physicalClosedEmbedding_equiv, heR]
      simp
    · intro d
      obtain ⟨dR, rfl⟩ := (physicalClosedEnergyEquiv a ha).surjective d
      rw [physicalClosedForm_equiv, physicalClosedEmbedding_equiv, hw dR,
        ← (weightedHeightUnitary a ha).inner_map_map
          ((weightedHeightUnitary a ha).symm (radialPhysicalEmbedding 1 dR)) v]
      simp

theorem physicalWeakGraph_zero_fiber (a : ℝ) (ha : 0 < a)
    (p : PhysicalHeightL2 × PhysicalHeightL2) (hp : p ∈ physicalWeakGraph a ha)
    (hz : p.1 = 0) : p.2 = 0 := by
  have h := (physicalWeakGraph_iff_radial a ha p.1 p.2).mp hp
  simp only [hz, map_zero, smul_zero, sub_zero] at h
  have hv := LinearPMap.mem_graph_snd_inj actualRadialFriedrichs h
    actualRadialFriedrichs.graph.zero_mem rfl
  apply (weightedHeightUnitary a ha).injective
  simpa using hv

/-- Native partial linear operator associated with the actual closed
physical energy form. Its definition contains no radial graph. -/
def actualModeFriedrichs (a : ℝ) (ha : 0 < a) :
    PhysicalHeightL2 →ₗ.[ℂ] PhysicalHeightL2 := (physicalWeakGraph a ha).toLinearPMap

theorem actualModeFriedrichs_graph (a : ℝ) (ha : 0 < a) :
    (actualModeFriedrichs a ha).graph = physicalWeakGraph a ha :=
  Submodule.toLinearPMap_graph_eq _ (physicalWeakGraph_zero_fiber a ha)

theorem actualModeFriedrichs_graph_conjugacy (a : ℝ) (ha : 0 < a)
    (u v : PhysicalHeightL2) :
    (u, v) ∈ (actualModeFriedrichs a ha).graph ↔
      (weightedHeightUnitary a ha u,
        weightedHeightUnitary a ha v - (1 / 4 : ℂ) • weightedHeightUnitary a ha u) ∈
          actualRadialFriedrichs.graph := by
  rw [actualModeFriedrichs_graph]
  exact physicalWeakGraph_iff_radial a ha u v

theorem actualModeFriedrichs_domain_iff (a : ℝ) (ha : 0 < a) (u : PhysicalHeightL2) :
    u ∈ (actualModeFriedrichs a ha).domain ↔
      weightedHeightUnitary a ha u ∈ actualRadialFriedrichs.domain := by
  rw [LinearPMap.mem_domain_iff, LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨_, (actualModeFriedrichs_graph_conjugacy a ha u v).mp hv⟩
  · rintro ⟨w, hw⟩
    refine ⟨(weightedHeightUnitary a ha).symm
      (w + (1 / 4 : ℂ) • weightedHeightUnitary a ha u), ?_⟩
    apply (actualModeFriedrichs_graph_conjugacy a ha _ _).mpr
    simpa using hw

theorem actualModeFriedrichs_dense_domain (a : ℝ) (ha : 0 < a) :
    Dense ((actualModeFriedrichs a ha).domain : Set PhysicalHeightL2) := by
  have hd := (weightedHeightUnitary a ha).symm.surjective.denseRange.dense_image
    (weightedHeightUnitary a ha).symm.continuous actualRadialFriedrichs_dense_domain
  apply hd.mono
  rintro u ⟨v, hv, rfl⟩
  apply (actualModeFriedrichs_domain_iff a ha _).mpr
  simpa using hv

theorem actualModeFriedrichs_isClosed (a : ℝ) (ha : 0 < a) :
    (actualModeFriedrichs a ha).IsClosed := by
  have hc : Continuous (fun p : PhysicalHeightL2 × PhysicalHeightL2 =>
      (weightedHeightUnitary a ha p.1,
        weightedHeightUnitary a ha p.2 - (1 / 4 : ℂ) • weightedHeightUnitary a ha p.1)) := by
    fun_prop
  have hclosed := actualRadialFriedrichs_isClosed.preimage hc
  change IsClosed ((actualModeFriedrichs a ha).graph : Set _)
  convert hclosed using 1
  ext p
  exact actualModeFriedrichs_graph_conjugacy a ha p.1 p.2

private theorem physical_adjoint_graph_iff (a : ℝ) (ha : 0 < a)
    (u v : PhysicalHeightL2) :
    (u, v) ∈ (actualModeFriedrichs a ha).graph.adjoint ↔
      (weightedHeightUnitary a ha u,
        weightedHeightUnitary a ha v - (1 / 4 : ℂ) • weightedHeightUnitary a ha u) ∈
          actualRadialFriedrichs.graph.adjoint := by
  rw [Submodule.mem_adjoint_iff, Submodule.mem_adjoint_iff]
  constructor
  · intro h x y hxy
    have hp : ((weightedHeightUnitary a ha).symm x,
        (weightedHeightUnitary a ha).symm (y + (1 / 4 : ℂ) • x)) ∈
          (actualModeFriedrichs a ha).graph := by
      apply (actualModeFriedrichs_graph_conjugacy a ha _ _).mpr
      simpa using hxy
    have hh := h _ _ hp
    rw [← (weightedHeightUnitary a ha).inner_map_map
      ((weightedHeightUnitary a ha).symm (y + (1 / 4 : ℂ) • x)) u,
      ← (weightedHeightUnitary a ha).inner_map_map
        ((weightedHeightUnitary a ha).symm x) v] at hh
    simp only [LinearIsometryEquiv.apply_symm_apply, inner_add_left,
      inner_smul_left] at hh
    change inner ℂ y (weightedHeightUnitary a ha u) -
      inner ℂ x (weightedHeightUnitary a ha v -
        (1 / 4 : ℂ) • weightedHeightUnitary a ha u) = 0
    rw [inner_sub_right, inner_smul_right]
    norm_num at hh
    linear_combination hh
  · intro h x y hxy
    have hh := h _ _ ((actualModeFriedrichs_graph_conjugacy a ha x y).mp hxy)
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right] at hh
    rw [← (weightedHeightUnitary a ha).inner_map_map y u,
      ← (weightedHeightUnitary a ha).inner_map_map x v]
    norm_num at hh
    linear_combination hh

/-- Actual native self-adjointness, following from the proved weak-graph
identification and its adjoint transformation. -/
theorem actualModeFriedrichs_isSelfAdjoint (a : ℝ) (ha : 0 < a) :
    IsSelfAdjoint (actualModeFriedrichs a ha) := by
  have hrad : actualRadialFriedrichs.graph.adjoint = actualRadialFriedrichs.graph := by
    rw [← LinearPMap.adjoint_graph_eq_graph_adjoint actualRadialFriedrichs_dense_domain]
    exact congrArg LinearPMap.graph
      (LinearPMap.isSelfAdjoint_def.mp actualRadialFriedrichs_isSelfAdjoint)
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (actualModeFriedrichs_dense_domain a ha)]
  apply SetLike.ext
  rintro ⟨u, v⟩
  rw [physical_adjoint_graph_iff, hrad, actualModeFriedrichs_graph_conjugacy]

theorem actualModeFriedrichs_nonneg (a : ℝ) (ha : 0 < a)
    (u : (actualModeFriedrichs a ha).domain) :
    0 ≤ (inner ℂ (u : PhysicalHeightL2) (actualModeFriedrichs a ha u)).re := by
  have hg := LinearPMap.mem_graph (actualModeFriedrichs a ha) u
  rw [actualModeFriedrichs_graph] at hg
  obtain ⟨e, he, hw⟩ := hg
  have h := hw e
  rw [he] at h
  rw [← h]
  simp only [physicalClosedForm, inner_self_eq_norm_sq_to_K, map_add,
    Complex.ofReal_re]
  positivity

def radialCoreEnergyPoint (T : RadialTest) : radialClosedEnergyDomain 1 :=
  ⟨radialEnergyCoreVector 1 T, (radialEnergyCoreSpan 1).le_topologicalClosure
    (Submodule.subset_span ⟨T, rfl⟩)⟩

def physicalCoreEnergyPoint (a : ℝ) (ha : 0 < a) (T : RadialTest) :
    physicalClosedEnergyDomain a ha := physicalClosedEnergyEquiv a ha (radialCoreEnergyPoint T)

theorem inverse_unitary_core_eq (a : ℝ) (ha : 0 < a) (T : RadialTest) :
    (weightedHeightUnitary a ha).symm (radialCoreL2 T) = physicalCoreL2 a ha T := by
  apply Lp.ext
  exact (weightedHeightUnitary_inverse_on_core_ae a ha T).trans
    (physicalLift_memLp ha T).coeFn_toLp.symm

theorem physicalClosedEmbedding_on_core (a : ℝ) (ha : 0 < a) (T : RadialTest) :
    physicalClosedEmbedding a ha (physicalCoreEnergyPoint a ha T) = physicalCoreL2 a ha T := by
  rw [physicalCoreEnergyPoint, physicalClosedEmbedding_equiv]
  have hc : radialPhysicalEmbedding 1 (radialCoreEnergyPoint T) = radialCoreL2 T :=
    energyPhysical_core 1 (by norm_num) T
  rw [hc, inverse_unitary_core_eq]

/-- The compact physical cores are dense in the actual height L2 space. -/
theorem physicalCoreL2_dense (a : ℝ) (ha : 0 < a) :
    Dense (range (physicalCoreL2 a ha)) := by
  have hd := (weightedHeightUnitary a ha).symm.surjective.denseRange.dense_image
    (weightedHeightUnitary a ha).symm.continuous radialCoreL2_range_dense
  apply hd.mono
  rintro f ⟨g, ⟨T, rfl⟩, rfl⟩
  exact ⟨T, (inverse_unitary_core_eq a ha T).symm⟩

/-- The middle closed-form coordinate has the actual physical vertical
derivative representative y*f'(y) on every compact test. -/
theorem physicalClosedVertical_on_core_ae (a : ℝ) (ha : 0 < a) (T : RadialTest) :
    physicalClosedVertical a ha (physicalCoreEnergyPoint a ha T) =ᵐ[heightMeasure]
      (fun y : PositiveHeight => (y : ℂ) * deriv (physicalLift a T.function) y) := by
  have hrep : (radialDerivativeL2 T + (1 / 2 : ℂ) • radialCoreL2 T : RadialL2) =ᵐ[volume]
      (fun r : ℝ => deriv T.function r + (1 / 2 : ℂ) * T.function r) := by
    filter_upwards [Lp.coeFn_add (radialDerivativeL2 T) ((1 / 2 : ℂ) • radialCoreL2 T),
      Lp.coeFn_smul (1 / 2 : ℂ) (radialCoreL2 T),
      T.derivative_memLp.coeFn_toLp, T.function_memLp.coeFn_toLp] with r hadd hsmul hd hf
    simp only [hadd, hsmul, Pi.smul_apply, smul_eq_mul]
    rw [hd, hf]
  have hrepY := (scaledHeightEquiv_symm_quasiMeasurePreserving a ha).ae hrep
  rw [physicalCoreEnergyPoint, physicalClosedVertical_equiv]
  have hc : radialHalfShiftedDerivative (radialCoreEnergyPoint T) =
      radialDerivativeL2 T + (1 / 2 : ℂ) • radialCoreL2 T := by
    simp [radialHalfShiftedDerivative, radialCoreEnergyPoint, radialClosedDerivative,
      radialPhysicalEmbedding, energyDerivativeCoordinate, energyPhysicalCoordinate,
      radialEnergyCoreVector]
  rw [hc]
  filter_upwards [weightedHeightUnitary_inverse_ae a ha
    (radialDerivativeL2 T + (1 / 2 : ℂ) • radialCoreL2 T), hrepY] with y hv hr
  rw [hv, hr]
  have hd := physicalLift_hasDerivAt ha y.property T.function
    (T.smooth.differentiable (by simp) _)
  rw [hd.deriv]
  have hs : (Real.sqrt (y : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 y.property).ne'
  have hsq : (Real.sqrt (y : ℝ) : ℂ) ^ 2 = (y : ℂ) := by
    exact_mod_cast Real.sq_sqrt y.property.le
  rw [← hsq]
  field_simp [hs] <;> ring

/-- The last coordinate is the literal physical potential multiplier a*y. -/
theorem physicalClosedPotential_on_core_ae (a : ℝ) (ha : 0 < a) (T : RadialTest) :
    physicalClosedPotential a ha (physicalCoreEnergyPoint a ha T) =ᵐ[heightMeasure]
      (fun y : PositiveHeight => (a : ℂ) * (y : ℂ) * physicalLift a T.function y) := by
  have hrep := (scaledHeightEquiv_symm_quasiMeasurePreserving a ha).ae
    T.exponential_memLp.coeFn_toLp
  rw [physicalCoreEnergyPoint, physicalClosedPotential_equiv]
  change (weightedHeightUnitary a ha).symm (radialExponentialL2 T) =ᵐ[heightMeasure] _
  filter_upwards [weightedHeightUnitary_inverse_ae a ha (radialExponentialL2 T), hrep]
    with y hv hr
  rw [hv, hr]
  simp only [exponentialProduct, physicalLift, Real.exp_log (mul_pos ha y.property),
    Complex.ofReal_mul]
  ring

/-- The closed form restricts to the literal physical dy Dirichlet form,
with the signed horizontal Fourier eigenvalue (2*pi*n)^2. -/
theorem physicalClosedForm_on_actual_mode_core {n : ℤ} (hn : n ≠ 0)
    (T U : RadialTest) :
    physicalClosedForm (CuspCylinderBesselMode20261024z.frequencyScale n)
      (CuspCylinderBesselMode20261024z.frequencyScale_pos hn)
      (physicalCoreEnergyPoint _ _ T) (physicalCoreEnergyPoint _ _ U) =
        physicalCoreEnergy n T U := by
  rw [physicalCoreEnergyPoint, physicalCoreEnergyPoint, physicalClosedForm_equiv,
    radialQuarterForm_eq, physicalCoreEnergy_eq_radial_add_quarter hn]
  simp [radialCoreEnergyPoint, radialPhysicalEmbedding, radialClosedDerivative,
    radialClosedExponential, energyPhysicalCoordinate, energyDerivativeCoordinate,
    energyExponentialCoordinate, radialEnergyCoreVector]

/-- Frequency specialization for the original signed nonzero Fourier mode.
The horizontal character remains n; only its positive radial scale uses |n|. -/
def actualNonzeroModeFriedrichs (n : ℤ) (hn : n ≠ 0) :
    PhysicalHeightL2 →ₗ.[ℂ] PhysicalHeightL2 :=
  actualModeFriedrichs (CuspCylinderBesselMode20261024z.frequencyScale n)
    (CuspCylinderBesselMode20261024z.frequencyScale_pos hn)

theorem actualNonzeroModeFriedrichs_graph_conjugacy (n : ℤ) (hn : n ≠ 0)
    (u v : PhysicalHeightL2) :
    let U := weightedHeightUnitary (CuspCylinderBesselMode20261024z.frequencyScale n)
      (CuspCylinderBesselMode20261024z.frequencyScale_pos hn)
    (u, v) ∈ (actualNonzeroModeFriedrichs n hn).graph ↔
      (U u, U v - (1 / 4 : ℂ) • U u) ∈ actualRadialFriedrichs.graph :=
  actualModeFriedrichs_graph_conjugacy _ _ u v

end
end ImbalancedChen.Part3.CuspModeNativeClosedForm20261026a
