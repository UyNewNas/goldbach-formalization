import ImbalancedChen.Part5OriginalBuchstabTrueAtomLimits
import ImbalancedChen.Part5OriginalH430NativeBuchstabMeasure

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The new prime-sum integral is identified with the existing native dx
coefficient through an actual reciprocal change of variables. The parent
physical weight and the arithmetic Theta are kept as different objects.
No cancellation or division by either parent mass is used.
-/
namespace ImbalancedChen.Part5OriginalBuchstabNativeAtomDictionary

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
open Part5OriginalUpsilon5CausalDictionary
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels Part5UpperTables
open Part5OriginalBuchstabCompactAtoms Part5OriginalBuchstabTrueAtomLimits
open Part5OriginalH430MovingBuchstabAtoms
open Part5OriginalH430BuchstabPhysicalBudget Part5OriginalH430NativeBuchstabMeasure
open Part5OriginalH430PhysicalMassPerturbation
open P2EnhancedLowerPhysicalNode


def scalarDomain (up : Bool) (b : FloorAtom) (c : ℝ) : Set ℝ :=
  {u | (fun _ : Fin 1 => u) ∈ atomDomain up b c}
def scalarKernel (u : ℝ) : ℝ := residualSingle (fun _ : Fin 1 => u) * (1/u)
def reciprocalMap (w : ℝ) : ℝ := 1/(w+1)

theorem measurable_scalarDomain (up : Bool) (b : FloorAtom) (c : ℝ) :
    MeasurableSet (scalarDomain up b c) := by
  change MeasurableSet (Icc (1/6:ℝ) (reciprocalTop c) ∩
    (fun u : ℝ => 1/u-1) ⁻¹' tableAtomSet up b)
  exact measurableSet_Icc.inter ((measurableSet_tableAtomSet up b).preimage
    ((measurable_const.div measurable_id).sub measurable_const))

theorem measurable_atomDomain (up : Bool) (b : FloorAtom) (c : ℝ) :
    MeasurableSet (atomDomain up b c) := by
  have he : atomDomain up b c = (fun x : Coord 1 => x 0) ⁻¹' scalarDomain up b c := by
    ext x
    have hx : (fun _ : Fin 1 => x 0) = x := by funext i; fin_cases i; rfl
    simp only [scalarDomain,mem_preimage,mem_setOf_eq,hx]
  rw [he]
  exact (measurable_scalarDomain up b c).preimage (measurable_pi_apply 0)

/-- Pi1 volume is converted to the original one-dimensional Lebesgue
measure, before the reciprocal substitution is performed. -/
theorem normalizedAtomIntegral_eq_scalar (up : Bool) (b : FloorAtom) (c : ℝ) :
    normalizedAtomIntegral up b c = ∫ u in scalarDomain up b c, scalarKernel u := by
  have h := (volume_preserving_funUnique (Fin 1) ℝ).integral_comp'
    ((scalarDomain up b c).indicator scalarKernel)
  change (∫ x : Coord 1, (scalarDomain up b c).indicator scalarKernel (x 0)) =
    ∫ u : ℝ, (scalarDomain up b c).indicator scalarKernel u at h
  have hind : (fun x : Coord 1 => (scalarDomain up b c).indicator scalarKernel (x 0)) =
      (atomDomain up b c).indicator (fun x => residualSingle x * ∏ i, 1/x i) := by
    funext x
    have hx : (fun _ : Fin 1 => x 0) = x := by funext i; fin_cases i; rfl
    have hmem : x 0 ∈ scalarDomain up b c ↔ x ∈ atomDomain up b c := by
      simp only [scalarDomain,mem_setOf_eq,hx]
    by_cases hm : x ∈ atomDomain up b c
    · simp only [indicator_of_mem hm,indicator_of_mem (hmem.mpr hm),
        scalarKernel,hx,Fin.prod_univ_one]
    · simp only [indicator_of_notMem hm,indicator_of_notMem (mt hmem.mp hm)]
  rw [hind,integral_indicator (measurable_atomDomain up b c),
    integral_indicator (measurable_scalarDomain up b c)] at h
  exact h

theorem reciprocal_query {w : ℝ} (hw : 1 ≤ w) :
    query (fun _ : Fin 1 => reciprocalMap w) = w := by
  have hw1 : w+1 ≠ 0 := by linarith
  simp only [query,reciprocalMap]
  field_simp [hw1] <;> ring

theorem scalarDomain_eq_image {up : Bool} {b : FloorAtom} {c : ℝ} (hc : 1 ≤ c) :
    scalarDomain up b c = reciprocalMap '' (Icc c 5 ∩ tableAtomSet up b) := by
  ext u
  change ((fun _ : Fin 1 => u) ∈ atomDomain up b c) ↔ _
  rw [atomDomain_query hc]
  constructor
  · rintro ⟨hu,hw,hb⟩
    refine ⟨query (fun _ : Fin 1 => u),⟨hw,hb⟩,?_⟩
    simp only [reciprocalMap,query]
    field_simp [hu.ne'] <;> ring
  · rintro ⟨w,hw,rfl⟩
    have hw1 : 1 ≤ w := hc.trans hw.1.1
    refine ⟨one_div_pos.mpr (by linarith),?_,?_⟩
    · simpa only [reciprocal_query hw1] using hw.1
    · simpa only [reciprocal_query hw1] using hw.2

theorem reciprocalMap_hasDerivAt {w : ℝ} (hw : 1 ≤ w) :
    HasDerivAt reciprocalMap (-(1/(w+1)^2)) w := by
  have h := (hasDerivAt_const w (1:ℝ)).div
    ((hasDerivAt_id w).add_const 1) (by linarith : w+1 ≠ 0)
  convert h using 1 <;> simp [reciprocalMap] <;> ring

theorem reciprocalMap_injOn : InjOn reciprocalMap buchstabAmbient := by
  intro w hw v hv he
  have hw1 : w+1 ≠ 0 := by linarith [hw.1]
  have hv1 : v+1 ≠ 0 := by linarith [hv.1]
  have hh := (div_eq_div_iff hw1 hv1).mp he
  linarith

theorem reciprocal_kernel {w : ℝ} (hw : w ∈ buchstabAmbient) :
    |-(1/(w+1)^2)| * scalarKernel (reciprocalMap w) = buchstabKernel w := by
  have hw0 : 0 < w := zero_lt_one.trans_le hw.1
  have hw1 : 0 < w+1 := by linarith
  have hu : 1/(w+1) ≤ (1/2:ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [hw.1])
  have hd : (1/10:ℝ) ≤ 1-1/(w+1) := by linarith
  have hn : 1-1/(w+1) ≠ 0 := by linarith
  rw [abs_neg,abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(w+1)^2),
    buchstabKernel_eq_raw hw]
  simp only [scalarKernel,reciprocalMap,residualSingle,max_eq_right hd]
  field_simp [hw0.ne',hw1.ne',hn] <;> ring

/-- Literal normalized integral, including closed knots, equals the
original dw/w atom. Nullity is used only inside this integral identity. -/
theorem normalizedAtomIntegral_eq_atomMass {up : Bool} {b : FloorAtom} {c : ℝ}
    (hc : 1 ≤ c) : normalizedAtomIntegral up b c = atomMass up b c := by
  let S := Icc c 5 ∩ tableAtomSet up b
  have hS : MeasurableSet S := measurableSet_Icc.inter (measurableSet_tableAtomSet up b)
  have hsub : S ⊆ buchstabAmbient := fun w hw => ⟨hc.trans hw.1.1,hw.1.2⟩
  have hchange := integral_image_eq_integral_abs_deriv_smul hS
    (fun w hw => (reciprocalMap_hasDerivAt (hsub hw).1).hasDerivWithinAt)
    (reciprocalMap_injOn.mono hsub) scalarKernel
  rw [normalizedAtomIntegral_eq_scalar,scalarDomain_eq_image hc]
  calc
    _ = ∫ w in S, |-(1/(w+1)^2)| • scalarKernel (reciprocalMap w) := hchange
    _ = ∫ w in S, buchstabKernel w := by
      apply setIntegral_congr_fun hS
      intro w hw
      simpa only [smul_eq_mul] using reciprocal_kernel (hsub hw)
    _ = atomMass up b c := by
      simp only [atomMass,startAtomDensity,integral_indicator hS,S]

/-- The continuous physical parent weight is NOT the arithmetic Theta.
This identity says exactly how the same normalized atom occurs in each. -/
theorem nativeAtomCoefficient_eq_normalized {up : Bool} {p : PhysicalNode}
    (hL : 0 < P2EnhancedLowerPhysicalNode.residual p) (hC : 0 < p.ceiling)
    (hg : directionGuard up p) (b : FloorAtom) :
    nativeAtomCoefficient up p b = physicalWeight p *
      normalizedAtomIntegral up b (physicalStart up p) := by
  rw [nativeAtomCoefficient_eq hL hC hg,
    normalizedAtomIntegral_eq_atomMass (physicalStart_ge_one hg)]
  rfl

end
end ImbalancedChen.Part5OriginalBuchstabNativeAtomDictionary
