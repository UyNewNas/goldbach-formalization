import ImbalancedChen.Part3ActualPrimeHeckePhysicalFourier
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The ORIGINAL physical prime Hecke trace preserves the original classical
Maass PDE, C2 regularity, and actual quotient periodicity. Both second
coordinate derivatives are derived by real affine chain rules. The height
factor (a*y)^2 exactly cancels the a^2 derivative scale. Finite summation
and original p^-1/2 normalization are paid by native Frechet derivatives.
No transformed PDE, Hecke eigenfunction, operator-domain commutation,
weak regularity or spectral completeness premise is assumed.
-/

namespace ImbalancedChen.Part3.ActualClassicalHeckeMaass20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators UpperHalfPlane
open ActualMaassFourierODE20261026a ActualPrimeHeckeBranchSeparation20261026b
open ActualHeckeDivisibleFourier20261026b ActualHeckeTranslationProjector20261026b
open ActualPrimeHeckeQuotientDescent20261026b ActualPrimeHeckePhysicalFourier20261026b
open QuotientRealKFourierCoefficient20261026b ActualCommonIntervalCompletionL1SourceOnly
open Gamma0QuotientCellPushforward20261025a

abbrev Plane := ℝ × ℝ

def direction (v : Plane) (u : Plane → ℂ) (z : Plane) : ℂ := fderiv ℝ u z v

def affineBranch (a b : ℝ) (z : Plane) : Plane := a • z + (b,0)

theorem affineBranch_hasFDerivAt (a b : ℝ) (z : Plane) :
    HasFDerivAt (affineBranch a b) (a • ContinuousLinearMap.id ℝ Plane) z :=
  ((hasFDerivAt_id z).const_smul a).add_const (b,0)

theorem affineBranch_mapsTo {a : ℝ} (ha : 0 < a) (b : ℝ) :
    MapsTo (affineBranch a b) upperDomain upperDomain := by
  intro z hz
  simpa [affineBranch,upperDomain] using mul_pos ha hz

private theorem differentiableAt_of_C1 {u : Plane → ℂ}
    (hu : ContDiffOn ℝ 1 u upperDomain) {z : Plane} (hz : z ∈ upperDomain) :
    DifferentiableAt ℝ u z :=
  ((hu.differentiableOn (by norm_num)) z hz).differentiableAt (upperDomain_isOpen.mem_nhds hz)

private theorem differentiableAt_of_C2 {u : Plane → ℂ}
    (hu : ContDiffOn ℝ 2 u upperDomain) {z : Plane} (hz : z ∈ upperDomain) :
    DifferentiableAt ℝ u z :=
  ((hu.differentiableOn (by norm_num)) z hz).differentiableAt (upperDomain_isOpen.mem_nhds hz)

theorem direction_contDiffOn (v : Plane) {u : Plane → ℂ}
    (hu : ContDiffOn ℝ 2 u upperDomain) : ContDiffOn ℝ 1 (direction v u) upperDomain :=
  (hu.fderiv_of_isOpen upperDomain_isOpen (by norm_num)).clm_apply contDiffOn_const

theorem direction_congr_on (v : Plane) {u w : Plane → ℂ}
    (heq : ∀ z ∈ upperDomain, u z = w z) {z : Plane} (hz : z ∈ upperDomain) :
    direction v u z = direction v w z := by
  have hloc : u =ᶠ[𝓝 z] w := by
    filter_upwards [upperDomain_isOpen.mem_nhds hz] with q hq
    exact heq q hq
  exact congrArg (fun L : Plane →L[ℝ] ℂ => L v) hloc.fderiv_eq

theorem second_direction_congr_on (v : Plane) {u w : Plane → ℂ}
    (heq : ∀ z ∈ upperDomain, u z = w z) {z : Plane} (hz : z ∈ upperDomain) :
    direction v (direction v u) z = direction v (direction v w) z :=
  direction_congr_on v (fun q hq => direction_congr_on v heq hq) hz

theorem direction_affine (v : Plane) {u : Plane → ℂ}
    (hu : DifferentiableOn ℝ u upperDomain) {a : ℝ} (ha : 0 < a) (b : ℝ)
    {z : Plane} (hz : z ∈ upperDomain) :
    direction v (u ∘ affineBranch a b) z = a • direction v u (affineBranch a b z) := by
  have hAz := affineBranch_mapsTo ha b hz
  have hd := ((hu _ hAz).differentiableAt (upperDomain_isOpen.mem_nhds hAz)).hasFDerivAt.comp z
    (affineBranch_hasFDerivAt a b z)
  change fderiv ℝ (u ∘ affineBranch a b) z v = _
  rw [hd.fderiv]
  simp [direction]

theorem second_direction_affine (v : Plane) {u : Plane → ℂ}
    (hu : ContDiffOn ℝ 2 u upperDomain) {a : ℝ} (ha : 0 < a) (b : ℝ)
    {z : Plane} (hz : z ∈ upperDomain) :
    direction v (direction v (u ∘ affineBranch a b)) z =
      a^2 • direction v (direction v u) (affineBranch a b z) := by
  have hfirst : ∀ q ∈ upperDomain, direction v (u ∘ affineBranch a b) q =
      a • direction v u (affineBranch a b q) :=
    fun q hq => direction_affine v (hu.differentiableOn (by norm_num)) ha b hq
  have hAz := affineBranch_mapsTo ha b hz
  have hdir := direction_contDiffOn v hu
  have hd := (differentiableAt_of_C1 hdir hAz).hasFDerivAt.comp z (affineBranch_hasFDerivAt a b z)
  rw [direction_congr_on v hfirst hz]
  change fderiv ℝ (fun q => a • direction v u (affineBranch a b q)) z v = _
  rw [(hd.const_smul a).fderiv]
  simp [direction,pow_two,smul_smul]

theorem direction_sum {ι : Type*} (s : Finset ι) (v : Plane) (f : ι → Plane → ℂ)
    (hf : ∀ i ∈ s, DifferentiableOn ℝ (f i) upperDomain) {z : Plane} (hz : z ∈ upperDomain) :
    direction v (fun q => ∑ i ∈ s, f i q) z = ∑ i ∈ s, direction v (f i) z := by
  change fderiv ℝ (fun q => ∑ i ∈ s, f i q) z v = _
  rw [fderiv_fun_sum (fun i hi => ((hf i hi) z hz).differentiableAt (upperDomain_isOpen.mem_nhds hz))]
  simp [direction]

theorem second_direction_sum {ι : Type*} (s : Finset ι) (v : Plane) (f : ι → Plane → ℂ)
    (hf : ∀ i ∈ s, ContDiffOn ℝ 2 (f i) upperDomain) {z : Plane} (hz : z ∈ upperDomain) :
    direction v (direction v (fun q => ∑ i ∈ s, f i q)) z =
      ∑ i ∈ s, direction v (direction v (f i)) z := by
  rw [direction_congr_on v (fun q hq => direction_sum s v f
    (fun i hi => (hf i hi).differentiableOn (by norm_num)) hq) hz]
  exact direction_sum s v (fun i => direction v (f i))
    (fun i hi => (direction_contDiffOn v (hf i hi)).differentiableOn (by norm_num)) hz

theorem direction_smul (c : ℂ) (v : Plane) {u : Plane → ℂ}
    (hu : DifferentiableOn ℝ u upperDomain) {z : Plane} (hz : z ∈ upperDomain) :
    direction v (fun q => c • u q) z = c • direction v u z := by
  change fderiv ℝ (fun q => c • u q) z v = _
  rw [fderiv_fun_const_smul ((hu z hz).differentiableAt (upperDomain_isOpen.mem_nhds hz)) c]
  rfl

theorem second_direction_smul (c : ℂ) (v : Plane) {u : Plane → ℂ}
    (hu : ContDiffOn ℝ 2 u upperDomain) {z : Plane} (hz : z ∈ upperDomain) :
    direction v (direction v (fun q => c • u q)) z = c • direction v (direction v u) z := by
  rw [direction_congr_on v (fun q hq => direction_smul c v
    (hu.differentiableOn (by norm_num)) hq) hz]
  exact direction_smul c v ((direction_contDiffOn v hu).differentiableOn (by norm_num)) hz

/-- Original negative hyperbolic Laplace equation, with literal native
coordinate derivatives and no supplied transformed solution. -/
structure ClassicalMaass (lambda : ℂ) (u : Plane → ℂ) : Prop where
  regular : ContDiffOn ℝ 2 u upperDomain
  equation : ∀ z ∈ upperDomain,
    -(z.2 : ℂ)^2 * (direction (1,0) (direction (1,0) u) z +
      direction (0,1) (direction (0,1) u) z) = lambda*u z

theorem ClassicalMaass.affine {lambda : ℂ} {u : Plane → ℂ} (hu : ClassicalMaass lambda u)
    {a : ℝ} (ha : 0 < a) (b : ℝ) : ClassicalMaass lambda (u ∘ affineBranch a b) := by
  refine ⟨hu.regular.comp (by unfold affineBranch; fun_prop) (affineBranch_mapsTo ha b),?_⟩
  intro z hz
  rw [second_direction_affine (1,0) hu.regular ha b hz,
    second_direction_affine (0,1) hu.regular ha b hz]
  have h := hu.equation (affineBranch a b z) (affineBranch_mapsTo ha b hz)
  have hheight : (affineBranch a b z).2 = a*z.2 := by
    change a*z.2+0=a*z.2
    ring
  rw [hheight,Complex.ofReal_mul,mul_pow] at h
  convert h using 1 <;>
    simp only [Function.comp_apply,Complex.real_smul,Complex.ofReal_pow] <;> ring

theorem ClassicalMaass.sum {ι : Type*} (s : Finset ι) (lambda : ℂ) (f : ι → Plane → ℂ)
    (hf : ∀ i ∈ s, ClassicalMaass lambda (f i)) :
    ClassicalMaass lambda (fun z => ∑ i ∈ s, f i z) := by
  refine ⟨ContDiffOn.sum (fun i hi => (hf i hi).regular),?_⟩
  intro z hz
  rw [second_direction_sum s (1,0) f (fun i hi => (hf i hi).regular) hz,
    second_direction_sum s (0,1) f (fun i hi => (hf i hi).regular) hz,
    ← Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i hi => (hf i hi).equation z hz)

theorem ClassicalMaass.smul {lambda : ℂ} {u : Plane → ℂ} (hu : ClassicalMaass lambda u)
    (c : ℂ) : ClassicalMaass lambda (fun z => c • u z) := by
  refine ⟨hu.regular.const_smul c,?_⟩
  intro z hz
  rw [second_direction_smul c (1,0) hu.regular hz,
    second_direction_smul c (0,1) hu.regular hz]
  convert congrArg (fun w : ℂ => c*w) (hu.equation z hz) using 1 <;>
    simp only [smul_eq_mul] <;> ring

theorem ClassicalMaass.congr_on {lambda : ℂ} {u w : Plane → ℂ} (hu : ClassicalMaass lambda u)
    (heq : ∀ z ∈ upperDomain, w z = u z) : ClassicalMaass lambda w := by
  refine ⟨hu.regular.congr heq,?_⟩
  intro z hz
  rw [second_direction_congr_on (1,0) heq hz,second_direction_congr_on (0,1) heq hz,heq z hz]
  exact hu.equation z hz

def classicalBranchScale (p : ℕ) : Branch p → ℝ
  | none => p
  | some _ => (p : ℝ)⁻¹

def classicalBranchShift (p : ℕ) : Branch p → ℝ
  | none => 0
  | some b => (b.val : ℝ)/(p : ℝ)

def classicalHecke (p : ℕ) [NeZero p] (u : Plane → ℂ) : Plane → ℂ :=
  fun z => (Real.sqrt (p : ℝ) : ℂ)⁻¹ • ∑ j : Branch p,
    u (affineBranch (classicalBranchScale p j) (classicalBranchShift p j) z)

theorem classicalHecke_eq_physical (p : ℕ) [NeZero p] (u : Plane → ℂ) :
    classicalHecke p u = primeHeckeExpression p u := by
  funext z
  have hnone : affineBranch (classicalBranchScale p none) (classicalBranchShift p none) z =
      ((p : ℝ)*z.1,(p : ℝ)*z.2) := by simp [affineBranch,classicalBranchScale,classicalBranchShift]
  have hsome (b : ZMod p) : affineBranch (classicalBranchScale p (some b))
      (classicalBranchShift p (some b)) z = ((z.1+(b.val : ℝ))/(p : ℝ),z.2/(p : ℝ)) := by
    ext <;> simp [affineBranch,classicalBranchScale,classicalBranchShift,div_eq_mul_inv] <;> ring
  simp only [classicalHecke,Fintype.sum_option,hnone]
  simp_rw [hsome]
  rw [sum_zmod_val_reindex]
  rfl

/-- Direct classical PDE preservation of the original literal physical
trace, including its p^-1/2 normalization. -/
theorem physicalHecke_classicalMaass (p : ℕ) (hp : 0 < p) {lambda : ℂ} {u : Plane → ℂ}
    (hu : ClassicalMaass lambda u) : ClassicalMaass lambda (primeHeckeExpression p u) := by
  letI : NeZero p := ⟨hp.ne'⟩
  rw [← classicalHecke_eq_physical p u]
  apply ClassicalMaass.smul
  apply ClassicalMaass.sum Finset.univ lambda
  intro j hj
  apply hu.affine
  cases j <;> simp only [classicalBranchScale]
  · exact_mod_cast hp
  · exact inv_pos.mpr (by exact_mod_cast hp)

/-- Genuine descended quotient Hecke function: original C2, actual unit
periodicity and the SAME original classical eigenvalue. No native operator
or quadratic-form domain commutation is inferred. -/
theorem actual_quotient_hecke_classicalMaass (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (U : Gamma0OrbitSpace N → ℂ) (lambda : ℂ)
    (hC2 : ContDiffOn ℝ 2 (maassChart N U) upperDomain)
    (hPDE : ∀ z ∈ upperDomain,
      -(z.2 : ℂ)^2*(partialX (partialX (maassChart N U)) z+
        partialY (partialY (maassChart N U)) z)=lambda*maassChart N U z) :
    ContDiffOn ℝ 2 (maassChart N (quotientHecke N p hp hpN U)) upperDomain ∧
    (∀ x y : ℝ, 0 < y → maassChart N (quotientHecke N p hp hpN U) (x+1,y)=
      maassChart N (quotientHecke N p hp hpN U) (x,y)) ∧
    (∀ z ∈ upperDomain,
      -(z.2 : ℂ)^2*(partialX (partialX (maassChart N (quotientHecke N p hp hpN U))) z+
        partialY (partialY (maassChart N (quotientHecke N p hp hpN U))) z)=
          lambda*maassChart N (quotientHecke N p hp hpN U) z) := by
  have hu : ClassicalMaass lambda (maassChart N U) := ⟨hC2,by
    simpa only [direction,partialX,partialY] using hPDE⟩
  have hT := (physicalHecke_classicalMaass p hp.pos hu).congr_on
    (fun z hz => quotientHecke_chart N p hp hpN U z.1 z.2 hz)
  refine ⟨hT.regular,maassChart_periodic N (quotientHecke N p hp hpN U),?_⟩
  simpa only [direction,partialX,partialY] using hT.equation

end
end ImbalancedChen.Part3.ActualClassicalHeckeMaass20261026b


