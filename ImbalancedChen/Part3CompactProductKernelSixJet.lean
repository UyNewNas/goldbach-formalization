import ImbalancedChen.Part3MaassWeakOperatorCore
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

A genuine simultaneous six-jet finite product-kernel approximation.
For a continuous complex weight on an actual compact rectangle, the
Bochner integral of translated product-kernel jets is approximated by ONE
finite complex combination of actual compact C-infinity product tensors.
All partial derivatives of total order at most two use the SAME coefficients.
The finite function is genuinely smooth, has support in one explicit
expanded rectangle, and is an actual finite CompactTensor core function.

The new approximation input is NOT C2 tensor density: it is continuity of
the weight and a compact smooth product kernel. Closed-span membership of
the actual six-jet integral is proved from convexity of a closed submodule.
No Gamma core membership or convergence of mollifiers to an arbitrary C2
function is claimed. Identifying the six integral components with the
partial derivatives of the convolution, and the C2 approximate-identity
limit, remain distinct analytic steps.
-/

noncomputable section

namespace ImbalancedChen.Part3.CompactProductKernelSixJet20261025a

open Set MeasureTheory Filter
open scoped Topology
open MaassWeakOperatorCore20261024zz CanonicalTensorHyperbolicLaplacianForm20261024z

/-- The actual six pairs (0,0), (1,0), (0,1), (2,0), (1,1), (0,2). -/
abbrev JetIndex := {ij : Fin 3 × Fin 3 // ij.1.val + ij.2.val ≤ 2}

def planeBox (A a b : ℝ) : Set (ℝ × ℝ) := Icc (-A) A ×ˢ Icc a b

instance planeBox_compactSpace (A a b : ℝ) : CompactSpace (planeBox A a b) :=
  isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)

theorem isCompact_planeBox (A a b : ℝ) : IsCompact (planeBox A a b) :=
  isCompact_Icc.prod isCompact_Icc

/-- Compact support and C-infinity regularity are retained before mapping
into the existing C2 CompactTensor core. -/
structure SmoothProduct where
  horizontal : ℝ → ℂ
  vertical : ℝ → ℂ
  horizontal_smooth : ContDiff ℝ ∞ horizontal
  vertical_smooth : ContDiff ℝ ∞ vertical
  horizontal_compact : HasCompactSupport horizontal
  vertical_compact : HasCompactSupport vertical
  vertical_positive : tsupport vertical ⊆ Ioi (0 : ℝ)

def SmoothProduct.toCompactTensor (T : SmoothProduct) : CompactTensor where
  horizontal := T.horizontal
  vertical := T.vertical
  horizontal_smooth := T.horizontal_smooth.of_le (by simp)
  vertical_smooth := T.vertical_smooth.of_le (by simp)
  horizontal_compact := T.horizontal_compact
  vertical_compact := T.vertical_compact
  vertical_positive := T.vertical_positive

/-- Primitive product-kernel data; the radius controls the literal support. -/
structure ProductKernel where
  horizontal : ℝ → ℂ
  vertical : ℝ → ℂ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  horizontal_smooth : ContDiff ℝ ∞ horizontal
  vertical_smooth : ContDiff ℝ ∞ vertical
  horizontal_support : tsupport horizontal ⊆ Icc (-radius) radius
  vertical_support : tsupport vertical ⊆ Icc (-radius) radius

/-- A concrete normalized smooth compact product kernel exists at EVERY
positive radius; the primitive kernel data are genuinely inhabited. -/
def radiusBump (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℝ) where
  rIn := r / 2
  rOut := r
  rIn_pos := half_pos hr
  rIn_lt_rOut := half_lt_self hr

private theorem complex_normedBump_support (r : ℝ) (hr : 0 < r) :
    tsupport (fun x => ((radiusBump r hr).normed volume x : ℂ)) ⊆ Icc (-r) r := by
  intro x hx
  have hs : x ∈ tsupport ((radiusBump r hr).normed volume) :=
    tsupport_comp_subset (g := Complex.ofReal) rfl ((radiusBump r hr).normed volume) hx
  rw [(radiusBump r hr).tsupport_normed_eq] at hs
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hs
  exact hs

def normalizedProductKernel (r : ℝ) (hr : 0 < r) : ProductKernel where
  horizontal x := ((radiusBump r hr).normed volume x : ℂ)
  vertical x := ((radiusBump r hr).normed volume x : ℂ)
  radius := r
  radius_nonneg := hr.le
  horizontal_smooth := Complex.ofRealCLM.contDiff.comp (radiusBump r hr).contDiff_normed
  vertical_smooth := Complex.ofRealCLM.contDiff.comp (radiusBump r hr).contDiff_normed
  horizontal_support := complex_normedBump_support r hr
  vertical_support := complex_normedBump_support r hr
def partialJet (ij : JetIndex) (H : (ℝ × ℝ) → ℂ) (p : ℝ × ℝ) : ℂ :=
  iteratedDeriv ij.1.1.val
    (fun x => iteratedDeriv ij.1.2.val (fun y => H (x, y)) p.2) p.1

/-- This is the literal partial derivative, not a freely supplied jet. -/
theorem partialJet_product (ij : JetIndex) (h v : ℝ → ℂ) (p : ℝ × ℝ) :
    partialJet ij (fun q => h q.1 * v q.2) p =
      iteratedDeriv ij.1.1.val h p.1 * iteratedDeriv ij.1.2.val v p.2 := by
  simp only [partialJet, iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field]

theorem horizontal_shift_support (k : ProductKernel) {A a b : ℝ}
    (t : planeBox A a b) :
    tsupport (fun x => k.horizontal (x - t.1.1)) ⊆
      Icc (-A - k.radius) (A + k.radius) := by
  intro x hx
  have hs := k.horizontal_support
    (tsupport_comp_subset_preimage k.horizontal (continuous_id.sub continuous_const) hx)
  have ht := t.2.1
  constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

theorem vertical_shift_support (k : ProductKernel) {A a b : ℝ}
    (t : planeBox A a b) :
    tsupport (fun y => k.vertical (y - t.1.2)) ⊆
      Icc (a - k.radius) (b + k.radius) := by
  intro y hy
  have hs := k.vertical_support
    (tsupport_comp_subset_preimage k.vertical (continuous_id.sub continuous_const) hy)
  have ht := t.2.2
  constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

/-- Every sampled kernel is an actual compact C-infinity product, with
positive vertical support as soon as its radius is below the height floor. -/
def translatedProduct (k : ProductKernel) {A a b : ℝ} (ha : k.radius < a)
    (t : planeBox A a b) : SmoothProduct where
  horizontal x := k.horizontal (x - t.1.1)
  vertical y := k.vertical (y - t.1.2)
  horizontal_smooth := k.horizontal_smooth.comp (contDiff_id.sub contDiff_const)
  vertical_smooth := k.vertical_smooth.comp (contDiff_id.sub contDiff_const)
  horizontal_compact := isCompact_Icc.of_isClosed_subset
    (isClosed_tsupport _) (horizontal_shift_support k t)
  vertical_compact := isCompact_Icc.of_isClosed_subset
    (isClosed_tsupport _) (vertical_shift_support k t)
  vertical_positive := by
    intro y hy
    have h := (vertical_shift_support k t hy).1
    change 0 < y
    linarith

def scaledProduct (c : ℂ) (T : SmoothProduct) : SmoothProduct where
  horizontal x := c * T.horizontal x
  vertical := T.vertical
  horizontal_smooth := contDiff_const.mul T.horizontal_smooth
  vertical_smooth := T.vertical_smooth
  horizontal_compact := T.horizontal_compact.mul_left
  vertical_compact := T.vertical_compact
  vertical_positive := T.vertical_positive

abbrev SixJet (B d e : ℝ) := C(planeBox B d e, JetIndex → ℂ)

/-- All six literal partial derivatives of one translated product kernel,
restricted to the fixed compact observation rectangle. -/
def kernelJet (k : ProductKernel) (B d e : ℝ) (t : ℝ × ℝ) : SixJet B d e where
  toFun p ij := iteratedDeriv ij.1.1.val k.horizontal (p.1.1 - t.1) *
    iteratedDeriv ij.1.2.val k.vertical (p.1.2 - t.2)
  continuous_toFun := continuous_pi fun ij =>
    ((k.horizontal_smooth.continuous_iteratedDeriv _ (by simp)).comp
      ((continuous_fst.comp continuous_subtype_val).sub continuous_const)).mul
    ((k.vertical_smooth.continuous_iteratedDeriv _ (by simp)).comp
      ((continuous_snd.comp continuous_subtype_val).sub continuous_const))

theorem kernelJet_continuous (k : ProductKernel) (B d e : ℝ) :
    Continuous (kernelJet k B d e) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply continuous_pi
  intro ij
  exact ((k.horizontal_smooth.continuous_iteratedDeriv _ (by simp)).comp
    ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).sub
      (continuous_fst.comp continuous_fst))).mul
    ((k.vertical_smooth.continuous_iteratedDeriv _ (by simp)).comp
    ((continuous_snd.comp (continuous_subtype_val.comp continuous_snd)).sub
      (continuous_snd.comp continuous_fst)))

theorem kernelJet_eq_partialJet (k : ProductKernel) (B d e : ℝ) (t : ℝ × ℝ)
    (p : planeBox B d e) (ij : JetIndex) :
    kernelJet k B d e t p ij =
      partialJet ij (fun q => k.horizontal (q.1 - t.1) * k.vertical (q.2 - t.2)) p.1 := by
  rw [partialJet_product]
  simp only [iteratedDeriv_comp_sub_const, kernelJet]

/-- ONE finite function, whose six genuine derivatives will be approximated. -/
def finiteKernelSum (k : ProductKernel) {A a b : ℝ}
    (c : planeBox A a b →₀ ℂ) (p : ℝ × ℝ) : ℂ :=
  ∑ t ∈ c.support, c t * k.horizontal (p.1 - t.1.1) * k.vertical (p.2 - t.1.2)

theorem finiteKernelSum_smooth (k : ProductKernel) {A a b : ℝ}
    (c : planeBox A a b →₀ ℂ) : ContDiff ℝ ∞ (finiteKernelSum k c) := by
  apply contDiff_sum
  intro t ht
  exact (contDiff_const.mul
    (k.horizontal_smooth.comp (contDiff_fst.sub contDiff_const))).mul
    (k.vertical_smooth.comp (contDiff_snd.sub contDiff_const))

theorem finiteKernelSum_partialJet (k : ProductKernel) {A a b : ℝ}
    (c : planeBox A a b →₀ ℂ) (p : ℝ × ℝ) (ij : JetIndex) :
    partialJet ij (finiteKernelSum k c) p =
      ∑ t ∈ c.support, c t * iteratedDeriv ij.1.1.val k.horizontal (p.1 - t.1.1) *
        iteratedDeriv ij.1.2.val k.vertical (p.2 - t.1.2) := by
  have hinner (x : ℝ) :
      iteratedDeriv ij.1.2.val (fun y => finiteKernelSum k c (x, y)) p.2 =
        ∑ t ∈ c.support, c t * k.horizontal (x - t.1.1) *
          iteratedDeriv ij.1.2.val k.vertical (p.2 - t.1.2) := by
    unfold finiteKernelSum
    rw [iteratedDeriv_fun_sum]
    · apply Finset.sum_congr rfl
      intro t ht
      simp only [iteratedDeriv_const_mul_field, iteratedDeriv_comp_sub_const]
    · intro t ht
      exact ((contDiff_const.mul
        (k.vertical_smooth.comp (contDiff_id.sub contDiff_const))).of_le (by simp)).contDiffAt
  unfold partialJet
  simp_rw [hinner]
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro t ht
    simp only [iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field,
      iteratedDeriv_comp_sub_const]
  · intro t ht
    exact (((contDiff_const.mul
      (k.horizontal_smooth.comp (contDiff_id.sub contDiff_const))).mul
      contDiff_const).of_le (by simp)).contDiffAt

/-- The support is controlled independently of the sampling coefficients. -/
theorem finiteKernelSum_support (k : ProductKernel) {A a b : ℝ}
    (c : planeBox A a b →₀ ℂ) :
    tsupport (finiteKernelSum k c) ⊆
      Icc (-A - k.radius) (A + k.radius) ×ˢ Icc (a - k.radius) (b + k.radius) := by
  apply closure_minimal _ (isClosed_Icc.prod isClosed_Icc)
  intro p hp
  by_contra hout
  have hzero : finiteKernelSum k c p = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    by_cases hh : k.horizontal (p.1 - t.1.1) = 0
    · simp [hh]
    by_cases hv : k.vertical (p.2 - t.1.2) = 0
    · simp [hv]
    have hx := horizontal_shift_support k t (subset_tsupport _ hh)
    have hy := vertical_shift_support k t (subset_tsupport _ hv)
    exact False.elim (hout ⟨hx, hy⟩)
  exact hp hzero

theorem finiteKernelSum_compact (k : ProductKernel) {A a b : ℝ}
    (c : planeBox A a b →₀ ℂ) : HasCompactSupport (finiteKernelSum k c) :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    (isClosed_tsupport _) (finiteKernelSum_support k c)

/-- Literal membership in the existing finite tensor core: the coefficients
are absorbed into the horizontal factors, which remain C-infinity compact. -/
theorem finiteKernelSum_eq_actual_finiteCore (k : ProductKernel) {A a b : ℝ}
    (ha : k.radius < a) (c : planeBox A a b →₀ ℂ) (z : UpperHalfPlane) :
    finiteKernelSum k c (z.re, z.im) = finiteCoreFunction c.support
      (fun t => (scaledProduct (c t) (translatedProduct k ha t)).toCompactTensor) z := by
  simp only [finiteKernelSum, finiteCoreFunction, tensorFunctionH_eq,
    SmoothProduct.toCompactTensor, scaledProduct, translatedProduct]

/-- Actual jet-valued convolution integral over the center rectangle. -/
def integratedKernelJet (k : ProductKernel) (A a b B d e : ℝ)
    (F : (ℝ × ℝ) → ℂ) : SixJet B d e :=
  ∫ t in planeBox A a b, F t • kernelJet k B d e t

theorem weightedKernelJet_integrable (k : ProductKernel) (A a b B d e : ℝ)
    {F : (ℝ × ℝ) → ℂ} (hF : Continuous F) :
    IntegrableOn (fun t => F t • kernelJet k B d e t) (planeBox A a b) :=
  (hF.smul (kernelJet_continuous k B d e)).continuousOn.integrableOn_compact
    (isCompact_planeBox A a b)

/-- No target density hypothesis is used: the actual Bochner integral lies
in the closed span of the actual translated product-kernel jets. -/
theorem integratedKernelJet_mem_closedSpan (k : ProductKernel) (A a b B d e : ℝ)
    {F : (ℝ × ℝ) → ℂ} (hF : Continuous F) :
    integratedKernelJet k A a b B d e F ∈
      (Submodule.span ℂ (Set.range fun t : planeBox A a b =>
        kernelJet k B d e t.1)).topologicalClosure := by
  let μ : Measure (ℝ × ℝ) := volume.restrict (planeBox A a b)
  let V := Submodule.span ℂ (Set.range fun t : planeBox A a b => kernelJet k B d e t.1)
  let W := V.topologicalClosure
  let H : (ℝ × ℝ) → SixJet B d e := fun t => F t • kernelJet k B d e t
  have hInt : Integrable H μ := weightedKernelJet_integrable k A a b B d e hF
  have hmem : ∀ᵐ t ∂μ, H t ∈ W := by
    filter_upwards [ae_restrict_mem (isCompact_planeBox A a b).measurableSet] with t ht
    exact W.smul_mem (F t) (V.le_topologicalClosure (Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩))
  change (∫ t, H t ∂μ) ∈ W
  by_cases hμ : μ = 0
  · simp only [hμ, integral_zero_measure]
    exact W.zero_mem
  letI : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using (isCompact_planeBox A a b).measure_lt_top⟩
  letI : NeZero μ := ⟨hμ⟩
  have havg : (⨍ t, H t ∂μ) ∈ W :=
    (W.restrictScalars ℝ).convex.average_mem V.isClosed_topologicalClosure hmem hInt
  have hs := (W.restrictScalars ℝ).smul_mem (μ.real univ) havg
  simpa only [measure_smul_average] using hs

/-- The integral components are literal integrals of the six differentiated
product kernels, with complex weight F and actual planar volume. -/
theorem integratedKernelJet_apply (k : ProductKernel) (A a b B d e : ℝ)
    {F : (ℝ × ℝ) → ℂ} (hF : Continuous F) (p : planeBox B d e) (ij : JetIndex) :
    integratedKernelJet k A a b B d e F p ij =
      ∫ t in planeBox A a b,
        F t * iteratedDeriv ij.1.1.val k.horizontal (p.1.1 - t.1) *
          iteratedDeriv ij.1.2.val k.vertical (p.1.2 - t.2) := by
  let L : SixJet B d e →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj ij).comp (ContinuousMap.evalCLM ℝ p)
  have h := L.integral_comp_comm (weightedKernelJet_integrable k A a b B d e hF)
  simpa only [L, integratedKernelJet, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousMap.evalCLM_apply,
    ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul, kernelJet, mul_assoc] using h.symm

/-- Genuine finite simultaneous approximation of all six literal partial
jets of a product-kernel smoothing, with one common finite coefficient set.
Together with the support and core identity above, this is the quadrature
step needed by C2 compact tensor approximation; it does not assume it. -/
theorem exists_finite_product_sixJet_approximation (k : ProductKernel)
    (A a b B d e : ℝ) {F : (ℝ × ℝ) → ℂ} (hF : Continuous F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : planeBox A a b →₀ ℂ, ∀ p : planeBox B d e, ∀ ij : JetIndex,
      ‖partialJet ij (finiteKernelSum k c) p.1 -
        ∫ t in planeBox A a b,
          F t * iteratedDeriv ij.1.1.val k.horizontal (p.1.1 - t.1) *
            iteratedDeriv ij.1.2.val k.vertical (p.1.2 - t.2)‖ < ε := by
  let V := Submodule.span ℂ (Set.range fun t : planeBox A a b => kernelJet k B d e t.1)
  have hmem : integratedKernelJet k A a b B d e F ∈ closure (V : Set (SixJet B d e)) :=
    integratedKernelJet_mem_closedSpan k A a b B d e hF
  obtain ⟨v, hv, hdist⟩ := Metric.mem_closure_iff.1 hmem ε hε
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
  refine ⟨c, ?_⟩
  intro p ij
  have hnorm : ‖v - integratedKernelJet k A a b B d e F‖ < ε := by
    rw [← dist_eq_norm, dist_comm]
    exact hdist
  have hpoint := (norm_le_pi_norm ((v - integratedKernelJet k A a b B d e F) p) ij).trans
    ((v - integratedKernelJet k A a b B d e F).norm_coe_le_norm p)
  have hfinite : v p ij = partialJet ij (finiteKernelSum k c) p.1 := by
    rw [← hc, finiteKernelSum_partialJet]
    simp only [Finsupp.sum, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      Pi.sum_apply, Pi.smul_apply, smul_eq_mul, kernelJet, mul_assoc]
  have heval := integratedKernelJet_apply k A a b B d e hF p ij
  have hlt := hpoint.trans_lt hnorm
  simpa only [ContinuousMap.sub_apply, Pi.sub_apply, hfinite, heval] using hlt

end ImbalancedChen.Part3.CompactProductKernelSixJet20261025a