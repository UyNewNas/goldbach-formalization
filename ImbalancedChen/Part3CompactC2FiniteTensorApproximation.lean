import ImbalancedChen.Part3CompactC2ProductMollifier
import ImbalancedChen.Part3Gamma0SmoothCompactTensorCore
import ImbalancedChen.Part3CompactSeedSmoothPlaneExtension

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual compact C-infinity plane functions with support at positive height
admit simultaneous uniform C2 approximation by finite actual smooth compact
product tensors. EVERY approximation has support in the SAME explicit
compact positive rectangle, independent of epsilon. The output is the
existing SmoothCompactTensor type, not merely the weaker C2 tensor type.
The complete six-jet conclusion includes literal value, xx and yy errors.

This is Euclidean approximation only. No Gamma periodization continuity,
quotient graph norm, closure domain or arbitrary smooth-core membership is
assumed or concluded. The original compact upper-half-plane seed is accepted
through its genuinely proved full-plane smooth zero extension.
-/

noncomputable section
namespace ImbalancedChen.Part3.CompactC2FiniteTensorApproximation20261026a

open Set MeasureTheory
open scoped Topology UpperHalfPlane
open CompactProductKernelSixJet20261025a CompactC2ProductMollifier20261026a
open MaassWeakOperatorCore20261024zz Gamma0SmoothCompactTensorCore20261025a
open Gamma0CompactGreenProductL120261025a Gamma0CompactUpperChartExtension20261025a
open CompactSeedSmoothPlaneExtension20261025a
open Gamma0CompactTensorPoincareC2Core20261025a Gamma0CompactCarrierBump20261025a

/-- A fixed common compact support, independent of the approximation error. -/
def commonBox (A a b : ℝ) : Set Plane := planeBox (A + 1) (a / 2) (b + 1)

instance commonBox_compactSpace (A a b : ℝ) : CompactSpace (commonBox A a b) :=
  planeBox_compactSpace _ _ _

theorem commonBox_isCompact (A a b : ℝ) : IsCompact (commonBox A a b) :=
  isCompact_planeBox _ _ _

def actualSmoothTensor (T : SmoothProduct) : SmoothCompactTensor where
  toCompactTensor := T.toCompactTensor
  horizontal_cinfty := T.horizontal_smooth
  vertical_cinfty := T.vertical_smooth

def sampledFamily (k : ProductKernel) {A a b : ℝ} (ha : k.radius < a)
    (c : planeBox A a b →₀ ℂ) (t : planeBox A a b) : SmoothCompactTensor :=
  actualSmoothTensor (scaledProduct (c t) (translatedProduct k ha t))

theorem sampledFamily_chart (k : ProductKernel) {A a b : ℝ} (ha : k.radius < a)
    (c : planeBox A a b →₀ ℂ) :
    finiteChartFunction c.support (fun t => (sampledFamily k ha c t).toCompactTensor) =
      finiteKernelSum k c := by
  funext p
  simp only [finiteChartFunction, sampledFamily, actualSmoothTensor,
    SmoothProduct.toCompactTensor, scaledProduct, translatedProduct, finiteKernelSum]

theorem expandedBox_subset_commonBox {A a b r : ℝ} (hr : r ≤ 1) (hra : r ≤ a / 2) :
    Icc (-A - r) (A + r) ×ˢ Icc (a - r) (b + r) ⊆ commonBox A a b := by
  intro p hp
  change (-(A + 1) ≤ p.1 ∧ p.1 ≤ A + 1) ∧ (a / 2 ≤ p.2 ∧ p.2 ≤ b + 1)
  constructor <;> constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]

theorem sampledFamily_horizontal_support (k : ProductKernel) {A a b : ℝ}
    (ha : k.radius < a) (c : planeBox A a b →₀ ℂ) (hr : k.radius ≤ 1)
    (t : planeBox A a b) :
    tsupport (sampledFamily k ha c t).horizontal ⊆ Icc (-(A + 1)) (A + 1) := by
  intro x hx
  change x ∈ tsupport (fun x => c t * k.horizontal (x - t.1.1)) at hx
  have hs := horizontal_shift_support k t (tsupport_mul_subset_right hx)
  constructor <;> linarith [hs.1, hs.2]

theorem sampledFamily_vertical_support (k : ProductKernel) {A a b : ℝ}
    (ha : k.radius < a) (c : planeBox A a b →₀ ℂ) (hr : k.radius ≤ 1)
    (hra : k.radius ≤ a / 2) (t : planeBox A a b) :
    tsupport (sampledFamily k ha c t).vertical ⊆ Icc (a / 2) (b + 1) := by
  intro y hy
  have hs := vertical_shift_support k t hy
  constructor <;> linarith [hs.1, hs.2]

/-- Genuine derivatives cannot enlarge topological support. -/
theorem directionalIter_tsupport_subset (v : Plane) (n : ℕ) (F : Plane → ℂ) :
    tsupport (directionalIter v n F) ⊆ tsupport F := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih => exact (tsupport_fderiv_apply_subset ℝ v).trans ih

theorem partialJet_tsupport_subset {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (ij : JetIndex) : tsupport (fun p => partialJet ij F p) ⊆ tsupport F := by
  have heq : (fun p => partialJet ij F p) = mixedJet F ij :=
    funext (partialJet_eq_mixedJet hF ij)
  rw [heq]
  exact (directionalIter_tsupport_subset ex ij.1.1.val _).trans
    (directionalIter_tsupport_subset ey ij.1.2.val F)
/-- All data are actual: the family is finite, each factor is C-infinity
compact, the common support is explicit, and the errors concern the real
coordinate derivatives of its literal finite chart function. -/
structure CompactC2TensorApproximation (F : Plane → ℂ) (A a b ε : ℝ) where
  indices : Finset (planeBox A a b)
  tensors : planeBox A a b → SmoothCompactTensor
  source_smooth : ContDiff ℝ ∞ F
  source_support : tsupport F ⊆ commonBox A a b
  horizontal_support : ∀ t, tsupport (tensors t).horizontal ⊆ Icc (-(A + 1)) (A + 1)
  vertical_support : ∀ t, tsupport (tensors t).vertical ⊆ Icc (a / 2) (b + 1)
  common_support : tsupport (finiteChartFunction indices
    (fun t => (tensors t).toCompactTensor)) ⊆ commonBox A a b
  uniform_sixJet_error : ∀ p : commonBox A a b, ∀ ij : JetIndex,
    ‖partialJet ij (finiteChartFunction indices (fun t => (tensors t).toCompactTensor)) p.1 -
      partialJet ij F p.1‖ < ε

/-- No C2 approximation or core-density premise is supplied. A shared small
normalized mollifier radius and the genuine finite six-jet quadrature
produce the actual finite family. The support bound is fixed for ALL ε. -/
theorem exists_compactC2TensorApproximation {F : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (A a b : ℝ) (ha : 0 < a) (hs : tsupport F ⊆ planeBox A a b)
    (ε : ℝ) (hε : 0 < ε) : Nonempty (CompactC2TensorApproximation F A a b ε) := by
  obtain ⟨δ, hδ, hSmooth⟩ := exists_shared_radius_uniform_sixJet hF hc (ε / 2) (half_pos hε)
  let r : ℝ := min (δ / 2) (min (1 / 2 : ℝ) (a / 4))
  have hr : 0 < r := lt_min (half_pos hδ) (lt_min (by norm_num) (by positivity))
  have hrd : r ≤ δ := (min_le_left _ _).trans (half_le_self hδ.le)
  have hr1 : r ≤ 1 := by
    have h := (min_le_right (δ / 2) (min (1 / 2 : ℝ) (a / 4))).trans
      (min_le_left (1 / 2 : ℝ) (a / 4))
    linarith
  have hra : r ≤ a / 2 := by
    have h := (min_le_right (δ / 2) (min (1 / 2 : ℝ) (a / 4))).trans
      (min_le_right (1 / 2 : ℝ) (a / 4))
    linarith
  have hra' : r < a := hra.trans_lt (half_lt_self ha)
  let k := normalizedProductKernel r hr
  obtain ⟨c, hQuad⟩ := exists_finite_product_sixJet_approximation k
    A a b (A + 1) (a / 2) (b + 1) hF.continuous (ε / 2) (half_pos hε)
  refine ⟨{
    indices := c.support
    tensors := sampledFamily k hra' c
    source_smooth := hF
    source_support := ?_
    horizontal_support := sampledFamily_horizontal_support k hra' c hr1
    vertical_support := sampledFamily_vertical_support k hra' c hr1 hra
    common_support := ?_
    uniform_sixJet_error := ?_ }⟩
  · intro p hp
    have h := hs hp
    change (-(A + 1) ≤ p.1 ∧ p.1 ≤ A + 1) ∧ (a / 2 ≤ p.2 ∧ p.2 ≤ b + 1)
    constructor <;> constructor <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]
  · rw [sampledFamily_chart]
    exact (finiteKernelSum_support k c).trans (expandedBox_subset_commonBox hr1 hra)
  · intro p ij
    rw [sampledFamily_chart]
    have hQ := hQuad p ij
    rw [← productSmoothing_partialJet_boxIntegral r hr hF hc A a b hs ij p.1] at hQ
    have hS := hSmooth r hr hrd p.1 ij
    calc
      ‖partialJet ij (finiteKernelSum k c) p.1 - partialJet ij F p.1‖
          ≤ ‖partialJet ij (finiteKernelSum k c) p.1 -
              partialJet ij (productSmoothing r hr F) p.1‖ +
            ‖partialJet ij (productSmoothing r hr F) p.1 - partialJet ij F p.1‖ :=
        norm_sub_le _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hQ hS
      _ = ε := add_halves ε

/-- The common support and true derivative support theorem upgrade the
fixed-rectangle estimate to a GLOBAL estimate; outside it both jets vanish. -/
theorem CompactC2TensorApproximation.uniform_sixJet_error_global
    {F : Plane → ℂ} {A a b ε : ℝ} (P : CompactC2TensorApproximation F A a b ε)
    (hε : 0 < ε) (p : Plane) (ij : JetIndex) :
    ‖partialJet ij (finiteChartFunction P.indices
      (fun t => (P.tensors t).toCompactTensor)) p - partialJet ij F p‖ < ε := by
  by_cases hp : p ∈ commonBox A a b
  · exact P.uniform_sixJet_error ⟨p, hp⟩ ij
  · have hG : ContDiff ℝ ∞ (finiteChartFunction P.indices
        (fun t => (P.tensors t).toCompactTensor)) :=
      finiteSmoothChart_contDiff P.indices P.tensors
    have hGzero : partialJet ij (finiteChartFunction P.indices
        (fun t => (P.tensors t).toCompactTensor)) p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp
        (P.common_support (partialJet_tsupport_subset hG ij h)))
    have hFzero : partialJet ij F p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp
        (P.source_support (partialJet_tsupport_subset P.source_smooth ij h)))
    simpa only [hGzero, hFzero, sub_self, norm_zero] using hε
def jet00 : JetIndex := ⟨(0, 0), by norm_num⟩
def jetXX : JetIndex := ⟨(2, 0), by norm_num⟩
def jetYY : JetIndex := ⟨(0, 2), by norm_num⟩

theorem partialJet_00 (F : Plane → ℂ) (p : Plane) : partialJet jet00 F p = F p := rfl

theorem partialJet_XX (F : Plane → ℂ) (p : Plane) :
    partialJet jetXX F p = deriv (deriv (fun x => F (x, p.2))) p.1 := by
  simp [partialJet, jetXX, iteratedDeriv_succ]

theorem partialJet_YY (F : Plane → ℂ) (p : Plane) :
    partialJet jetYY F p = deriv (deriv (fun y => F (p.1, y))) p.2 := by
  simp [partialJet, jetYY, iteratedDeriv_succ]

/-- The requested value/xx/yy consequences retain ONE finite approximation. -/
theorem CompactC2TensorApproximation.value_xx_yy {F : Plane → ℂ} {A a b ε : ℝ}
    (P : CompactC2TensorApproximation F A a b ε) (p : commonBox A a b) :
    let G := finiteChartFunction P.indices (fun t => (P.tensors t).toCompactTensor)
    ‖G p.1 - F p.1‖ < ε ∧
      ‖deriv (deriv (fun x => G (x, p.1.2))) p.1.1 -
        deriv (deriv (fun x => F (x, p.1.2))) p.1.1‖ < ε ∧
      ‖deriv (deriv (fun y => G (p.1.1, y))) p.1.2 -
        deriv (deriv (fun y => F (p.1.1, y))) p.1.2‖ < ε := by
  exact ⟨by simpa only [partialJet_00] using P.uniform_sixJet_error p jet00,
    by simpa only [partialJet_XX] using P.uniform_sixJet_error p jetXX,
    by simpa only [partialJet_YY] using P.uniform_sixJet_error p jetYY⟩

/-- A genuine compact smooth H test supplies the actual Euclidean
approximation data through its proved global smooth zero extension. -/
theorem exists_upper_seed_compactC2TensorApproximation (f : UpperHalfPlane → ℂ)
    (hfc : HasCompactSupport f) (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    ∃ A a b : ℝ, 0 ≤ A ∧ 0 < a ∧ a ≤ b ∧
      ∀ ε : ℝ, 0 < ε → Nonempty (CompactC2TensorApproximation (extendUpper f) A a b ε) := by
  obtain ⟨A, a, b, hA, ha, hab, hrect⟩ := compact_height_rectangle hfc
  have hs : tsupport (extendUpper f) ⊆ planeBox A a b := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := extendUpper_support_image f hfc hp
    exact hrect z hz
  refine ⟨A, a, b, hA, ha, hab, ?_⟩
  intro ε hε
  exact exists_compactC2TensorApproximation (extendUpper_cinfty f hfc hf)
    (extendUpper_hasCompactSupport f hfc) A a b ha hs ε hε

end ImbalancedChen.Part3.CompactC2FiniteTensorApproximation20261026a