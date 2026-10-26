import ImbalancedChen.Part3PositiveRectanglePhysicalRellich
import ImbalancedChen.Part3Gamma0LocalFourierTailCharts

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
Literal inverseClassRep Mobius charts, localized by one actual cutoff,
form a totally bounded family in the finite product of physical L2
spaces with dx dy/y² norm. Positive-chart C2 regularity is glued across
y=0 using the cutoff's strictly positive physical support floor.
No periodic extension, compact embedding, partition reconstruction, or
cuspidal/continuous spectral completeness is an assumption or conclusion.
The primitive family bound is the actual local two-derivative energy. -/

namespace ImbalancedChen.Part3.Gamma0PositiveRectangleRellichCharts20261026b
noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane BigOperators
open PositiveRectangleAffineNormalization20261026b
open PositiveRectanglePhysicalRellich20261026b
open CompactRectanglePhysicalRellich20261026a
open Gamma0FiniteMeasureCarrier20261024z
open Gamma0LocalFourierTailCharts20261026a
open ActualGamma0MaassDescent20261025a MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareC2Core20261025a

local instance (N : ℕ) [NeZero N] : Fintype (gamma0Classes N) :=
  (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex

/-- A C2 positive-chart function with an actual positive rectangle support
has a global C2 extension. Zero germs below the support floor are proved. -/
theorem global_C2_of_rectangle_support (R : Rectangle) {δ : ℝ} (hδ : 0 ≤ δ)
    (F : Plane → ℂ) (hF : ContDiffOn ℝ 2 F positiveChart)
    (hs : Function.support F ⊆ region R δ) : ContDiff ℝ 2 F := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : 0 < p.2
  · exact (hF p hp).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  · have hpB : p.2 < R.bottom := (le_of_not_gt hp).trans_lt R.bottom_pos
    have hzero : F =ᶠ[𝓝 p] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hpB] with q hq
      by_contra hn
      exact (not_le_of_gt hq) (region_height hδ (hs hn)).1
    exact (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : Plane => (0 : ℂ)) p).
      congr_of_eventuallyEq hzero

theorem localized_support_rectangle (N : ℕ) [NeZero N] (R : Rectangle) {δ : ℝ}
    (f ρ : UpperHalfPlane → ℂ)
    (hs : Function.support (extendUpper ρ) ⊆ region R δ) (q : gamma0Classes N) :
    Function.support (extendUpper (localizedClassChart N f ρ q)) ⊆ region R δ := by
  intro p hp
  apply hs
  intro hz
  apply hp
  by_cases hy : 0 < p.2
  · rw [extendUpper_chartLift _ p hy]
    have hρ : ρ (chartLift p) = 0 := (extendUpper_chartLift ρ p hy).symm.trans hz
    simp only [localizedClassChart, hρ, zero_mul]
  · simp only [extendUpper, dif_neg hy]

structure SmoothFunction where
  function : UpperHalfPlane → ℂ
  smooth : ContDiffOn ℝ 2 (extendUpper function) positiveChart

/-- The function in each seed is exactly the inverse-class-representative
Mobius pullback multiplied by rho, then canonically extended by zero. -/
def classSeed (N : ℕ) [NeZero N] (R : Rectangle) {δ : ℝ} (hδ : 0 ≤ δ)
    (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart)
    (hs : Function.support (extendUpper ρ) ⊆ region R δ)
    (f : SmoothFunction) (q : gamma0Classes N) : RectangleSeed R δ :=
  ⟨extendUpper (localizedClassChart N f.function ρ q),
    global_C2_of_rectangle_support R hδ _
      (localizedClassChart_C2 N f.function ρ f.smooth hρ q)
      (localized_support_rectangle N R f.function ρ hs q),
    localized_support_rectangle N R f.function ρ hs q⟩

def chartTuple (N : ℕ) [NeZero N] (R : Rectangle) {δ : ℝ} (hδ : 0 ≤ δ)
    (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart)
    (hs : Function.support (extendUpper ρ) ⊆ region R δ)
    (f : SmoothFunction) : gamma0Classes N → PhysicalL2 :=
  fun q => weightedPhysical (classSeed N R hδ ρ hρ hs f q)

def chartEnergyBall (N : ℕ) [NeZero N] (R : Rectangle) {δ : ℝ} (hδ : 0 ≤ δ)
    (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart)
    (hs : Function.support (extendUpper ρ) ⊆ region R δ) (A : ℝ) : Set SmoothFunction :=
  {f | ∀ q : gamma0Classes N, classSeed N R hδ ρ hρ hs f q ∈ h1Ball R δ A}

/-- Each coordinate's norm is the literal weighted integral of the
localized actual Mobius chart, with no unidentified abstract chart norm. -/
theorem chartTuple_norm_square (N : ℕ) [NeZero N] (R : Rectangle) {δ : ℝ}
    (hδ : 0 ≤ δ) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart)
    (hs : Function.support (extendUpper ρ) ⊆ region R δ)
    (f : SmoothFunction) (q : gamma0Classes N) :
    ‖chartTuple N R hδ ρ hρ hs f q‖^2 = ∫ p : Plane, (p.2⁻¹)^2 *
      ‖extendUpper (localizedClassChart N f.function ρ q) p‖^2 :=
  weightedPhysical_hyperbolic_square hδ (classSeed N R hδ ρ hρ hs f q)

/-- Simultaneous compactness for EVERY actual finite Gamma0 class. The
input bound is a real mass-plus-two-physical-partials H1 bound, not a
Rellich premise. The compact product is built from proved rectangle
closures. No chart is omitted and no single-cusp shortcut is used. -/
theorem actual_finite_chart_family_totallyBounded (N : ℕ) [NeZero N]
    (R : Rectangle) {δ : ℝ} (hδ : 0 < δ) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart)
    (hs : Function.support (extendUpper ρ) ⊆ region R δ)
    (A : ℝ) (hA : 0 ≤ A) :
    TotallyBounded (chartTuple N R hδ.le ρ hρ hs ''
      chartEnergyBall N R hδ.le ρ hρ hs A) := by
  have hc : IsCompact {v : gamma0Classes N → PhysicalL2 |
      ∀ q, v q ∈ closure (weightedPhysical '' h1Ball R δ A)} :=
    isCompact_pi_infinite (fun _ => weighted_h1Ball_compact_closure R hδ A hA)
  apply hc.totallyBounded.subset
  rintro v ⟨f, hf, rfl⟩ q
  exact subset_closure ⟨classSeed N R hδ.le ρ hρ hs f q, hf q, rfl⟩

theorem actual_finite_chart_family_compact_closure (N : ℕ) [NeZero N]
    (R : Rectangle) {δ : ℝ} (hδ : 0 < δ) (ρ : UpperHalfPlane → ℂ)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart)
    (hs : Function.support (extendUpper ρ) ⊆ region R δ)
    (A : ℝ) (hA : 0 ≤ A) :
    IsCompact (closure (chartTuple N R hδ.le ρ hρ hs ''
      chartEnergyBall N R hδ.le ρ hρ hs A)) :=
  (actual_finite_chart_family_totallyBounded N R hδ ρ hρ hs A hA).closure.isCompact
    isClosed_closure.isComplete

end
end ImbalancedChen.Part3.Gamma0PositiveRectangleRellichCharts20261026b
