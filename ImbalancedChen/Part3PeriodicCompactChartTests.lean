import ImbalancedChen.Part3PeriodicCompactPartitionUnfolding
import ImbalancedChen.Part3PlanarFrechetCompactGreen

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual compact real-chart tests obtained from smooth periodic circle
tests by the genuine horizontal integer partition. Joint smoothness,
compact positive-height support and the literal ordinary horizontal
derivative are proved. Conjugating the test inserts it into the standard
sesquilinear raw local weak derivative equation and yields the bilinear
partitioned tensor equation, with its alpha' seam term explicit.
No boundary trace or pointwise derivative of the unknown is assumed.
-/
namespace ImbalancedChen.Part3.PeriodicCompactChartTests20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
open SmoothIntegerUnitPartition20261026b
open ProductConvolutionSecondDerivatives20261026a PlanarFrechetCompactGreen20261026b

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def periodicChartTensor (χ : ℝ → ℝ) (φ : C(UnitAddCircle, ℂ)) (β : ℝ → ℝ)
    (p : Plane) : ℂ := (χ p.1 : ℂ) * φ (p.1 : UnitAddCircle) * (β p.2 : ℂ)

theorem periodicChartTensor_smooth {χ β : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (φ : C(UnitAddCircle, ℂ))
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ (t : UnitAddCircle)))
    (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (periodicChartTensor χ φ β) :=
  ((Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_fst)).mul
    (hφ.comp contDiff_fst)).mul (Complex.ofRealCLM.contDiff.comp (hβ.comp contDiff_snd))

theorem periodicChartTensor_tsupport {χ β : ℝ → ℝ} (φ : C(UnitAddCircle, ℂ)) :
    tsupport (periodicChartTensor χ φ β) ⊆ tsupport χ ×ˢ tsupport β := by
  apply closure_minimal _ ((isClosed_tsupport χ).prod (isClosed_tsupport β))
  intro p hp
  constructor
  · by_contra h
    exact hp (by simp [periodicChartTensor, image_eq_zero_of_notMem_tsupport h])
  · by_contra h
    exact hp (by simp [periodicChartTensor, image_eq_zero_of_notMem_tsupport h])

theorem periodicChartTensor_compact {χ β : ℝ → ℝ}
    (hχ : HasCompactSupport χ) (φ : C(UnitAddCircle, ℂ)) (hβ : HasCompactSupport β) :
    HasCompactSupport (periodicChartTensor χ φ β) :=
  (hχ.prod hβ).of_isClosed_subset isClosed_tsupport (periodicChartTensor_tsupport φ)

theorem periodicChartTensor_height_support {χ β : ℝ → ℝ} (φ : C(UnitAddCircle, ℂ))
    {a : ℝ} (hs : tsupport β ⊆ Ioi a) :
    tsupport (periodicChartTensor χ φ β) ⊆ {p : Plane | a < p.2} :=
  fun p hp => hs ((periodicChartTensor_tsupport φ hp).2)

/-- The compact tensor's derivative is computed by an actual real
HasDerivAt assertion and native Frechet/slice derivative identification. -/
theorem partition_chart_horizontal_derivative (φ ψ : C(UnitAddCircle, ℂ))
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ (t : UnitAddCircle)))
    (htest : ∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (s : UnitAddCircle))
      (ψ (t : UnitAddCircle)) t) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (p : Plane) :
    directional xDirection (periodicChartTensor horizontalUnitPartition φ β) p =
      periodicChartTensor (deriv horizontalUnitPartition) φ β p +
        periodicChartTensor horizontalUnitPartition ψ β p := by
  have hdα := (horizontalUnitPartition_cinfty.differentiable (by simp) p.1).hasDerivAt
  have hd := ((hdα.ofReal_comp).mul (htest p.1)).mul_const (β p.2 : ℂ)
  rw [directional_x_eq_slice
    (periodicChartTensor_smooth horizontalUnitPartition_cinfty φ hφ hβ)]
  simpa only [periodicChartTensor, add_mul] using hd.deriv

/-- Standard raw local horizontal distributional differentiation on a
real chart. The derivative in the equation is the actual ordinary
Frechet directional derivative of an arbitrary compact smooth test. -/
def HasRealChartHorizontalWeakDerivative (Ω : Set Plane) (F D : Plane → ℂ) : Prop :=
  ∀ Ψ : Plane → ℂ, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Ω →
    (∫ p : Plane, star (Ψ p) * D p) =
      -(∫ p : Plane, star (directional xDirection Ψ p) * F p)

/-- Inserting the explicit compact conjugate test yields a bilinear
tensor equation, including the seam term which will cancel by integer
partition unfolding rather than by a boundary trace assumption. -/
theorem local_weak_partition_tensor {a : ℝ} {F D : Plane → ℂ}
    (hweak : HasRealChartHorizontalWeakDerivative {p : Plane | a < p.2} F D)
    (φ ψ : C(UnitAddCircle, ℂ))
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ (t : UnitAddCircle)))
    (htest : ∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (s : UnitAddCircle))
      (ψ (t : UnitAddCircle)) t) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi a) :
    (∫ p : Plane, periodicChartTensor horizontalUnitPartition φ β p * D p) =
      -(∫ p : Plane,
        (periodicChartTensor (deriv horizontalUnitPartition) φ β p +
          periodicChartTensor horizontalUnitPartition ψ β p) * F p) := by
  let Ψ := periodicChartTensor horizontalUnitPartition φ β
  have hΨ : ContDiff ℝ ∞ Ψ :=
    periodicChartTensor_smooth horizontalUnitPartition_cinfty φ hφ hβ
  have hcΨ : HasCompactSupport Ψ :=
    periodicChartTensor_compact horizontalUnitPartition_compact φ hc
  have hsΨ : tsupport Ψ ⊆ {p : Plane | a < p.2} :=
    periodicChartTensor_height_support φ hs
  have h := hweak (fun p => star (Ψ p)) hΨ.star (hcΨ.comp_left (by simp))
    ((tsupport_comp_subset (by simp) Ψ).trans hsΨ)
  simpa only [star_star, directional_star,
    partition_chart_horizontal_derivative φ ψ hφ htest hβ, Ψ] using h

end
end ImbalancedChen.Part3.PeriodicCompactChartTests20261026b
