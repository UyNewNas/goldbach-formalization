import ImbalancedChen.Part3ActualHorizontalGreenTensorTests

/-!
CODE_ONLY / SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Exact norm and distance factorization for actual compact continuous planar
L2 tensors. This supplies the real error estimate for transporting one-
dimensional horizontal derivative approximation to actual planar tests.
-/

noncomputable section

namespace ImbalancedChen.Part3.ActualPlanarTensorL2NormSourceOnly

open MeasureTheory Set
open CanonicalTensorHyperbolicLaplacianForm20261024z MaassFirstGradientWeakLimit20261025a
open ActualHorizontalGreenTensorTestsSourceOnly

abbrev LineL2 := Lp (α := ℝ) ℂ 2 volume

def lineL2 (g : ℝ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) : LineL2 :=
  (hg.memLp_of_hasCompactSupport hgc).toLp g

def planeTensorL2 (g v : ℝ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hv : Continuous v) (hvc : HasCompactSupport v) : PlaneL2 :=
  (separated_plane_memLp g v hg hv hgc hvc).toLp (tensorFunction g v)

theorem lineL2_coe_ae (g : ℝ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    (lineL2 g hg hgc : ℝ → ℂ) =ᵐ[volume] g :=
  (hg.memLp_of_hasCompactSupport hgc).coeFn_toLp

theorem planeTensorL2_coe_ae (g v : ℝ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    (planeTensorL2 g v hg hgc hv hvc : ℝ × ℝ → ℂ) =ᵐ[volume] tensorFunction g v :=
  (separated_plane_memLp g v hg hv hgc hvc).coeFn_toLp

private theorem integral_norm_sq_lp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : Lp ℂ 2 μ) : (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) f f).symm

private theorem integral_norm_sq_line (g : ℝ → ℂ) (hg : Continuous g)
    (hgc : HasCompactSupport g) : (∫ x : ℝ, ‖g x‖ ^ 2) = ‖lineL2 g hg hgc‖ ^ 2 := by
  calc
    _ = ∫ x : ℝ, ‖lineL2 g hg hgc x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [lineL2_coe_ae g hg hgc] with x hx
      rw [hx]
    _ = _ := integral_norm_sq_lp _ _

theorem planeTensorL2_norm_sq (g v : ℝ → ℂ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hv : Continuous v) (hvc : HasCompactSupport v) :
    ‖planeTensorL2 g v hg hgc hv hvc‖ ^ 2 =
      ‖lineL2 g hg hgc‖ ^ 2 * ‖lineL2 v hv hvc‖ ^ 2 := by
  calc
    _ = ∫ p : ℝ × ℝ, ‖planeTensorL2 g v hg hgc hv hvc p‖ ^ 2 :=
      (integral_norm_sq_lp _ _).symm
    _ = ∫ p : ℝ × ℝ, ‖tensorFunction g v p‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [planeTensorL2_coe_ae g v hg hgc hv hvc] with p hp
      rw [hp]
    _ = ∫ p : ℝ × ℝ, ‖g p.1‖ ^ 2 * ‖v p.2‖ ^ 2 := by
      simp only [tensorFunction, norm_mul, mul_pow]
    _ = (∫ x : ℝ, ‖g x‖ ^ 2) * (∫ y : ℝ, ‖v y‖ ^ 2) := by
      rw [integral_prod_mul]
    _ = _ := by rw [integral_norm_sq_line g hg hgc, integral_norm_sq_line v hv hvc]

theorem planeTensorL2_norm (g v : ℝ → ℂ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hv : Continuous v) (hvc : HasCompactSupport v) :
    ‖planeTensorL2 g v hg hgc hv hvc‖ = ‖lineL2 g hg hgc‖ * ‖lineL2 v hv hvc‖ := by
  have hs := planeTensorL2_norm_sq g v hg hgc hv hvc
  have hsq : (‖lineL2 g hg hgc‖ * ‖lineL2 v hv hvc‖) ^ 2 =
      ‖lineL2 g hg hgc‖ ^ 2 * ‖lineL2 v hv hvc‖ ^ 2 := mul_pow _ _ _
  have hp : 0 ≤ ‖lineL2 g hg hgc‖ * ‖lineL2 v hv hvc‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (planeTensorL2 g v hg hgc hv hvc)]

theorem lineL2_sub (g h : ℝ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hh : Continuous h) (hhc : HasCompactSupport h) :
    lineL2 (g - h) (hg.sub hh) (hgc.sub hhc) = lineL2 g hg hgc - lineL2 h hh hhc :=
  MemLp.toLp_sub (hg.memLp_of_hasCompactSupport hgc) (hh.memLp_of_hasCompactSupport hhc)

theorem planeTensorL2_sub (g h v : ℝ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hh : Continuous h) (hhc : HasCompactSupport h) (hv : Continuous v) (hvc : HasCompactSupport v) :
    planeTensorL2 (g - h) v (hg.sub hh) (hgc.sub hhc) hv hvc =
      planeTensorL2 g v hg hgc hv hvc - planeTensorL2 h v hh hhc hv hvc := by
  have hmg := separated_plane_memLp g v hg hv hgc hvc
  have hmh := separated_plane_memLp h v hh hv hhc hvc
  have hpoint : tensorFunction (g - h) v = tensorFunction g v - tensorFunction h v := by
    funext p
    simp only [tensorFunction, Pi.sub_apply, sub_mul]
  change (separated_plane_memLp (g - h) v (hg.sub hh) hv (hgc.sub hhc) hvc).toLp _ = _
  calc
    _ = (hmg.sub hmh).toLp (tensorFunction g v - tensorFunction h v) :=
      MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun p => congrFun hpoint p)
    _ = _ := MemLp.toLp_sub hmg hmh

/-- The exact tensorization estimate needed by the derivative-density
argument; neither finite measure of the plane nor bounded support size is assumed. -/
theorem planeTensorL2_distance (g h v : ℝ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hh : Continuous h) (hhc : HasCompactSupport h) (hv : Continuous v) (hvc : HasCompactSupport v) :
    ‖planeTensorL2 g v hg hgc hv hvc - planeTensorL2 h v hh hhc hv hvc‖ =
      ‖lineL2 g hg hgc - lineL2 h hh hhc‖ * ‖lineL2 v hv hvc‖ := by
  rw [← planeTensorL2_sub g h v hg hgc hh hhc hv hvc,
    planeTensorL2_norm, lineL2_sub]

end ImbalancedChen.Part3.ActualPlanarTensorL2NormSourceOnly
