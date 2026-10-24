import ImbalancedChen.Part3ActualKProfileLp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED.
The actual positive-parameter Laplace profile is a continuous L² curve.
The distance identity is proved from pointwise exponentials and genuine
integrals, not from an assumed Hilbert-space continuity statement.
-/

namespace ImbalancedChen.Part3.P3ActualKProfileL2ContinuitySourceOnly

noncomputable section

open Set MeasureTheory Filter
open ImbalancedChen.Part3.ImaginaryOrderKBesselSourceOnly
open ImbalancedChen.Part3.P3ActualKProfileLpSourceOnly

private theorem full_exp_cosh_integral {s : ℝ} (hs : 0 < s) :
    (∫ u : ℝ, Real.exp (-s * Real.cosh u)) =
      2 * imaginaryOrderK 0 s := by
  calc
    (∫ u : ℝ, Real.exp (-s * Real.cosh u)) =
        ∫ u : ℝ, Real.exp (-s * Real.cosh |u|) := by
      congr 1
      funext u
      rw [Real.cosh_abs]
    _ = 2 * ∫ u in Ioi (0 : ℝ), Real.exp (-s * Real.cosh u) := by
      exact integral_comp_abs (f := fun u : ℝ => Real.exp (-s * Real.cosh u))
    _ = 2 * imaginaryOrderK 0 s := by
      simp [imaginaryOrderK, kIntegrand]

private theorem exp_cosh_integrable {s : ℝ} (hs : 0 < s) :
    Integrable (fun u : ℝ => Real.exp (-s * Real.cosh u)) := by
  simpa only [evenLaplaceProfile, Complex.ofReal_re] using
    (evenLaplaceProfile_integrable hs).re

private theorem profile_sub_norm_sq_pointwise (q r u : ℝ) :
    ‖evenLaplaceProfile q u - evenLaplaceProfile r u‖ ^ 2 =
      Real.exp (-(2 * q) * Real.cosh u) +
      Real.exp (-(2 * r) * Real.cosh u) -
      2 * Real.exp (-(q + r) * Real.cosh u) := by
  let A : ℝ := Real.exp (-q * Real.cosh u)
  let B : ℝ := Real.exp (-r * Real.cosh u)
  have hqq : A ^ 2 = Real.exp (-(2 * q) * Real.cosh u) := by
    dsimp [A]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hrr : B ^ 2 = Real.exp (-(2 * r) * Real.cosh u) := by
    dsimp [B]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hqr : A * B = Real.exp (-(q + r) * Real.cosh u) := by
    dsimp [A, B]
    rw [← Real.exp_add]
    congr 1
    ring
  change ‖(A : ℂ) - (B : ℂ)‖ ^ 2 = _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, sub_sq, hqq, hrr, hqr]
  ring

/-- The full-line square distance has three actual K₀ integrals. -/
theorem evenLaplaceProfile_sub_norm_sq_integral {q r : ℝ}
    (hq : 0 < q) (hr : 0 < r) :
    (∫ u : ℝ, ‖evenLaplaceProfile q u - evenLaplaceProfile r u‖ ^ 2) =
      2 * imaginaryOrderK 0 (2 * q) +
      2 * imaginaryOrderK 0 (2 * r) -
      4 * imaginaryOrderK 0 (q + r) := by
  have hq2 : 0 < 2 * q := by linarith
  have hr2 : 0 < 2 * r := by linarith
  have hqr : 0 < q + r := by linarith
  have hA := exp_cosh_integrable hq2
  have hB := exp_cosh_integrable hr2
  have hC := exp_cosh_integrable hqr
  calc
    (∫ u : ℝ, ‖evenLaplaceProfile q u - evenLaplaceProfile r u‖ ^ 2) =
        ∫ u : ℝ,
          (Real.exp (-(2 * q) * Real.cosh u) +
            Real.exp (-(2 * r) * Real.cosh u)) -
            2 * Real.exp (-(q + r) * Real.cosh u) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (profile_sub_norm_sq_pointwise q r)
    _ = (∫ u : ℝ, Real.exp (-(2 * q) * Real.cosh u)) +
        (∫ u : ℝ, Real.exp (-(2 * r) * Real.cosh u)) -
        2 * (∫ u : ℝ, Real.exp (-(q + r) * Real.cosh u)) := by
      rw [integral_sub (hA.add hB) (hC.const_mul 2), integral_add hA hB,
        integral_const_mul]
    _ = 2 * imaginaryOrderK 0 (2 * q) +
        2 * imaginaryOrderK 0 (2 * r) -
        4 * imaginaryOrderK 0 (q + r) := by
      rw [full_exp_cosh_integral hq2, full_exp_cosh_integral hr2,
        full_exp_cosh_integral hqr]
      ring

/-- A genuine L² class for each positive Laplace parameter. -/
def evenLaplaceProfileLp (q : Ioi (0 : ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (evenLaplaceProfile_memLp_two q.property).toLp (evenLaplaceProfile q)

private theorem lp_norm_sq_eq_integral_norm_sq
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ u : ℝ, ‖f u‖ ^ 2 := by
  calc
    ‖f‖ ^ 2 = Complex.re (inner ℂ f f) := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    _ = Complex.re (∫ u : ℝ, inner ℂ (f u) (f u)) := by
      rw [L2.inner_def]
    _ = ∫ u : ℝ, ‖f u‖ ^ 2 := by
      rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
      congr 1
      funext u
      rw [inner_self_eq_norm_sq_to_K]
      simp

/-- Squared L² distance, retaining the full-line factor of two. -/
theorem evenLaplaceProfileLp_distance_sq (q r : Ioi (0 : ℝ)) :
    ‖evenLaplaceProfileLp q - evenLaplaceProfileLp r‖ ^ 2 =
      2 * imaginaryOrderK 0 (2 * (q : ℝ)) +
      2 * imaginaryOrderK 0 (2 * (r : ℝ)) -
      4 * imaginaryOrderK 0 ((q : ℝ) + (r : ℝ)) := by
  let hq := evenLaplaceProfile_memLp_two q.property
  let hr := evenLaplaceProfile_memLp_two r.property
  have hsub : MemLp (evenLaplaceProfile q - evenLaplaceProfile r) 2
      (volume : Measure ℝ) := hq.sub hr
  calc
    ‖evenLaplaceProfileLp q - evenLaplaceProfileLp r‖ ^ 2 =
        ‖hsub.toLp (evenLaplaceProfile q - evenLaplaceProfile r)‖ ^ 2 := by
      rw [show hsub.toLp (evenLaplaceProfile q - evenLaplaceProfile r) =
        evenLaplaceProfileLp q - evenLaplaceProfileLp r from hq.toLp_sub hr]
    _ = ∫ u : ℝ,
        ‖(hsub.toLp (evenLaplaceProfile q - evenLaplaceProfile r)) u‖ ^ 2 :=
      lp_norm_sq_eq_integral_norm_sq _
    _ = ∫ u : ℝ, ‖evenLaplaceProfile q u - evenLaplaceProfile r u‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hsub.coeFn_toLp] with u hu
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hu
    _ = _ := evenLaplaceProfile_sub_norm_sq_integral q.property r.property

private theorem k0_continuousAt {s : ℝ} (hs : 0 < s) :
    ContinuousAt (fun x : ℝ => imaginaryOrderK 0 x) s := by
  let a : ℝ := s / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have has : a < s := by dsimp [a]; linarith
  have hpair : Continuous (fun x : Ici a => ((0 : ℝ), x)) := by fun_prop
  have hsub : Continuous (fun x : Ici a => imaginaryOrderK 0 (x : ℝ)) :=
    (imaginaryOrderK_joint_continuous a ha).comp hpair
  have hOn : ContinuousOn (fun x : ℝ => imaginaryOrderK 0 x) (Ici a) := by
    exact continuousOn_iff_continuous_domRestrict.mpr hsub
  have hnhds : Ici a ∈ 𝓝 s :=
    Filter.mem_of_superset (isOpen_Ioi.mem_nhds has) Ioi_subset_Ici_self
  exact (hOn s has.le).continuousAt hnhds

/-- The actual positive-parameter profile is continuous in the Hilbert L² norm. -/
theorem evenLaplaceProfileLp_continuous :
    Continuous evenLaplaceProfileLp := by
  apply continuous_iff_continuousAt.mpr
  intro r
  have h2r : 0 < 2 * (r : ℝ) := by linarith [r.property]
  have hq2 : ContinuousAt
      (fun q : Ioi (0 : ℝ) => imaginaryOrderK 0 (2 * (q : ℝ))) r :=
    (k0_continuousAt h2r).comp
      ((continuous_const.mul continuous_subtype_val).continuousAt)
  have hqr : ContinuousAt
      (fun q : Ioi (0 : ℝ) => imaginaryOrderK 0 ((q : ℝ) + (r : ℝ))) r :=
    (k0_continuousAt (by linarith [r.property])).comp
      ((continuous_subtype_val.add continuous_const).continuousAt)
  have hExpr : Tendsto
      (fun q : Ioi (0 : ℝ) =>
        2 * imaginaryOrderK 0 (2 * (q : ℝ)) +
        2 * imaginaryOrderK 0 (2 * (r : ℝ)) -
        4 * imaginaryOrderK 0 ((q : ℝ) + (r : ℝ)))
      (𝓝 r) (𝓝 0) := by
    have hExprAt : ContinuousAt
        (fun q : Ioi (0 : ℝ) =>
          2 * imaginaryOrderK 0 (2 * (q : ℝ)) +
          2 * imaginaryOrderK 0 (2 * (r : ℝ)) -
          4 * imaginaryOrderK 0 ((q : ℝ) + (r : ℝ))) r :=
      ((continuousAt_const.mul hq2).add continuousAt_const).sub
        (continuousAt_const.mul hqr)
    have hzero :
        2 * imaginaryOrderK 0 (2 * (r : ℝ)) +
        2 * imaginaryOrderK 0 (2 * (r : ℝ)) -
        4 * imaginaryOrderK 0 ((r : ℝ) + (r : ℝ)) = 0 := by
      rw [show (r : ℝ) + (r : ℝ) = 2 * (r : ℝ) by ring]
      ring
    simpa only [hzero] using hExprAt.tendsto
  have hSq : Tendsto
      (fun q : Ioi (0 : ℝ) =>
        ‖evenLaplaceProfileLp q - evenLaplaceProfileLp r‖ ^ 2)
      (𝓝 r) (𝓝 0) := by
    simpa only [evenLaplaceProfileLp_distance_sq] using hExpr
  have hNorm : Tendsto
      (fun q : Ioi (0 : ℝ) =>
        ‖evenLaplaceProfileLp q - evenLaplaceProfileLp r‖)
      (𝓝 r) (𝓝 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hSq
    simpa [Real.sqrt_sq_eq_abs] using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hNorm

end

end ImbalancedChen.Part3.P3ActualKProfileL2ContinuitySourceOnly
