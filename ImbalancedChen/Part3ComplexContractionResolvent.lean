import ImbalancedChen.Part3PositiveContractionResolventCalculus
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

Actual complex continuous functional calculus resolvent on an arbitrary
complex Hilbert space: r_z(t)=t/(1-(1+z)t), Im(z) != 0. Reality of the
self-adjoint spectrum supplies nonvanishing denominators. The imaginary
part supplies the true operator norm bound 1/|Im(z)|.

Both inverse directions are proved for the actual relation
G(R)={(u,v):R(u+v)=u}, with forcing v-z*u. No resolvent or inverse identity
is a premise. Positivity/contraction are not needed for this CFC stage;
they are needed later for the nonnegative lambda=1/t-1 measure support.
-/

namespace ImbalancedChen.Part3.ComplexContractionResolvent20261025a

noncomputable section
open Set
open PositiveContractionResolventCalculus20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def complexDenominator (z w : ℂ) : ℂ := 1 - (1 + z) * w
def complexInverseDenominator (z w : ℂ) : ℂ := 1 / complexDenominator z w
def complexResolventRatio (z w : ℂ) : ℂ := w / complexDenominator z w

def complexResolvent (R : H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  cfc (complexResolventRatio z) R

def complexNormalizer (R : H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  1 - (1 + z) • R

def complexInverseNormalizer (R : H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  cfc (complexInverseDenominator z) R

private theorem complexDenominator_im_real (z : ℂ) (t : ℝ) :
    (complexDenominator z (t : ℂ)).im = -(z.im * t) := by
  simp [complexDenominator] <;> ring

theorem complexDenominator_real_ne_zero {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    complexDenominator z (t : ℂ) ≠ 0 := by
  by_cases ht : t = 0
  · simp [complexDenominator, ht]
  · intro hd
    have h := congrArg Complex.im hd
    rw [complexDenominator_im_real] at h
    simp only [Complex.zero_im, neg_eq_zero] at h
    exact (mul_ne_zero hz ht) h

theorem complexDenominator_spectrum_ne_zero (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    {z : ℂ} (hz : z.im ≠ 0) {w : ℂ} (hw : w ∈ spectrum ℂ R) :
    complexDenominator z w ≠ 0 := by
  rw [hSA.mem_spectrum_eq_re hw]
  exact complexDenominator_real_ne_zero hz w.re

theorem complexResolventRatio_real_norm_le {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    ‖complexResolventRatio z (t : ℂ)‖ ≤ 1 / |z.im| := by
  have himpos : 0 < |z.im| := abs_pos.mpr hz
  have hdenpos : 0 < ‖complexDenominator z (t : ℂ)‖ :=
    norm_pos_iff.mpr (complexDenominator_real_ne_zero hz t)
  have hnorm : |z.im| * |t| ≤ ‖complexDenominator z (t : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (complexDenominator z (t : ℂ))
    simpa only [complexDenominator_im_real, abs_neg, abs_mul] using h
  rw [complexResolventRatio, norm_div, Complex.norm_real, Real.norm_eq_abs]
  apply (div_le_div_iff₀ hdenpos himpos).2
  simpa only [one_mul, mul_comm] using hnorm

theorem complexDenominator_continuousOn (R : H →L[ℂ] H) (z : ℂ) :
    ContinuousOn (complexDenominator z) (spectrum ℂ R) := by
  have h : Continuous (complexDenominator z) := by unfold complexDenominator; fun_prop
  exact h.continuousOn

theorem complexInverseDenominator_continuousOn (R : H →L[ℂ] H)
    (hSA : IsSelfAdjoint R) {z : ℂ} (hz : z.im ≠ 0) :
    ContinuousOn (complexInverseDenominator z) (spectrum ℂ R) :=
  continuousOn_const.div (complexDenominator_continuousOn R z)
    (fun _ hw => complexDenominator_spectrum_ne_zero R hSA hz hw)

theorem complexResolventRatio_continuousOn (R : H →L[ℂ] H)
    (hSA : IsSelfAdjoint R) {z : ℂ} (hz : z.im ≠ 0) :
    ContinuousOn (complexResolventRatio z) (spectrum ℂ R) :=
  continuousOn_id.div (complexDenominator_continuousOn R z)
    (fun _ hw => complexDenominator_spectrum_ne_zero R hSA hz hw)

theorem cfc_complexDenominator (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R) (z : ℂ) :
    cfc (complexDenominator z) R = complexNormalizer R z := by
  unfold complexDenominator complexNormalizer
  rw [cfc_sub, cfc_const_one ℂ R hSA.isStarNormal,
    cfc_const_mul_id (1 + z) R hSA.isStarNormal]

theorem complexInverseNormalizer_mul (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    {z : ℂ} (hz : z.im ≠ 0) :
    complexInverseNormalizer R z * complexNormalizer R z = 1 := by
  rw [complexInverseNormalizer, ← cfc_complexDenominator R hSA z,
    ← cfc_mul (complexInverseDenominator z) (complexDenominator z) R
      (complexInverseDenominator_continuousOn R hSA hz) (complexDenominator_continuousOn R z)]
  have heq : (spectrum ℂ R).EqOn
      (fun w => complexInverseDenominator z w * complexDenominator z w) (fun _ => 1) := by
    intro w hw
    exact one_div_mul_cancel (complexDenominator_spectrum_ne_zero R hSA hz hw)
  rw [cfc_congr heq, cfc_const_one ℂ R hSA.isStarNormal]

theorem complexNormalizer_mul_inverse (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    {z : ℂ} (hz : z.im ≠ 0) :
    complexNormalizer R z * complexInverseNormalizer R z = 1 := by
  rw [complexInverseNormalizer, ← cfc_complexDenominator R hSA z,
    ← cfc_mul (complexDenominator z) (complexInverseDenominator z) R
      (complexDenominator_continuousOn R z) (complexInverseDenominator_continuousOn R hSA hz)]
  have heq : (spectrum ℂ R).EqOn
      (fun w => complexDenominator z w * complexInverseDenominator z w) (fun _ => 1) := by
    intro w hw
    exact mul_one_div_cancel (complexDenominator_spectrum_ne_zero R hSA hz hw)
  rw [cfc_congr heq, cfc_const_one ℂ R hSA.isStarNormal]

theorem complexResolvent_eq_inverse_mul (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    {z : ℂ} (hz : z.im ≠ 0) :
    complexResolvent R z = complexInverseNormalizer R z * R := by
  have heq : complexResolventRatio z = fun w => complexInverseDenominator z w * w := by
    funext w
    unfold complexResolventRatio complexInverseDenominator
    ring
  rw [complexResolvent, heq,
    cfc_mul (complexInverseDenominator z) (fun w : ℂ => w) R
      (complexInverseDenominator_continuousOn R hSA hz) continuousOn_id,
    cfc_id' ℂ R hSA.isStarNormal]
  rfl

theorem complexNormalizer_mul_resolvent (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    {z : ℂ} (hz : z.im ≠ 0) :
    complexNormalizer R z * complexResolvent R z = R := by
  rw [complexResolvent_eq_inverse_mul R hSA hz, ← mul_assoc,
    complexNormalizer_mul_inverse R hSA hz, one_mul]

/-- The genuine nonreal spectral-parameter operator norm bound. -/
theorem complexResolvent_norm_le (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    {z : ℂ} (hz : z.im ≠ 0) : ‖complexResolvent R z‖ ≤ 1 / |z.im| := by
  apply norm_cfc_le (by positivity)
  intro w hw
  rw [hSA.mem_spectrum_eq_re hw]
  exact complexResolventRatio_real_norm_le hz w.re

/-- First actual graph inverse direction for forcing v-z*u. -/
theorem complexResolvent_on_graph (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    {z : ℂ} (hz : z.im ≠ 0) {u v : H} (hgraph : (u, v) ∈ resolventGraph R) :
    complexResolvent R z (v - z • u) = u := by
  change R (u + v) = u at hgraph
  have hv : R v = u - R u := by
    apply (eq_sub_iff_add_eq).2
    simpa only [map_add, add_comm] using hgraph
  have hN : R (v - z • u) = complexNormalizer R z u := by
    rw [map_sub, map_smul, hv]
    change u - R u - z • R u = u - (1 + z) • R u
    module
  rw [complexResolvent_eq_inverse_mul R hSA hz]
  change complexInverseNormalizer R z (R (v - z • u)) = u
  rw [hN]
  exact congrArg (fun T : H →L[ℂ] H => T u) (complexInverseNormalizer_mul R hSA hz)

/-- Second actual graph inverse direction; the returned pair belongs to G(R). -/
theorem complexResolvent_graph_pair (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    {z : ℂ} (hz : z.im ≠ 0) (f : H) :
    (complexResolvent R z f, f + z • complexResolvent R z f) ∈ resolventGraph R := by
  let u := complexResolvent R z f
  have hN : complexNormalizer R z u = R f :=
    congrArg (fun T : H →L[ℂ] H => T f) (complexNormalizer_mul_resolvent R hSA hz)
  change R (u + (f + z • u)) = u
  rw [map_add, map_add, map_smul, ← hN]
  change R u + (u - (1 + z) • R u + z • R u) = u
  module

theorem existsUnique_complex_graph_solution (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    {z : ℂ} (hz : z.im ≠ 0) (f : H) :
    ∃! u : H, (u, f + z • u) ∈ resolventGraph R := by
  refine ⟨complexResolvent R z f, complexResolvent_graph_pair R hSA hz f, ?_⟩
  intro u hu
  have h := complexResolvent_on_graph R hSA hz hu
  have he : (f + z • u) - z • u = f := by abel
  rw [he] at h
  exact h.symm

end
end ImbalancedChen.Part3.ComplexContractionResolvent20261025a
