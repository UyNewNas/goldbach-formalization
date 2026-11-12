import ImbalancedChen.Part3ActualCharacterCriticalFamily
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! Relative to the critical boundary, the exact ordinary Young scalar has
one inverse Dirichlet factor. Its absolute-series majorant is independent
of the conductor, the vertical coordinate and the character, including
the principal square with its regularized reciprocal. -/
namespace ImbalancedChen.Part3.ActualEisensteinReciprocalGrowth20261110

noncomputable section
open Set Filter Topology Complex
open scoped Classical BigOperators LSeries.notation ArithmeticFunction.Moebius
open ActualCharacterCriticalFamily20261110

open scoped ComplexOrder in
private theorem norm_series_le_zeta (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : ‖LSeries f s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ := by
  have hreal (n : ℕ) :
      ((‖LSeries.term 1 (s.re : ℂ) n‖ : ℝ) : ℂ) = LSeries.term 1 (s.re : ℂ) n :=
    (Complex.eq_coe_norm_of_nonneg (LSeries.term_nonneg (by simp) s.re)).symm
  have hS := LSeriesHasSum_one (s := (s.re : ℂ)) (by simpa using hs)
  have E : ((∑' n, ‖LSeries.term 1 (s.re : ℂ) n‖ : ℝ) : ℂ) = riemannZeta (s.re : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact (tsum_congr hreal).trans hS.tsum_eq
  have B (n : ℕ) : ‖LSeries.term f s n‖ ≤ ‖LSeries.term 1 (s.re : ℂ) n‖ := by
    rw [LSeries.norm_term_eq,LSeries.norm_term_eq]
    split_ifs <;> simp only [Pi.one_apply,norm_one,Complex.ofReal_re] <;> first
      | exact le_rfl
      | exact div_le_div_of_nonneg_right (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have S := hS.summable.norm
  have H := S.of_nonneg_of_le (fun n => norm_nonneg _) B
  calc
    ‖LSeries f s‖ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm H
    _ ≤ ∑' n, ‖LSeries.term 1 (s.re : ℂ) n‖ := H.tsum_le_tsum B S
    _ = ‖riemannZeta (s.re : ℂ)‖ := by
      rw [← E,Complex.norm_real,Real.norm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]

/-- The majorant follows from the actual Dirichlet-character Möbius
inverse on the half-plane of absolute convergence. -/
theorem reciprocal_le_zeta {q : ℕ} [NeZero q] (η : DirichletCharacter ℂ q)
    (u : ℂ) (hu : 1 < u.re) : ‖reciprocalL η u‖ ≤ ‖riemannZeta (u.re : ℂ)‖ := by
  have hne : u ≠ 1 := fun e => (by simpa [e] using hu : False)
  have hn := DirichletCharacter.LFunction_ne_zero_of_one_le_re η (.inr hne) hu.le
  have R : reciprocalL η u = (η.LFunction u)⁻¹ := by
    by_cases h : η = 1
    · subst η
      rw [reciprocalL,if_pos rfl,DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hne]
      change (u-1)/((u-1)*(1 : DirichletCharacter ℂ q).LFunction u) = _
      field_simp [sub_ne_zero.mpr hne,hn]
    · simp [reciprocalL,h]
  let f : ℕ → ℂ := ↗η * ↗μ
  have I : η.LFunction u * LSeries f u = 1 := by
    rw [η.LFunction_eq_LSeries hu]
    exact DirichletCharacter.LSeries.mul_mu_eq_one η hu
  have E : (η.LFunction u)⁻¹ = LSeries f u := by
    calc
      _ = (η.LFunction u)⁻¹ * (η.LFunction u * LSeries f u) := by rw [I,mul_one]
      _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]
  rw [R,E]
  refine norm_series_le_zeta f ?_ u hu
  intro n
  change ‖η (n : ZMod q) * ((μ n : ℤ) : ℂ)‖ ≤ 1
  rw [norm_mul]
  have hμ : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
    norm_cast
    exact ArithmeticFunction.abs_moebius_le_one
  simpa using mul_le_mul (η.norm_le_one n) hμ (norm_nonneg _) zero_le_one

/-- A single bound works simultaneously for every Young channel on the
whole open half-strip `1/2 < Re s ≤ 3/2`. -/
theorem relative_reciprocal_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (η : DirichletCharacter ℂ q) (s : ℂ),
      1/2 < s.re → s.re ≤ 3/2 → (s.re-1/2)*‖reciprocalL η (2*s)‖ ≤ C := by
  have Cts : Continuous (fun x : ℝ => DirichletCharacter.LFunctionTrivChar₁ 1 (x : ℂ)) :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).continuous.comp Complex.continuous_ofReal
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (1 : ℝ) 3)).exists_bound_of_continuousOn Cts.continuousOn
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro q iq η s hs htop
  let x := (2*s).re
  have X : x = 2*s.re := by simp [x,Complex.mul_re]
  have hx : 1 < x := by rw [X]; linarith
  have hx3 : x ≤ 3 := by rw [X]; linarith
  have H := reciprocal_le_zeta η (2*s) hx
  have E : DirichletCharacter.LFunctionTrivChar₁ 1 (x : ℂ) = (x-1 : ℂ)*riemannZeta (x : ℂ) := by
    have X₁ : (x : ℂ) ≠ 1 := by exact_mod_cast hx.ne'
    rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne X₁]
    simp only [DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq]
  have h := hB x ⟨hx.le,hx3⟩
  rw [E,norm_mul,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
    Real.norm_of_nonneg (sub_nonneg.mpr hx.le)] at h
  have D := mul_le_mul_of_nonneg_left H (sub_nonneg.mpr hs.le)
  have : (s.re-1/2)*‖riemannZeta (x : ℂ)‖ ≤ (x-1)*‖riemannZeta (x : ℂ)‖ :=
    mul_le_mul_of_nonneg_right (by rw [X]; linarith) (norm_nonneg _)
  exact D.trans (this.trans (h.trans (le_max_left _ _)))

end
end ImbalancedChen.Part3.ActualEisensteinReciprocalGrowth20261110
