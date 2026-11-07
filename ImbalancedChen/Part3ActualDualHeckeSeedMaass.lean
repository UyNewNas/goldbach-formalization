import ImbalancedChen.Part3ActualDualHeckeSeedCompactSmooth
import ImbalancedChen.Part3ActualUpperMaassLinearity
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The existing upperMaass of the correct compact dual Hecke seed is exactly
the same dual transform of the ORIGINAL upperMaass seed. The literal real
affine inverse branches are differentiated twice using native one-variable
derivatives, including total-derivative conventions; y^2 cancels a^2.
Finite native seed summation and p^-1/2 scalar are paid by existing actual
Maass linearity and C2 finite-sum APIs. No transformed differential or
operator-domain commutation is a premise. This is arbitrary seed covariance,
not merely an eigenfunction equation.
-/

namespace ImbalancedChen.Part3.ActualDualHeckeSeedMaass20261026b
noncomputable section
open Set Filter Matrix Matrix.SpecialLinearGroup
open scoped UpperHalfPlane Topology BigOperators
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeRealBranch20261026b
open ActualClassicalHeckeMaass20261026b ActualCompactSeedHeckeReindex20261026b
open ActualDualHeckeSeedCompactSmooth20261026b ActualUpperMaassLinearity20261025a
open ActualPoincareMaassLocalFinite20261025a Gamma0CompactTensorPoincareC2Core20261025a
open MaassWeakOperatorCore20261024zz

private theorem deriv_real_affine (f : ℝ → ℂ) (a b x : ℝ) :
    deriv (fun t => f (a*t+b)) x = a • deriv f (a*x+b) := by
  have h := deriv_comp_mul_left a (fun t => f (t+b)) x
  simpa only [deriv_comp_add_const] using h

private theorem second_deriv_real_affine (f : ℝ → ℂ) (a b x : ℝ) :
    deriv (deriv (fun t => f (a*t+b))) x = a^2 • deriv (deriv f) (a*x+b) := by
  have heq : deriv (fun t => f (a*t+b)) = fun t => a • deriv f (a*t+b) :=
    funext (fun t => deriv_real_affine f a b t)
  rw [heq,deriv_fun_const_smul_field,deriv_real_affine]
  simp only [smul_smul,pow_two]

/-- Exact covariance of the EXISTING native chartMaass for a real affine
branch. It holds even under total-derivative conventions. -/
theorem chartMaass_real_affine (u : ℝ × ℝ → ℂ) (a b : ℝ) (z : ℝ × ℝ) :
    chartMaass (u ∘ affineBranch a b) z = chartMaass u (affineBranch a b z) := by
  have hA : affineBranch a b = fun q : ℝ × ℝ => (a*q.1+b,a*q.2) := by
    funext q
    ext <;> simp [affineBranch]
  rw [hA]
  change -((z.2 : ℂ)^2 *
      (deriv (deriv (fun t : ℝ => u (a*t+b,a*z.2))) z.1 +
        deriv (deriv (fun t : ℝ => u (a*z.1+b,a*t))) z.2)) =
    -(((a*z.2 : ℝ) : ℂ)^2 *
      (deriv (deriv (fun t : ℝ => u (t,a*z.2))) (a*z.1+b) +
        deriv (deriv (fun t : ℝ => u (a*z.1+b,t))) (a*z.2)))
  rw [second_deriv_real_affine (fun t => u (t,a*z.2)) a b z.1]
  have hy := second_deriv_real_affine (fun t => u (a*z.1+b,t)) a 0 z.2
  simp only [add_zero] at hy
  rw [hy]
  simp only [Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_mul,mul_pow]
  ring

/-- Actual inverse normalized REAL branch covariance, through its native
positive-chart germ; no integral-matrix surrogate is substituted. -/
theorem upperMaass_inverse_branch (p : ℕ) (hp : p.Prime) (f : ℍ → ℂ) (j : Branch p) (z : ℍ) :
    upperMaass (fun w => f ((branchSL p hp.pos j)⁻¹ • w)) z =
      upperMaass f ((branchSL p hp.pos j)⁻¹ • z) := by
  have hopen : IsOpen positiveChart := isOpen_lt continuous_const continuous_snd
  have heq : extendUpper (fun w => f ((branchSL p hp.pos j)⁻¹ • w)) =ᶠ[𝓝 (z.re,z.im)]
      (extendUpper f ∘ affineBranch (dualBranchScale p j) (dualBranchShift p j)) := by
    filter_upwards [hopen.mem_nhds z.im_pos] with q hq
    exact extendUpper_inverse_branch p hp f j hq
  change chartMaass (extendUpper (fun w => f ((branchSL p hp.pos j)⁻¹ • w))) (z.re,z.im) = _
  rw [chartMaass_eq_of_eventuallyEq heq,chartMaass_real_affine,← inverse_branch_chart p hp j z]
  rfl

private theorem extendUpper_finite_sum {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ) :
    extendUpper (fun z => ∑ i ∈ s,f i z) = fun q => ∑ i ∈ s,extendUpper (f i) q := by
  funext q
  by_cases hq : 0 < q.2 <;> simp [extendUpper,hq]

/-- The actual finite dual seed has exactly the ORIGINAL transformed
Maass output, not an unnamed differential satisfying an eigen-equation. -/
theorem dualHeckeSeed_upperMaass (p : ℕ) (hp : p.Prime) (f : ℍ → ℂ)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    upperMaass (dualHeckeSeed p hp f) = dualHeckeSeed p hp (upperMaass f) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let G : Branch p → ℍ → ℂ := fun j z => f ((branchSL p hp.pos j)⁻¹ • z)
  have hG (j : Branch p) : ContDiffOn ℝ 2 (extendUpper (G j)) positiveChart :=
    (inverse_branch_nativeCinfty p hp f hf j).of_le (by simp)
  change upperMaass ((Real.sqrt (p : ℝ) : ℂ)⁻¹ • (fun z => ∑ j : Branch p,G j z)) = _
  rw [upperMaass_smul]
  funext z
  change (Real.sqrt (p : ℝ) : ℂ)⁻¹ • upperMaass (fun z => ∑ j : Branch p,G j z) z =
    (Real.sqrt (p : ℝ) : ℂ)⁻¹ • ∑ j : Branch p,upperMaass f ((branchSL p hp.pos j)⁻¹ • z)
  congr 1
  change chartMaass (extendUpper (fun z => ∑ j : Branch p,G j z)) (z.re,z.im) = _
  rw [extendUpper_finite_sum,chartMaass_finsetSum Finset.univ (fun j => extendUpper (G j))
    (fun j hj => hG j) z.im_pos]
  apply Finset.sum_congr rfl
  intro j hj
  exact upperMaass_inverse_branch p hp f j z

end
end ImbalancedChen.Part3.ActualDualHeckeSeedMaass20261026b

