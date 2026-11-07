import ImbalancedChen.Part3ActualRadialFriedrichsSmoothExtension
import ImbalancedChen.Part3GeneralActualRadialGreen
import ImbalancedChen.Part3OneCompactCrossGreen

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The literal imaginary-order K transform of a compact smooth radial test
intertwines every iterate of the actual logarithmic Schrödinger expression
H=-d²/dr²+exp(2r) with multiplication by tau². Smoothness, compact support,
support containment and all integral convergence are proved on the actual
functions. This is integration by parts, not Plancherel or rapid-decay input.
-/

namespace ImbalancedChen.Part3.ActualKLCompactTestIntegrationByParts20261025a

noncomputable section
open Set MeasureTheory Filter
open RadialSchrodingerL2Form20261025a ActualKRadialLogConjugation20261025a
open GeneralActualRadialGreenSourceOnly ComplexOrderKRadialRegularitySourceOnly
open ComplexCompactGreenGluingSourceOnly OneCompactCrossGreen20261025a

/-- The order parameter is tau itself, so the kernel is K_{i tau}. -/
def actualKtransform (f : ℝ → ℂ) (tau : ℝ) : ℂ :=
  ∫ r : ℝ, f r * radialK ((tau : ℂ) * Complex.I) r

theorem actualKtransform_integrable (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (tau : ℝ) :
    Integrable (fun r : ℝ => f r * radialK ((tau : ℂ) * Complex.I) r) :=
  (hf.mul (radialK_C2 _).continuous).integrable_of_hasCompactSupport hc.mul_right

theorem logSchrodinger_radialK_imaginary (tau r : ℝ) :
    logSchrodinger (radialK ((tau : ℂ) * Complex.I)) r =
      (tau : ℂ)^2 * radialK ((tau : ℂ) * Complex.I) r := by
  have h := actual_radialK_homogeneous ((tau : ℂ) * Complex.I) r
  unfold operator potential at h
  simp only [mul_pow, Complex.I_sq, mul_neg, mul_one] at h
  simp only [logSchrodinger, Complex.real_smul]
  linear_combination h

/-- Lift the already defined actual differential expression back to the
same compact smooth RadialTest type. -/
def hamiltonianTest (T : RadialTest) : RadialTest where
  function := radialOperatorFunction T
  smooth := by
    have hd : ContDiff ℝ ∞ (deriv T.function) :=
      (contDiff_infty_iff_deriv.mp T.smooth).2
    have hdd : ContDiff ℝ ∞ (deriv (deriv T.function)) :=
      (contDiff_infty_iff_deriv.mp hd).2
    have he : ContDiff ℝ ∞ (fun r : ℝ => Real.exp (2*r)) := by fun_prop
    exact hdd.neg.add (he.smul T.smooth)
  compact := by
    exact T.compact.deriv.deriv.neg.add T.compact.smul_left

theorem hamiltonianTest_function (T : RadialTest) :
    (hamiltonianTest T).function = logSchrodinger T.function := rfl

/-- Applying H can shrink the topological support, but never enlarges it. -/
theorem hamiltonianTest_support_subset (T : RadialTest) :
    tsupport (hamiltonianTest T).function ⊆ tsupport T.function := by
  change closure (Function.support (hamiltonianTest T).function) ⊆ tsupport T.function
  apply closure_minimal ?_ isClosed_tsupport
  intro r hr
  by_contra hout
  have hf : T.function r = 0 := image_eq_zero_of_notMem_tsupport hout
  have hdd : deriv (deriv T.function) r = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hout (tsupport_deriv_subset (tsupport_deriv_subset h)))
  have hzero : (hamiltonianTest T).function r = 0 := by
    simp only [hamiltonianTest_function, logSchrodinger, hdd, hf, neg_zero,
      smul_zero, add_zero]
  exact hr hzero

def hamiltonianIterate : ℕ → RadialTest → RadialTest
  | 0, T => T
  | m+1, T => hamiltonianTest (hamiltonianIterate m T)

theorem hamiltonianIterate_support_subset (m : ℕ) (T : RadialTest) :
    tsupport (hamiltonianIterate m T).function ⊆ tsupport T.function := by
  induction m with
  | zero => exact Subset.rfl
  | succ m ih => exact (hamiltonianTest_support_subset _).trans ih

private theorem secondDeriv_transfer_one_compact (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport f) :
    (∫ r : ℝ, f r * (-deriv (deriv g) r)) =
      ∫ r : ℝ, (-deriv (deriv f) r) * g r := by
  have hs : ContDiff ℝ 2 (fun r : ℝ => star (f r)) := hf.star
  have hcs : HasCompactSupport (fun r : ℝ => star (f r)) :=
    hc.comp_left (g := star) (by simp)
  have h := one_compact_green_symmetry (fun r : ℝ => star (f r)) g hs hg hcs
  simpa only [star_star, deriv.star', deriv.star, star_neg] using h

/-- Exact one-step transform identity. The noncompact K branch has no
artificial boundary condition: compactness of the test pays both boundaries. -/
theorem actualKtransform_hamiltonian (T : RadialTest) (tau : ℝ) :
    actualKtransform (hamiltonianTest T).function tau =
      (tau : ℂ)^2 * actualKtransform T.function tau := by
  let g := radialK ((tau : ℂ) * Complex.I)
  have hf2 : ContDiff ℝ 2 T.function := T.smooth.of_le (by simp)
  have hg2 : ContDiff ℝ 2 g := radialK_C2 _
  have hD := secondDeriv_transfer_one_compact T.function g hf2 hg2 T.compact
  have hd := (contDiff_infty_iff_deriv.mp T.smooth).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2.continuous
  have hiD : Integrable (fun r : ℝ => (-deriv (deriv T.function) r) * g r) :=
    (hdd.neg.mul hg2.continuous).integrable_of_hasCompactSupport
      T.compact.deriv.deriv.neg.mul_right
  have hiE : Integrable (fun r : ℝ =>
      ((Real.exp (2*r) : ℂ) * T.function r) * g r) :=
    (((Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
        T.smooth.continuous).mul hg2.continuous).integrable_of_hasCompactSupport
          T.compact.mul_left.mul_right
  have hiD' : Integrable (fun r : ℝ => T.function r * (-deriv (deriv g) r)) := by
    have hgs : ContDiff ℝ ((1 : ℕ∞ω)+1) g := by simpa using hg2
    have hgdd := (contDiff_succ_iff_deriv.mp hgs).2.2.continuous_deriv_one
    exact (T.smooth.continuous.mul hgdd.neg).integrable_of_hasCompactSupport T.compact.mul_right
  have hiE' : Integrable (fun r : ℝ => T.function r *
      ((Real.exp (2*r) : ℂ) * g r)) := by
    convert hiE using 1
    funext r
    ring
  calc
    actualKtransform (hamiltonianTest T).function tau =
        (∫ r : ℝ, (-deriv (deriv T.function) r) * g r) +
          (∫ r : ℝ, ((Real.exp (2*r) : ℂ) * T.function r) * g r) := by
      unfold actualKtransform
      simp only [hamiltonianTest_function, logSchrodinger, Complex.real_smul, add_mul]
      exact integral_add hiD hiE
    _ = (∫ r : ℝ, T.function r * (-deriv (deriv g) r)) +
          (∫ r : ℝ, T.function r * ((Real.exp (2*r) : ℂ) * g r)) := by
      rw [hD]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun r => by ring
    _ = ∫ r : ℝ, T.function r * logSchrodinger g r := by
      rw [← integral_add hiD' hiE']
      apply integral_congr_ae
      exact Eventually.of_forall fun r => by simp only [logSchrodinger, Complex.real_smul]; ring
    _ = (tau : ℂ)^2 * actualKtransform T.function tau := by
      simp_rw [show ∀ r, logSchrodinger g r = (tau : ℂ)^2 * g r from
        logSchrodinger_radialK_imaginary tau]
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun r => by ring

/-- Every power gain is proved by iteration of the actual compact Green
identity. No rapid transform-decay estimate occurs among the hypotheses. -/
theorem actualKtransform_iterated_hamiltonian (m : ℕ) (T : RadialTest) (tau : ℝ) :
    (tau : ℂ)^(2*m) * actualKtransform T.function tau =
      actualKtransform (hamiltonianIterate m T).function tau := by
  induction m with
  | zero => simp only [hamiltonianIterate, mul_zero, pow_zero, one_mul]
  | succ m ih =>
      rw [hamiltonianIterate, actualKtransform_hamiltonian, ← ih,
        show 2*(m+1)=2*m+2 by omega, pow_add]
      ring

end
end ImbalancedChen.Part3.ActualKLCompactTestIntegrationByParts20261025a
