import ImbalancedChen.Part3ActualMobiusMaassEquivariance
import ImbalancedChen.Part3ActualPoincareMaassLocalFinite
import ImbalancedChen.Part3Gamma0QuotientCellPushforward

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

For ANY actual Gamma0-invariant H-function whose positive coordinate chart
is C2, the EXISTING upperMaass is proved Gamma0-invariant. The proof uses
the proved arbitrary-C2 actual Mobius chart chain and chart germ locality;
no Laplacian invariance or periodized-Delta identity is a premise.

Both the original function and its actual differential descend to the
actual Gamma0 orbit quotient. The latter has exactly upperMaass F as its
representative pullback. No Hilbert graph closure or spectral assertion is
made by this representative-level differential construction.
-/

namespace ImbalancedChen.Part3.ActualGamma0MaassDescent20261025a

noncomputable section
open Filter Topology Set
open scoped UpperHalfPlane MatrixGroups BigOperators
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.ActualMobiusMaassEquivariance20261025a
open ImbalancedChen.Part3.ActualPoincareMaassLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a

theorem extendUpper_pair (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    extendUpper F (z.re, z.im) = F z := by
  rw [extendUpper, dif_pos z.im_pos]
  rfl

theorem extendUpper_chartLift (F : UpperHalfPlane → ℂ)
    (p : ℝ × ℝ) (hp : 0 < p.2) : extendUpper F p = F (chartLift p) := by
  rw [extendUpper, dif_pos hp, chartLift_of_positive hp]
  rfl

theorem extendUpper_mobiusChart (F : UpperHalfPlane → ℂ)
    (g : SL(2, ℤ)) (p : ℝ × ℝ) (hp : 0 < p.2) :
    extendUpper F (mobiusChart g p) = F (g • chartLift p) := by
  rw [mobiusChart_eq_actual g hp]
  exact extendUpper_pair F (g • chartLift p)

theorem chartLift_pair (z : UpperHalfPlane) : chartLift (z.re, z.im) = z := by
  rw [chartLift_of_positive z.im_pos]
  rfl

private theorem positiveChart_isOpen : IsOpen positiveChart :=
  isOpen_lt continuous_const continuous_snd

/-- The input invariance is transported through the actual positive chart
on a genuine neighborhood; the zero extension below y=0 is irrelevant. -/
theorem invariant_mobius_chart_germ
    (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hInv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    (γ : CongruenceSubgroup.Gamma0 N) (p : ℝ × ℝ) (hp : 0 < p.2) :
    (fun q => extendUpper F (mobiusChart (γ : SL(2, ℤ)) q)) =ᶠ[𝓝 p] extendUpper F := by
  filter_upwards [positiveChart_isOpen.mem_nhds hp] with q hq
  rw [extendUpper_mobiusChart F (γ : SL(2, ℤ)) q hq, extendUpper_chartLift F q hq]
  exact hInv γ (chartLift q)

/-- Actual Gamma0 invariance of the existing hyperbolic differential for
an arbitrary invariant C2 positive-chart function. No output invariance
is assumed; it is derived from the genuine Mobius second-chain theorem. -/
theorem upperMaass_gamma0_invariant
    (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hInv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    upperMaass F (γ • z) = upperMaass F z := by
  let p : ℝ × ℝ := (z.re, z.im)
  have hp : 0 < p.2 := z.im_pos
  have hqp : mobiusChart (γ : SL(2, ℤ)) p = ((γ • z).re, (γ • z).im) := by
    rw [mobiusChart_eq_actual (γ : SL(2, ℤ)) hp, chartLift_pair]
  have hq : 0 < (mobiusChart (γ : SL(2, ℤ)) p).2 := by
    rw [hqp]
    exact (γ • z).im_pos
  have hFq : ContDiffAt ℝ 2 (extendUpper F) (mobiusChart (γ : SL(2, ℤ)) p) :=
    (hF _ hq).contDiffAt (positiveChart_isOpen.mem_nhds hq)
  have hgeom := chartMaass_comp_gamma0 N γ (extendUpper F) p hp hFq
  have hlocal := chartMaass_eq_of_eventuallyEq (invariant_mobius_chart_germ N F hInv γ p hp)
  change chartMaass (extendUpper F) ((γ • z).re, (γ • z).im) =
    chartMaass (extendUpper F) (z.re, z.im)
  rw [← hqp]
  exact hgeom.symm.trans hlocal

/-- The true orbit-quotient function for an arbitrary invariant input. -/
def quotientInvariantFunction (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hInv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z) :
    Gamma0OrbitSpace N → ℂ :=
  Quotient.lift F (by
    intro z w hzw
    obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp hzw
    rw [← hγ]
    exact hInv γ w)

/-- Actual differential descent; invariance of upperMaass F is proved
above, never accepted as a separate differential-invariance supplier. -/
def quotientMaass (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hInv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z) :
    Gamma0OrbitSpace N → ℂ :=
  Quotient.lift (upperMaass F) (by
    intro z w hzw
    obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp hzw
    rw [← hγ]
    exact upperMaass_gamma0_invariant N F hF hInv γ w)

@[simp] theorem quotientInvariantFunction_projection
    (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hInv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    (z : UpperHalfPlane) :
    quotientInvariantFunction N F hInv (orbitProjection N z) = F z := rfl

@[simp] theorem quotientMaass_projection
    (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hInv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    (z : UpperHalfPlane) :
    quotientMaass N F hF hInv (orbitProjection N z) = upperMaass F z := rfl

theorem upperMaass_eq_of_same_orbit
    (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hInv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    (z w : UpperHalfPlane) (hzw : orbitProjection N z = orbitProjection N w) :
    upperMaass F z = upperMaass F w :=
  congrArg (quotientMaass N F hF hInv) hzw

/-- The representative-level differential does not depend on selected
proofs of the input's smoothness or invariance. -/
theorem quotientMaass_proof_independent
    (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hF₁ hF₂ : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hInv₁ hInv₂ : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z) :
    quotientMaass N F hF₁ hInv₁ = quotientMaass N F hF₂ hInv₂ := by
  funext q
  exact Quotient.inductionOn q (fun z => rfl)

/-- Finite actual smooth sums have their actual sum differential. -/
theorem upperMaass_finsetSum {ι : Type*} (s : Finset ι)
    (F : ι → UpperHalfPlane → ℂ)
    (hF : ∀ i ∈ s, ContDiffOn ℝ 2 (extendUpper (F i)) positiveChart)
    (z : UpperHalfPlane) :
    upperMaass (fun w => ∑ i ∈ s, F i w) z = ∑ i ∈ s, upperMaass (F i) z := by
  have hext : extendUpper (fun w => ∑ i ∈ s, F i w) =
      (fun p => ∑ i ∈ s, extendUpper (F i) p) := by
    funext p
    by_cases hp : 0 < p.2
    · simp only [extendUpper, dif_pos hp]
    · simp only [extendUpper, dif_neg hp, Finset.sum_const_zero]
  unfold upperMaass
  rw [hext, chartMaass_finsetSum s (fun i => extendUpper (F i)) hF z.im_pos]

/-- Arbitrary finite linear combinations of actual invariant smooth
representatives have invariant actual differential. Scalars and all row
choices are fixed only as genuine input data. -/
theorem upperMaass_finite_combination_gamma0_invariant {ι : Type*}
    (N : ℕ) (s : Finset ι) (a : ι → ℂ) (F : ι → UpperHalfPlane → ℂ)
    (hF : ∀ i ∈ s, ContDiffOn ℝ 2 (extendUpper (F i)) positiveChart)
    (hInv : ∀ i ∈ s, ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      F i (γ • z) = F i z)
    (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    upperMaass (fun w => ∑ i ∈ s, a i * F i w) (γ • z) =
      upperMaass (fun w => ∑ i ∈ s, a i * F i w) z := by
  apply upperMaass_gamma0_invariant N
  · have hext : extendUpper (fun w => ∑ i ∈ s, a i * F i w) =
        (fun p => ∑ i ∈ s, a i * extendUpper (F i) p) := by
      funext p
      by_cases hp : 0 < p.2
      · simp only [extendUpper, dif_pos hp]
      · simp only [extendUpper, dif_neg hp, mul_zero, Finset.sum_const_zero]
    rw [hext]
    apply ContDiffOn.sum
    intro i hi
    exact contDiffOn_const.mul (hF i hi)
  · intro γ' w
    apply Finset.sum_congr rfl
    intro i hi
    rw [hInv i hi γ' w]

end
end ImbalancedChen.Part3.ActualGamma0MaassDescent20261025a
