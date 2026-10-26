import ImbalancedChen.Part3GammaCompactOrbitCutoffJets

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Above the explicit compact-carrier plateau threshold, the actual cutoff
square times the original compact seed is the SAME FUNCTION everywhere.
Actual periodization and its native Maass output are consequently exact.
For the original finite smooth Poincare family this gives exact cutoff
tests and exact native Leibniz outputs. No invariant support premise is
needed: compactness is used only on the original seed carrier.
-/

namespace ImbalancedChen.Part3.GammaCompactSeedEventualCutoffExact20261026b

noncomputable section
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactTensorPoincareC2Core20261025a Gamma0SmoothCompactTensorCore20261025a
open Gamma0CompactTensorQuotientL2Core20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open ActualModularSmoothCuspCutoff20261025a ActualModularCutoffMaassBudget20261025a
open GammaSmoothMultiplierPeriodization20261026a GammaSmoothMultiplierLegalTests20261026a
open GammaCompactSeedCutoffPlateau20261026a GammaCompactOrbitCutoffJets20261026b

/-- The seed equality is global: off its support both sides are zero.
The constant germ supplies the value only on its original carrier. -/
theorem cutoff_square_mul_seed_eq
    (f : UpperHalfPlane → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support f ⊆ plateauBand a b)
    (Y : ℝ) (hY : plateauThreshold a b ≤ Y) :
    (complexGlobalH Y * complexGlobalH Y) * f = f := by
  funext z
  by_cases hz : z ∈ Function.support f
  · have hg := globalCutoff_germ_one_on_band a b ha Y hY z (hsupp hz)
    have hone := (complexGlobalH_square_germ_one Y z hg).eq_of_nhds
    change (complexGlobalH Y * complexGlobalH Y) z * f z = f z
    rw [hone,one_mul]
  · have hzero : f z = 0 := not_not.mp hz
    simp only [Pi.mul_apply,hzero,mul_zero]

/-- Differential equality is obtained by congruence of globally equal
functions, not by differentiating an isolated pointwise identity. -/
theorem cutoff_square_seed_differential_eq
    (f : UpperHalfPlane → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support f ⊆ plateauBand a b)
    (Y : ℝ) (hY : plateauThreshold a b ≤ Y) :
    upperMaass ((complexGlobalH Y * complexGlobalH Y) * f) = upperMaass f :=
  congrArg upperMaass (cutoff_square_mul_seed_eq f a b ha hsupp Y hY)

/-- The same Y works for the entire Poincare function, including points
outside the seed carrier. Actual multiplier periodization supplies this. -/
theorem cutoff_square_mul_seedTrace_eq (N : ℕ)
    (f : UpperHalfPlane → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support f ⊆ plateauBand a b)
    (Y : ℝ) (hY : plateauThreshold a b ≤ Y) :
    (complexGlobalH Y * complexGlobalH Y) * complexSeedTrace N f = complexSeedTrace N f := by
  rw [← complexSeedTrace_mul_invariant N _ f (actualCutoff_square_invariant N Y),
    cutoff_square_mul_seed_eq f a b ha hsupp Y hY]

/-- Compactness fixes the explicit threshold before N, Y, point or orbit.
Both the original actual trace and its original differential seed trace
are eventually literally identical to their cutoff-square versions. -/
theorem exists_compact_seed_eventual_exact
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ tsupport f ⊆ plateauBand a b ∧
      ∀ Y : ℝ, plateauThreshold a b ≤ Y →
        (complexGlobalH Y * complexGlobalH Y) * f = f ∧
        upperMaass ((complexGlobalH Y * complexGlobalH Y) * f) = upperMaass f ∧
        ∀ N : ℕ,
          complexSeedTrace N ((complexGlobalH Y * complexGlobalH Y) * f) =
            complexSeedTrace N f ∧
          complexSeedTrace N (upperMaass ((complexGlobalH Y * complexGlobalH Y) * f)) =
            complexSeedTrace N (upperMaass f) ∧
          (complexGlobalH Y * complexGlobalH Y) * complexSeedTrace N f = complexSeedTrace N f := by
  obtain ⟨a,b,ha,hab,hband,_⟩ := exists_compact_seed_plateau_parameters hfc
  have hsupp : Function.support f ⊆ plateauBand a b := (subset_tsupport f).trans hband
  refine ⟨a,b,ha,hab,hband,?_⟩
  intro Y hY
  have heq := cutoff_square_mul_seed_eq f a b ha hsupp Y hY
  have hdiff := congrArg upperMaass heq
  refine ⟨heq,hdiff,?_⟩
  intro N
  exact ⟨congrArg (complexSeedTrace N) heq,congrArg (complexSeedTrace N) hdiff,
    cutoff_square_mul_seedTrace_eq N f a b ha hsupp Y hY⟩

/-- Original finite SmoothCompactTensor Poincare test, with the genuine
native multiplier differential retained until the global equality proves
that every error term cancels. The original family is unchanged. -/
theorem exists_finite_smooth_poincare_eventual_exact
    {ι : Type*} (s : Finset ι) (T : ι → SmoothCompactTensor) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ N : ℕ, ∀ Y : ℝ, plateauThreshold a b ≤ Y →
        (complexGlobalH Y * complexGlobalH Y) * smoothFinitePoincare N s T =
          smoothFinitePoincare N s T ∧
        upperMaass ((complexGlobalH Y * complexGlobalH Y) * smoothFinitePoincare N s T) =
          upperMaass (smoothFinitePoincare N s T) ∧
        multiplierDifferential (complexGlobalH Y * complexGlobalH Y) (smoothFinitePoincare N s T) =
          upperMaass (smoothFinitePoincare N s T) ∧
        quotientMultiplier N (complexGlobalH Y * complexGlobalH Y)
            (actualCutoff_square_invariant N Y) *
          quotientTensorPoincare N s (fun i => (T i).toCompactTensor) =
          quotientTensorPoincare N s (fun i => (T i).toCompactTensor) := by
  let f := finiteCoreFunction s (fun i => (T i).toCompactTensor)
  obtain ⟨hfc,_⟩ := finiteSmoothSeed_compact_cinfty s T
  obtain ⟨a,b,ha,hab,hband,hexact⟩ := exists_compact_seed_eventual_exact f hfc
  refine ⟨a,b,ha,hab,?_⟩
  intro N Y hY
  have hYpos : 0 < Y := (plateauThreshold_pos a b).trans_le hY
  have hmul : (complexGlobalH Y * complexGlobalH Y) * smoothFinitePoincare N s T =
      smoothFinitePoincare N s T := ((hexact Y hY).2.2 N).2.2
  have hdiff := congrArg upperMaass hmul
  refine ⟨hmul,hdiff,?_,?_⟩
  · rw [multiplierDifferential_eq _ _
      ((actualCutoff_square_cinfty Y hYpos).of_le (by simp))
      ((smoothFinitePoincare_contDiffOn_chart N s T).of_le (by simp)),hdiff]
  · funext q
    exact Quotient.inductionOn q (fun z => congrFun hmul z)

end
end ImbalancedChen.Part3.GammaCompactSeedEventualCutoffExact20261026b
