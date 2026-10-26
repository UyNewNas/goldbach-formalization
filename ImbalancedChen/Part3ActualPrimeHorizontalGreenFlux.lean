import ImbalancedChen.Part3PrimeExplicitCosetGreenTrace
import ImbalancedChen.Part3ActualFrickeQuotientMeasure
import ImbalancedChen.Part3ActualEisensteinFourierInterchange

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The genuine completed all-level infinity and normalized Fricke Green
fluxes are continuous period-one horizontal densities. Smoothness of
the REAL Fricke pullback is obtained from the native analytic Mobius
action. Its Gamma0 invariance is derived from the actual normalizer
identity. Actual integral translation/partition can therefore use these
densities without presuming their continuity, period, or flux identities.
The positively oriented TOP tangent is -1, giving the shared +Jy sign.
No quotient Stokes, held side cancellation, or spectral normalization is used.
-/

noncomputable section
open Complex MeasureTheory
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.PrimeExplicitCosetGreenTrace20261026b
open ImbalancedChen.Part3.SLRealGreenCurrent20261026b
open ImbalancedChen.Part3.Gamma0PairedEdgeGreen20261026b
open ImbalancedChen.Part3.Gamma0FiniteCosetGreenTrace20261026b
open ImbalancedChen.Part3.ActualCompletedGamma0Sides20261026b
open ImbalancedChen.Part3.ActualFrickeQuotientMeasure20261026b
open ImbalancedChen.Part3.ActualEisensteinFourierInterchange20261025a
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
open ImbalancedChen.Part3.FrickeNormalizer

namespace ImbalancedChen.Part3.ActualPrimeHorizontalGreenFlux20261026b

theorem slMap_contDiffAt_real (g : SL(2, ℝ)) (z : UpperHalfPlane) :
    ContDiffAt ℝ ∞ (slMap g) (z : ℂ) := by
  have hd : 0 < (realGL g).val.det := by simp [realGL]
  exact (UpperHalfPlane.analyticAt_smul hd z).contDiffAt.restrict_scalars ℝ

theorem frickeField_contDiffAt (N : ℕ) (hN : 0 < N) (F : ℂ → ℂ)
    (hF : ∀ z : UpperHalfPlane, ContDiffAt ℝ ∞ F (z : ℂ)) (z : UpperHalfPlane) :
    ContDiffAt ℝ ∞ (frickeField N hN F) (z : ℂ) := by
  have hFm : ContDiffAt ℝ ∞ F (slMap (frickeSL N hN) z) := by
    simpa only [slMap_eq_action] using hF (frickeSL N hN • z)
  exact hFm.comp (z : ℂ) (slMap_contDiffAt_real (frickeSL N hN) z)

/-- Normalizer geometry proves the period of the ACTUAL Fricke channel. -/
theorem frickeField_Gamma0_invariant (N : ℕ) (hN : 0 < N) (F : ℂ → ℂ)
    (hFI : ∀ δ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      F ((δ • z : UpperHalfPlane) : ℂ) = F z)
    (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    frickeField N hN F ((γ • z : UpperHalfPlane) : ℂ) = frickeField N hN F z := by
  simp only [frickeField, slMap_eq_action]
  rw [fricke_commute_deck N hN γ z]
  exact hFI (frickeGamma0 N γ) (frickeSL N hN • z)

theorem horizontalPoint_coe_affine (y : ℝ) (hy : 0 < y) (x : ℝ) :
    (horizontalPoint y hy x : ℂ) = (x : ℂ) + (y : ℂ) * I := by
  ext <;> simp [horizontalPoint]

theorem horizontalPoint_hasDerivAt (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun r : ℝ => (horizontalPoint y hy r : ℂ)) 1 x := by
  simp_rw [horizontalPoint_coe_affine]
  simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * I)

theorem horizontalPoint_contDiff (y : ℝ) (hy : 0 < y) :
    ContDiff ℝ 1 (fun r : ℝ => (horizontalPoint y hy r : ℂ)) := by
  simp_rw [horizontalPoint_coe_affine]
  fun_prop

theorem horizontalPoint_translation (y : ℝ) (hy : 0 < y) (x : ℝ) :
    horizontalPoint y hy (x + 1) = ModularGroup.T ^ (1 : ℤ) • horizontalPoint y hy x := by
  apply UpperHalfPlane.ext
  rw [ModularGroup.coe_T_zpow_smul_eq]
  ext <;> simp [horizontalPoint] <;> ring

def horizontalGreenDensity (F G : ℂ → ℂ) (y : ℝ) (hy : 0 < y) (x : ℝ) : ℂ :=
  greenOneForm F G (horizontalPoint y hy x) (-1)

/-- TOP outward flux is +Jy, matching the original Green-current convention. -/
theorem horizontalGreenDensity_eq_verticalCurrent (F G : ℂ → ℂ)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    horizontalGreenDensity F G y hy x =
      conj (F (horizontalPoint y hy x)) * fderiv ℝ G (horizontalPoint y hy x) I -
        conj (fderiv ℝ F (horizontalPoint y hy x) I) * G (horizontalPoint y hy x) := by
  unfold horizontalGreenDensity greenOneForm
  rw [show -I * (-1 : ℂ) = I by ring]

theorem horizontalGreenDensity_continuous (F G : ℂ → ℂ)
    (hF : ∀ z : UpperHalfPlane, ContDiffAt ℝ ∞ F (z : ℂ))
    (hG : ∀ z : UpperHalfPlane, ContDiffAt ℝ ∞ G (z : ℂ))
    (y : ℝ) (hy : 0 < y) : Continuous (horizontalGreenDensity F G y hy) := by
  have h := greenOneForm_edge_continuous F G hF hG (horizontalPoint y hy)
    (horizontalPoint_contDiff y hy)
  simp_rw [(horizontalPoint_hasDerivAt y hy _).deriv] at h
  simpa only [horizontalGreenDensity, greenOneForm_neg_tangent] using h.neg

/-- Periodicity of the current follows from genuine field automorphy and
the produced derivative transport; periodicity of a derivative is not assumed. -/
theorem horizontalGreenDensity_periodic (N : ℕ) (F G : ℂ → ℂ)
    (hF : ∀ z : UpperHalfPlane, DifferentiableAt ℝ F (z : ℂ))
    (hG : ∀ z : UpperHalfPlane, DifferentiableAt ℝ G (z : ℂ))
    (hFI : ∀ δ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      F ((δ • z : UpperHalfPlane) : ℂ) = F z)
    (hGI : ∀ δ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      G ((δ • z : UpperHalfPlane) : ℂ) = G z)
    (y : ℝ) (hy : 0 < y) : Function.Periodic (horizontalGreenDensity F G y hy) 1 := by
  let γ : CongruenceSubgroup.Gamma0 N :=
    ⟨ModularGroup.T ^ (1 : ℤ), translation_mem_gamma0 N 1⟩
  intro x
  unfold horizontalGreenDensity
  rw [horizontalPoint_translation]
  have h := greenOneForm_gamma0_transport N γ F G hF hG hFI hGI
    (horizontalPoint y hy x) (-1)
  simpa only [γ, zpow_one, slFactor_T, one_mul] using h

/-- Real tangent linearity retains the literal affine 1/p Jacobian. -/
theorem greenOneForm_real_smul (F G : ℂ → ℂ) (z v : ℂ) (a : ℝ) :
    greenOneForm F G z (a • v) = a • greenOneForm F G z v := by
  unfold greenOneForm
  rw [show -I * (a • v) = a • (-I * v) by simp [Complex.real_smul]; ring]
  simp only [map_smul, Complex.real_smul, map_mul, conj_ofReal]
  ring

def actualInfinityGreenDensity (N : ℕ) (s u : ℂ) (y : ℝ) (hy : 0 < y) : ℝ → ℂ :=
  horizontalGreenDensity (completedComplexField N s) (completedComplexField N u) y hy

def actualFrickeGreenDensity (N : ℕ) (hN : 0 < N) (s u : ℂ)
    (y : ℝ) (hy : 0 < y) : ℝ → ℂ :=
  horizontalGreenDensity (frickeField N hN (completedComplexField N s))
    (frickeField N hN (completedComplexField N u)) y hy

def actualInfinityGreenFlux (N : ℕ) (s u : ℂ) (y : ℝ) (hy : 0 < y) : ℂ :=
  ∫ x in (-(1 / 2) : ℝ)..(1 / 2), actualInfinityGreenDensity N s u y hy x

def actualFrickeGreenFlux (N : ℕ) (hN : 0 < N) (s u : ℂ) (y : ℝ) (hy : 0 < y) : ℂ :=
  ∫ x in (-(1 / 2) : ℝ)..(1 / 2), actualFrickeGreenDensity N hN s u y hy x

theorem actualInfinityGreenDensity_continuous (N : ℕ) (s u : ℂ) (y : ℝ) (hy : 0 < y) :
    Continuous (actualInfinityGreenDensity N s u y hy) :=
  horizontalGreenDensity_continuous _ _
    (completedComplexField_contDiffAt N s) (completedComplexField_contDiffAt N u) y hy

theorem actualFrickeGreenDensity_continuous (N : ℕ) (hN : 0 < N)
    (s u : ℂ) (y : ℝ) (hy : 0 < y) :
    Continuous (actualFrickeGreenDensity N hN s u y hy) :=
  horizontalGreenDensity_continuous _ _
    (frickeField_contDiffAt N hN _ (completedComplexField_contDiffAt N s))
    (frickeField_contDiffAt N hN _ (completedComplexField_contDiffAt N u)) y hy

theorem actualInfinityGreenDensity_periodic (N : ℕ) (hN : 0 < N) (s u : ℂ)
    (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    (y : ℝ) (hy : 0 < y) : Function.Periodic (actualInfinityGreenDensity N s u y hy) 1 :=
  horizontalGreenDensity_periodic N _ _
    (fun z => (completedComplexField_contDiffAt N s z).differentiableAt (by simp))
    (fun z => (completedComplexField_contDiffAt N u z).differentiableAt (by simp))
    (completedComplexField_Gamma0_invariant N hN s hs)
    (completedComplexField_Gamma0_invariant N hN u hu) y hy

theorem actualFrickeGreenDensity_periodic (N : ℕ) (hN : 0 < N) (s u : ℂ)
    (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    (y : ℝ) (hy : 0 < y) : Function.Periodic (actualFrickeGreenDensity N hN s u y hy) 1 :=
  horizontalGreenDensity_periodic N _ _
    (fun z => frickeField_differentiableAt N hN _
      (fun w => (completedComplexField_contDiffAt N s w).differentiableAt (by simp)) z)
    (fun z => frickeField_differentiableAt N hN _
      (fun w => (completedComplexField_contDiffAt N u w).differentiableAt (by simp)) z)
    (frickeField_Gamma0_invariant N hN _ (completedComplexField_Gamma0_invariant N hN s hs))
    (frickeField_Gamma0_invariant N hN _ (completedComplexField_Gamma0_invariant N hN u hu)) y hy

theorem actualInfinityGreenDensity_intervalIntegrable (N : ℕ) (s u : ℂ)
    (y : ℝ) (hy : 0 < y) (a b : ℝ) :
    IntervalIntegrable (actualInfinityGreenDensity N s u y hy) volume a b :=
  (actualInfinityGreenDensity_continuous N s u y hy).intervalIntegrable a b

theorem actualFrickeGreenDensity_intervalIntegrable (N : ℕ) (hN : 0 < N)
    (s u : ℂ) (y : ℝ) (hy : 0 < y) (a b : ℝ) :
    IntervalIntegrable (actualFrickeGreenDensity N hN s u y hy) volume a b :=
  (actualFrickeGreenDensity_continuous N hN s u y hy).intervalIntegrable a b

end ImbalancedChen.Part3.ActualPrimeHorizontalGreenFlux20261026b
