import ImbalancedChen.Part3ActualCuspEigenbasisNativeLabels
import ImbalancedChen.Part3UniformNormalizedEigenFrameClassicalBound

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT / READY_FALSE.
Inherited d1e/b8d be3646/0f1f and eigen-regularity DOTS API holds are retained.

ONE chosen family of genuine smooth Gamma profiles represents the ORIGINAL
actual cuspidal Hilbert basis. Normalization is the original quotient/carrier
L2 normalization; no global H-volume L2 assertion is made. Compact ordinary
mixed-jet constants are chosen before the basis index and grow as
(1+lambda_i)^(k+2), using the already proved uniform compact estimate.
No basis, smooth eigenprofile, or derivative bound is assumed as a parameter.
-/

namespace ImbalancedChen.Part3.ActualCuspSmoothEigenprofileFamily20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups UpperHalfPlane Topology ContDiff
open ActualFullCuspEigenbasis20261026b ActualCuspEigenbasisNativeLabels20261026b
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open GammaActualEigenSmoothRepresentative20261026b UniformNormalizedEigenFrameClassicalBound20261026b
open Gamma0QuotientCellPushforward20261025a Gamma0FiniteMeasureCarrier20261024z
open MaassWeakOperatorCore20261024zz CanonicalTensorHyperbolicLaplacianForm20261024z
open ActualEigenNormalizedSmoothFrame20261026b NormalizedCuspCompactQuotientLp20261026b
open Gamma0GeneralCuspUnitPeriod20261025a Gamma0GeneralCuspWidth20261025a
open Gamma0CompactTensorPoincareC2Core20261025a PlanarWeakDifferentialMultiindex20261026b
open QuantitativeLocalClassicalJetEstimate20261026b

private theorem actualCuspProfile_exists (N : ℕ) [NeZero N] (hN : 0 < N)
    (i : actualCuspBasisIndex N hN) :
    ∃ Phi : UpperHalfPlane → ℂ,
      ContDiffOn ℝ ∞ (extendUpper Phi) upperChart ∧
      (Phi =ᵐ[(volume : Measure UpperHalfPlane)] fun z =>
        (actualCuspHilbertBasis N hN i : QuotientL2 N) (orbitProjection N z)) ∧
      GammaSmoothMultiplierPeriodization20261026a.IsGammaInvariant N Phi ∧
      (∀ z, upperMaass Phi z = (actualCuspNativeEigenvalue N hN i : ℂ) * Phi z) :=
  actual_native_eigen_has_smooth_upper_representative N (actualCuspNativeEigenvalue N hN i)
    (actualCuspHilbertBasis N hN i : QuotientL2 N)
    (actualCuspHilbertBasis_original_maass_graph N hN i)

def actualCuspSmoothProfile (N : ℕ) [NeZero N] (hN : 0 < N)
    (i : actualCuspBasisIndex N hN) : UpperHalfPlane → ℂ :=
  Classical.choose (actualCuspProfile_exists N hN i)

def actualCuspPlanarProfile (N : ℕ) [NeZero N] (hN : 0 < N)
    (i : actualCuspBasisIndex N hN) : ℝ × ℝ → ℂ :=
  extendUpper (actualCuspSmoothProfile N hN i)

theorem actualCuspSmoothProfile_spec (N : ℕ) [NeZero N] (hN : 0 < N)
    (i : actualCuspBasisIndex N hN) :
    ContDiffOn ℝ ∞ (actualCuspPlanarProfile N hN i) upperChart ∧
      (actualCuspSmoothProfile N hN i =ᵐ[(volume : Measure UpperHalfPlane)] fun z =>
        (actualCuspHilbertBasis N hN i : QuotientL2 N) (orbitProjection N z)) ∧
      GammaSmoothMultiplierPeriodization20261026a.IsGammaInvariant N (actualCuspSmoothProfile N hN i) ∧
      (∀ z, upperMaass (actualCuspSmoothProfile N hN i) z =
        (actualCuspNativeEigenvalue N hN i : ℂ) * actualCuspSmoothProfile N hN i z) :=
  Classical.choose_spec (actualCuspProfile_exists N hN i)

theorem actualCuspProfile_native_norm_one (N : ℕ) [NeZero N] (hN : 0 < N)
    (i : actualCuspBasisIndex N hN) :
    ‖(actualCuspHilbertBasis N hN i : QuotientL2 N)‖ = 1 :=
  actualCuspHilbertBasis_norm N hN i

/-- Norm-one is literal mass on the ORIGINAL finite carrier, not on all H. -/
theorem actualCuspSmoothProfile_carrier_mass_one (N : ℕ) [NeZero N] (hN : 0 < N)
    (i : actualCuspBasisIndex N hN) :
    (∫ z in gamma0Carrier N, ‖actualCuspSmoothProfile N hN i z‖ ^ 2) = 1 := by
  let f : QuotientL2 N := (actualCuspHilbertBasis N hN i : QuotientL2 N)
  have hnorm : ‖f‖ ^ 2 = ∫ q, ‖f q‖ ^ 2 ∂carrierPushforward N := by
    have h := L2.inner_def (𝕜 := ℂ) f f
    simp_rw [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] at h
    rw [integral_ofReal] at h
    exact Complex.ofReal_injective h
  have hAE := (actualCuspSmoothProfile_spec N hN i).2.1
  calc
    _ = ∫ z in gamma0Carrier N, ‖f (orbitProjection N z)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hAE] with z hz
      rw [hz]
    _ = ∫ q, ‖f q‖ ^ 2 ∂carrierPushforward N := by
      symm
      change (∫ q, ‖f q‖ ^ 2 ∂Measure.map (orbitProjection N)
        ((volume : Measure UpperHalfPlane).restrict (gamma0Carrier N))) = _
      exact integral_map (orbitProjection_measurable N).aemeasurable
        ((Lp.aestronglyMeasurable f).norm.pow 2)
    _ = ‖f‖ ^ 2 := hnorm.symm
    _ = 1 := by rw [actualCuspProfile_native_norm_one N hN i]; norm_num

private theorem normalizedScaling_identity (N : ℕ) [NeZero N] (hN : 0 < N) :
    normalizedScaling N hN (1 : SL(2, ℤ)) = 1 := by
  apply Subtype.ext
  rw [normalizedScaling_entries, cuspWidth_infinity N hN]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

private theorem smoothFrame_identity_on_upper (N : ℕ) [NeZero N] (hN : 0 < N)
    (Phi : UpperHalfPlane → ℂ) {p : ℝ × ℝ} (hp : p ∈ upperChart) :
    smoothFrame N (1 : SL(2, ℤ)) Phi p = extendUpper Phi p := by
  rw [smoothFrame_at_upper N hN (1 : SL(2, ℤ)) Phi hp]
  change Phi (normalizedScaling N hN (1 : SL(2, ℤ)) • chartLift p) = _
  rw [normalizedScaling_identity N hN, one_smul, chartLift_of_positive hp]
  simp only [extendUpper, dif_pos hp]

/-- All ordinary compact-chart jets share one geometry/order constant fixed
before i. The original norm-one basis normalization removes the L2 factor. -/
theorem exists_uniform_actual_cusp_profile_compact_jet_bound (N : ℕ) [NeZero N] (hN : 0 < N)
    (k : ℕ) (K : Set (ℝ × ℝ)) (hK : IsCompact K) (hKpos : K ⊆ upperChart) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : actualCuspBasisIndex N hN,
      ∀ α : MultiIndex, α.1 + α.2 ≤ k → ∀ p ∈ K,
        ‖testPartial α (actualCuspPlanarProfile N hN i) p‖ ≤
          C * (1 + actualCuspNativeEigenvalue N hN i) ^ (k + 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_normalized_frame_classical_bound
    N hN (1 : SL(2, ℤ)) k K hK hKpos
  refine ⟨C, hC, ?_⟩
  intro i α hα p hp
  obtain ⟨hPhi, hAE, hGamma, hPDE⟩ := actualCuspSmoothProfile_spec N hN i
  have heq : smoothFrame N (1 : SL(2, ℤ)) (actualCuspSmoothProfile N hN i) =ᶠ[𝓝 p]
      actualCuspPlanarProfile N hN i := by
    have hopen : IsOpen upperChart := isOpen_lt continuous_const continuous_snd
    filter_upwards [hopen.mem_nhds (hKpos hp)] with q hq
    exact smoothFrame_identity_on_upper N hN _ hq
  have hjet := testPartial_germ α heq
  rw [← hjet]
  have hb := hbound (actualCuspNativeEigenvalue N hN i)
    (actualCuspHilbertBasis N hN i : QuotientL2 N) (actualCuspSmoothProfile N hN i)
    hPhi hAE hPDE α hα p hp
  simpa only [actualCuspProfile_native_norm_one N hN i, mul_one,
    abs_of_nonneg (actualCuspNativeEigenvalue_nonneg N hN i)] using hb

end
end ImbalancedChen.Part3.ActualCuspSmoothEigenprofileFamily20261026b
