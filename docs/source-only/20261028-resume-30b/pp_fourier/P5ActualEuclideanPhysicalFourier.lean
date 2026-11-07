import ImbalancedChen.P5AllRankMixedFourierPointwise
import ImbalancedChen.P5AllRankCauchyCubeTail
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual Fourier transform below is Mathlib's transform on the
Euclidean inner-product space, not a Fourier instance on the plain Pi
arithmetic chart. The coordinate change is xi=2*pi*nu. We derive its
Jacobian, physical oscillatory integral and inversion; then we apply the
preceding product-Cauchy cube-tail theorem to this actual transform.
No transform identity, Fourier representation or arithmetic conclusion is
assumed. Every result is uniform in the finite occurrence rank, including 0.
-/
namespace ImbalancedChen.P5Z.ActualEuclideanPhysicalFourier
noncomputable section

open MeasureTheory FourierTransform SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap RealInnerProductSpace
open AllRankCoordinateFourierIBP AllRankMixedOperatorBudget
open AllRankMixedFourierPointwise AllRankCauchyKernelIntegral AllRankCauchyCubeTail

/-- Mathlib uses exp(2*pi*i*nu.z); the original paper uses exp(i*xi.z). -/
def frequencyScale : ℝ := 2 * Real.pi

theorem frequencyScale_pos : 0 < frequencyScale := by
  unfold frequencyScale
  positivity

theorem frequencyScale_ne_zero : frequencyScale ≠ 0 := frequencyScale_pos.ne'

variable (m : ℕ)

/-- Coordinates of a physical frequency in the normalized Euclidean space. -/
def normalizedFrequency (ξ : Fin m → ℝ) : V m :=
  frequencyScale⁻¹ • WithLp.toLp 2 ξ

def physicalCoordinates (ν : V m) : Fin m → ℝ :=
  fun i => frequencyScale * ν i

@[simp] theorem physical_coordinate_normalized (ξ : Fin m → ℝ) (i : Fin m) :
    physicalCoordinates m (normalizedFrequency m ξ) i = ξ i := by
  change frequencyScale * (frequencyScale⁻¹ * ξ i) = ξ i
  field_simp [frequencyScale_ne_zero]

@[simp] theorem normalized_physicalCoordinates (ν : V m) :
    normalizedFrequency m (physicalCoordinates m ν) = ν := by
  ext i
  change frequencyScale⁻¹ * (frequencyScale * ν i) = ν i
  field_simp [frequencyScale_ne_zero]

/-- Unit-Jacobian transport from the arithmetic Pi coordinates into the
Euclidean space. This is a pinned native Mathlib measure equivalence. -/
theorem integral_toLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V m → E) :
    (∫ ξ : Fin m → ℝ, g (WithLp.toLp 2 ξ)) = ∫ ν : V m, g ν := by
  have hp :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).symm.integral_comp' g
  simpa only [MeasurableEquiv.symm_symm, MeasurableEquiv.coe_toLp] using hp

theorem integrable_toLp {E : Type*} [NormedAddCommGroup E]
    (g : V m → E) (hg : Integrable g) :
    Integrable (fun ξ : Fin m → ℝ => g (WithLp.toLp 2 ξ)) := by
  have hp :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).symm
  have hi := (hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hg
  simpa only [MeasurableEquiv.symm_symm, MeasurableEquiv.coe_toLp] using hi

/-- The actual Jacobian of xi=2*pi*nu in dimension m. The native Haar
scaling theorem is valid at dimension zero, so no nontriviality premise
and no special rank-four normalization are introduced. -/
theorem integral_normalizedFrequency {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : V m → E) :
    (∫ ξ : Fin m → ℝ, g (normalizedFrequency m ξ)) =
      frequencyScale ^ m • ∫ ν : V m, g ν := by
  calc
    (∫ ξ : Fin m → ℝ, g (normalizedFrequency m ξ)) =
        ∫ ν : V m, g (frequencyScale⁻¹ • ν) :=
      integral_toLp m (fun ν => g (frequencyScale⁻¹ • ν))
    _ = frequencyScale ^ m • ∫ ν : V m, g ν := by
      simpa only [finrank_euclideanSpace, Fintype.card_fin] using
        (Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (V m))
          g frequencyScale_pos.le)

theorem normalized_integral_normalizedFrequency {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : V m → E) :
    (frequencyScale ^ m)⁻¹ •
      (∫ ξ : Fin m → ℝ, g (normalizedFrequency m ξ)) = ∫ ν : V m, g ν := by
  rw [integral_normalizedFrequency, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero m frequencyScale_ne_zero), one_smul]

theorem integrable_normalizedFrequency {E : Type*} [NormedAddCommGroup E]
    (g : V m → E) (hg : Integrable g) :
    Integrable (fun ξ : Fin m → ℝ => g (normalizedFrequency m ξ)) := by
  have hd : Integrable (fun ν : V m => g (frequencyScale⁻¹ • ν)) :=
    (integrable_comp_smul_iff (volume : Measure (V m)) g
      (inv_ne_zero frequencyScale_ne_zero)).2 hg
  exact integrable_toLp m _ hd

def dotPhysical (ξ : Fin m → ℝ) (z : V m) : ℝ := ∑ i, ξ i * z i

theorem scaled_inner_eq_dot (ξ : Fin m → ℝ) (z : V m) :
    frequencyScale * ⟪normalizedFrequency m ξ, z⟫_ℝ = dotPhysical m ξ z := by
  rw [PiLp.inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [normalizedFrequency, PiLp.smul_apply, PiLp.toLp_apply,
    smul_eq_mul, Real.inner_apply, dotPhysical]
  field_simp [frequencyScale_ne_zero] <;> ring

theorem scaled_inner_right_eq_dot (ξ : Fin m → ℝ) (z : V m) :
    frequencyScale * ⟪z, normalizedFrequency m ξ⟫_ℝ = dotPhysical m ξ z := by
  rw [real_inner_comm]
  exact scaled_inner_eq_dot m ξ z

/-- The actual physical-frequency transform, with the original paper's
unscaled spatial Lebesgue measure. It is not an independent new transform. -/
def physicalFourier (f : V m → ℂ) (ξ : Fin m → ℝ) : ℂ :=
  𝓕 f (normalizedFrequency m ξ)

/-- Exp(-i*xi.z), derived from the native exp(-2*pi*i*nu.z) Fourier kernel. -/
theorem physicalFourier_eq_integral (f : V m → ℂ) (ξ : Fin m → ℝ) :
    physicalFourier m f ξ =
      ∫ z : V m, Complex.exp (((-dotPhysical m ξ z : ℝ) : ℂ) * Complex.I) * f z := by
  rw [physicalFourier, Real.fourier_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    have hphase : -2 * Real.pi * ⟪z, normalizedFrequency m ξ⟫_ℝ =
        -dotPhysical m ξ z := by
      have h := scaled_inner_right_eq_dot m ξ z
      dsimp only [frequencyScale] at h
      nlinarith
    rw [hphase, smul_eq_mul])

def physicalPhase (z : V m) (ξ : Fin m → ℝ) : ℂ :=
  Complex.exp (((dotPhysical m ξ z : ℝ) : ℂ) * Complex.I)

theorem physicalPhase_eq_native (z : V m) (ξ : Fin m → ℝ) :
    physicalPhase m z ξ =
      Complex.exp (((2 * Real.pi * ⟪normalizedFrequency m ξ, z⟫_ℝ : ℝ) : ℂ) *
        Complex.I) := by
  have h := scaled_inner_eq_dot m ξ z
  simpa only [physicalPhase, frequencyScale] using
    congrArg (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) h.symm

theorem physicalPhase_continuous (z : V m) : Continuous (physicalPhase m z) := by
  unfold physicalPhase dotPhysical
  fun_prop

theorem physicalPhase_norm (z : V m) (ξ : Fin m → ℝ) :
    ‖physicalPhase m z ξ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- Compact smooth Euclidean charts have genuinely integrable native
Fourier transforms, by the existing Schwartz-map Fourier theorem. -/
theorem euclidean_fourier_integrable (f : V m → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : Integrable (𝓕 f) := by
  let F : 𝓢(V m, ℂ) := hc.toSchwartzMap hf
  have hF : (F : V m → ℂ) = f := rfl
  have hi := (𝓕 F).integrable
  simpa only [SchwartzMap.fourier_coe, hF] using hi

theorem physicalFourier_integrable (f : V m → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (physicalFourier m f) :=
  integrable_normalizedFrequency m (𝓕 f) (euclidean_fourier_integrable m f hf hc)

/-- The source pointwise mixed-IBP theorem is now applied to the actual
native Fourier value at xi/(2*pi); its product kernel is the literal
physical product product_i(1+xi_i^2)^(-1). -/
theorem physicalFourier_pointwise (f : V m → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (ξ : Fin m → ℝ) :
    ‖physicalFourier m f ξ‖ ≤ mixedD m f * productCauchy m ξ := by
  have hp := pointwise_cauchy m f hf hc (normalizedFrequency m ξ)
  have hkernel : cauchyProduct m (normalizedFrequency m ξ) = productCauchy m ξ := by
    unfold cauchyProduct productCauchy
    apply Finset.prod_congr rfl
    intro i hi
    have hcoord : physical m (normalizedFrequency m ξ) i = ξ i :=
      physical_coordinate_normalized m ξ i
    rw [hcoord]
    rfl
  simpa only [physicalFourier, hkernel] using hp

theorem mixedD_nonneg (f : V m → ℂ) : 0 ≤ mixedD m f := by
  unfold mixedD
  exact Finset.sum_nonneg (fun S hS => integral_nonneg (fun z => norm_nonneg _))

/-- Exact L1 Jacobian: the normalized physical Fourier mass is precisely
Mathlib's native Euclidean Fourier mass. -/
theorem physicalFourier_l1_identity (f : V m → ℂ) :
    (∫ ξ : Fin m → ℝ, ‖physicalFourier m f ξ‖) / frequencyScale ^ m =
      ∫ ν : V m, ‖𝓕 f ν‖ := by
  have hi := normalized_integral_normalizedFrequency m (fun ν : V m => ‖𝓕 f ν‖)
  simpa only [physicalFourier, smul_eq_mul, div_eq_mul_inv, mul_comm] using hi

theorem physicalFourier_normalized_l1_le (f : V m → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ ξ : Fin m → ℝ, ‖physicalFourier m f ξ‖) / frequencyScale ^ m ≤
      mixedD m f / 2 ^ m := by
  simpa only [frequencyScale] using
    normalized_l1_of_mixed_ibp_pointwise m (physicalFourier m f) (mixedD m f)
      (physicalFourier_integrable m f hf hc).norm
      (physicalFourier_pointwise m f hf hc)

/-- The equality above also identifies the native Fourier L1 budget:
D/2^m is exact at every finite rank, including ranks below four. -/
theorem euclidean_fourier_l1_le (f : V m → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ ν : V m, ‖𝓕 f ν‖) ≤ mixedD m f / 2 ^ m := by
  rw [← physicalFourier_l1_identity]
  exact physicalFourier_normalized_l1_le m f hf hc

/-- Actual inverse Fourier synthesis in physical coordinates. Both the
phase identity and the Jacobian are proved above; the native inversion
input is Mathlib's theorem applied to this compact smooth Euclidean f. -/
theorem physical_inverse (f : V m → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (z : V m) :
    (frequencyScale ^ m)⁻¹ •
      (∫ ξ : Fin m → ℝ, physicalFourier m f ξ * physicalPhase m z ξ) = f z := by
  let G : V m → ℂ := fun ν =>
    Complex.exp (((2 * Real.pi * ⟪ν, z⟫_ℝ : ℝ) : ℂ) * Complex.I) * 𝓕 f ν
  have hintegrand :
      (fun ξ => physicalFourier m f ξ * physicalPhase m z ξ) =
      fun ξ => G (normalizedFrequency m ξ) := by
    funext ξ
    rw [physicalPhase_eq_native]
    dsimp only [physicalFourier, G]
    exact mul_comm _ _
  rw [hintegrand, normalized_integral_normalizedFrequency]
  have hinv : (∫ ν : V m, G ν) = 𝓕⁻ (𝓕 f) z := by
    rw [Real.fourierInv_eq']
    rfl
  rw [hinv]
  exact (hf.continuous.integrable_of_hasCompactSupport hc).fourierInv_fourier_eq
    (euclidean_fourier_integrable m f hf hc) hf.continuous.continuousAt

def truncatedPhysical (f : V m → ℂ) (H : ℝ) (z : V m) : ℂ :=
  (frequencyScale ^ m)⁻¹ •
    ∫ ξ in (outsideCube m H)ᶜ, physicalFourier m f ξ * physicalPhase m z ξ

/-- The original paper's uniform truncation estimate (F), now for the
actual Euclidean transform. It consumes the newly proved cube-tail
calculation, with no physical-transform or Fourier-representation premise. -/
theorem actual_uniform_truncation_error (f : V m → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (H : ℝ) (hH : 0 < H) (z : V m) :
    ‖f z - truncatedPhysical m f H z‖ ≤ (m : ℝ) * mixedD m f / H := by
  have htail := normalized_synthesis_error_le m (physicalFourier m f)
    (physicalPhase m z) (physicalFourier_integrable m f hf hc)
    (physicalPhase_continuous m z).aestronglyMeasurable
    (fun ξ => (physicalPhase_norm m z ξ).le)
    (mixedD m f) H (mixedD_nonneg m f) hH
    (physicalFourier_pointwise m f hf hc)
  rw [← physical_inverse m f hf hc z, truncatedPhysical, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg frequencyScale_pos.le m))]
  simpa only [frequencyScale, div_eq_mul_inv, mul_comm] using htail

/-- In rank zero the Jacobian is one; there is a single frequency point. -/
theorem jacobian_rank_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V 0 → E) :
    (∫ ξ : Fin 0 → ℝ, g (normalizedFrequency 0 ξ)) = ∫ ν : V 0, g ν := by
  simpa using integral_normalizedFrequency 0 g

/-- There are no omitted coordinate slabs in rank zero, for any cutoff. -/
theorem outsideCube_rank_zero (H : ℝ) : outsideCube 0 H = ∅ := by
  ext ξ
  simp only [outsideCube, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨i, hi⟩
  exact Fin.elim0 i

/-- The rank-zero retained synthesis is exactly f, without a positive-H
hypothesis. This also records that no artificial D/16 normalization occurs. -/
theorem truncated_rank_zero (f : V 0 → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (H : ℝ) (z : V 0) :
    truncatedPhysical 0 f H z = f z := by
  simpa only [truncatedPhysical, outsideCube_rank_zero, Set.compl_empty,
    Measure.restrict_univ] using physical_inverse 0 f hf hc z

end
end ImbalancedChen.P5Z.ActualEuclideanPhysicalFourier
