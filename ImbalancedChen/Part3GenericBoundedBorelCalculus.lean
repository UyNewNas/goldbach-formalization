import ImbalancedChen.Part3GenericGlobalContinuousCFC
import ImbalancedChen.Part3GenericGlobalProjectionScalarConsistency

/-! SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Literal bounded measurable complex multiplication on the actual scalar fibers,
transported through the actual global unitary. Algebra and adjoints are proved
on representatives. No Borel-calculus or representation premise is used. -/
namespace ImbalancedChen.Part3.GenericBoundedBorelCalculus20261025a
noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a
open ImbalancedChen.Part3.GenericGlobalContinuousCFC20261025a
open ImbalancedChen.Part3.GenericCyclicBorelProjection20261025a
open ImbalancedChen.Part3.GenericGlobalBorelProjection20261025a

structure BoundedBorelFunction (X : Type*) [MeasurableSpace X] where
  toFun : X → ℂ
  measurable_toFun : Measurable toFun
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le_bound : ∀ x, ‖toFun x‖ ≤ bound

namespace BoundedBorelFunction
variable {X : Type*} [MeasurableSpace X]
instance : CoeFun (BoundedBorelFunction X) (fun _ => X → ℂ) := ⟨toFun⟩

def const (z : ℂ) : BoundedBorelFunction X where
  toFun := fun _ => z
  measurable_toFun := measurable_const
  bound := ‖z‖
  bound_nonneg := norm_nonneg z
  norm_le_bound := fun _ => le_rfl

def add (φ ψ : BoundedBorelFunction X) : BoundedBorelFunction X where
  toFun := fun t => φ t + ψ t
  measurable_toFun := φ.measurable_toFun.add ψ.measurable_toFun
  bound := φ.bound + ψ.bound
  bound_nonneg := add_nonneg φ.bound_nonneg ψ.bound_nonneg
  norm_le_bound := fun t => (norm_add_le _ _).trans (add_le_add (φ.norm_le_bound t) (ψ.norm_le_bound t))

def sub (φ ψ : BoundedBorelFunction X) : BoundedBorelFunction X where
  toFun := fun t => φ t - ψ t
  measurable_toFun := φ.measurable_toFun.sub ψ.measurable_toFun
  bound := φ.bound + ψ.bound
  bound_nonneg := add_nonneg φ.bound_nonneg ψ.bound_nonneg
  norm_le_bound := fun t => (norm_sub_le _ _).trans (add_le_add (φ.norm_le_bound t) (ψ.norm_le_bound t))

def mul (φ ψ : BoundedBorelFunction X) : BoundedBorelFunction X where
  toFun := fun t => φ t * ψ t
  measurable_toFun := φ.measurable_toFun.mul ψ.measurable_toFun
  bound := φ.bound * ψ.bound
  bound_nonneg := mul_nonneg φ.bound_nonneg ψ.bound_nonneg
  norm_le_bound := fun t => by
    rw [norm_mul]
    exact mul_le_mul (φ.norm_le_bound t) (ψ.norm_le_bound t) (norm_nonneg _) φ.bound_nonneg

def conj (φ : BoundedBorelFunction X) : BoundedBorelFunction X where
  toFun := fun t => star (φ t)
  measurable_toFun := φ.measurable_toFun.star
  bound := φ.bound
  bound_nonneg := φ.bound_nonneg
  norm_le_bound := fun t => by simpa only [norm_star] using φ.norm_le_bound t

def indicator (B : Set X) (hB : MeasurableSet B) : BoundedBorelFunction X where
  toFun := B.indicator (fun _ => (1 : ℂ))
  measurable_toFun := measurable_const.indicator hB
  bound := 1
  bound_nonneg := zero_le_one
  norm_le_bound := fun t => by by_cases ht : t ∈ B <;> simp [ht]

def ofContinuous [TopologicalSpace X] [BorelSpace X] [CompactSpace X]
    (φ : C(X, ℂ)) : BoundedBorelFunction X where
  toFun := φ
  measurable_toFun := φ.continuous.measurable
  bound := ‖φ‖
  bound_nonneg := norm_nonneg φ
  norm_le_bound := φ.norm_coe_le_norm
end BoundedBorelFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

private theorem multiply_memLp (f : H) (φ : BoundedBorelFunction (ResolventSpectrum R))
    (ξ : ScalarL2 R hSA f) : MemLp (fun t => φ t * ξ t) 2 (scalarMeasure R hSA f) := by
  apply (Lp.memLp ξ).of_le_mul
    (φ.measurable_toFun.aestronglyMeasurable.mul (Lp.aestronglyMeasurable ξ))
  exact Filter.Eventually.of_forall fun t => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (φ.norm_le_bound t) (norm_nonneg _)

def fiberProduct (f : H) (φ : BoundedBorelFunction (ResolventSpectrum R))
    (ξ : ScalarL2 R hSA f) : ScalarL2 R hSA f :=
  (multiply_memLp R hSA f φ ξ).toLp (fun t => φ t * ξ t)

theorem fiberProduct_coe_ae (f : H) (φ : BoundedBorelFunction (ResolventSpectrum R))
    (ξ : ScalarL2 R hSA f) : fiberProduct R hSA f φ ξ =ᵐ[scalarMeasure R hSA f]
      (fun t => φ t * ξ t) := (multiply_memLp R hSA f φ ξ).coeFn_toLp

def fiberProductLinear (f : H) (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    ScalarL2 R hSA f →ₗ[ℂ] ScalarL2 R hSA f where
  toFun := fiberProduct R hSA f φ
  map_add' ξ η := by
    apply Lp.ext
    filter_upwards [fiberProduct_coe_ae R hSA f φ (ξ + η), Lp.coeFn_add ξ η,
      Lp.coeFn_add (fiberProduct R hSA f φ ξ) (fiberProduct R hSA f φ η),
      fiberProduct_coe_ae R hSA f φ ξ, fiberProduct_coe_ae R hSA f φ η]
        with t hleft hin hright hξ hη
    rw [hleft, hright, hξ, hη, hin]
    ring
  map_smul' c ξ := by
    apply Lp.ext
    filter_upwards [fiberProduct_coe_ae R hSA f φ (c • ξ), Lp.coeFn_smul c ξ,
      Lp.coeFn_smul c (fiberProduct R hSA f φ ξ), fiberProduct_coe_ae R hSA f φ ξ]
        with t hleft hin hright hξ
    rw [hleft, hright, hξ, hin]
    simp only [smul_eq_mul]
    ring

theorem fiberProduct_norm_le (f : H) (φ : BoundedBorelFunction (ResolventSpectrum R))
    (ξ : ScalarL2 R hSA f) : ‖fiberProduct R hSA f φ ξ‖ ≤ φ.bound * ‖ξ‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [fiberProduct_coe_ae R hSA f φ ξ] with t ht
  rw [ht, norm_mul]
  exact mul_le_mul_of_nonneg_right (φ.norm_le_bound t) (norm_nonneg _)

def fiberMultiplier (f : H) (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    ScalarL2 R hSA f →L[ℂ] ScalarL2 R hSA f :=
  (fiberProductLinear R hSA f φ).mkContinuous φ.bound (fiberProduct_norm_le R hSA f φ)

theorem fiberMultiplier_coe_ae (f : H) (φ : BoundedBorelFunction (ResolventSpectrum R))
    (ξ : ScalarL2 R hSA f) : fiberMultiplier R hSA f φ ξ =ᵐ[scalarMeasure R hSA f]
      (fun t => φ t * ξ t) := fiberProduct_coe_ae R hSA f φ ξ

theorem fiberMultiplier_opNorm_le (f : H) (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    ‖fiberMultiplier R hSA f φ‖ ≤ φ.bound :=
  (fiberMultiplier R hSA f φ).opNorm_le_bound φ.bound_nonneg (fiberProduct_norm_le R hSA f φ)

/-- Bounds are construction witnesses only; the operator depends on the function. -/
theorem fiberMultiplier_congr (f : H) (φ ψ : BoundedBorelFunction (ResolventSpectrum R))
    (h : ∀ t, φ t = ψ t) : fiberMultiplier R hSA f φ = fiberMultiplier R hSA f ψ := by
  ext ξ
  apply Lp.ext
  filter_upwards [fiberMultiplier_coe_ae R hSA f φ ξ,
    fiberMultiplier_coe_ae R hSA f ψ ξ] with t hφ hψ
  rw [hφ, hψ, h t]

theorem fiberMultiplier_mul (f : H) (φ ψ : BoundedBorelFunction (ResolventSpectrum R)) :
    fiberMultiplier R hSA f (φ.mul ψ) =
      (fiberMultiplier R hSA f φ).comp (fiberMultiplier R hSA f ψ) := by
  ext ξ
  apply Lp.ext
  filter_upwards [fiberMultiplier_coe_ae R hSA f (φ.mul ψ) ξ,
    fiberMultiplier_coe_ae R hSA f φ (fiberMultiplier R hSA f ψ ξ),
    fiberMultiplier_coe_ae R hSA f ψ ξ] with t hleft hout hin
  change _ = (fiberMultiplier R hSA f φ (fiberMultiplier R hSA f ψ ξ)) t
  rw [hleft, hout, hin]
  exact mul_assoc _ _ _

theorem fiberMultiplier_add (f : H) (φ ψ : BoundedBorelFunction (ResolventSpectrum R)) :
    fiberMultiplier R hSA f (φ.add ψ) = fiberMultiplier R hSA f φ + fiberMultiplier R hSA f ψ := by
  ext ξ
  apply Lp.ext
  filter_upwards [fiberMultiplier_coe_ae R hSA f (φ.add ψ) ξ,
    fiberMultiplier_coe_ae R hSA f φ ξ, fiberMultiplier_coe_ae R hSA f ψ ξ,
    Lp.coeFn_add (fiberMultiplier R hSA f φ ξ) (fiberMultiplier R hSA f ψ ξ)]
    with t hab ha hb hadd
  change _ = ((fiberMultiplier R hSA f φ ξ) + (fiberMultiplier R hSA f ψ ξ)) t
  rw [hab, hadd, ha, hb]
  exact add_mul _ _ _

theorem fiberMultiplier_sub (f : H) (φ ψ : BoundedBorelFunction (ResolventSpectrum R)) :
    fiberMultiplier R hSA f (φ.sub ψ) = fiberMultiplier R hSA f φ - fiberMultiplier R hSA f ψ := by
  ext ξ
  apply Lp.ext
  filter_upwards [fiberMultiplier_coe_ae R hSA f (φ.sub ψ) ξ,
    fiberMultiplier_coe_ae R hSA f φ ξ, fiberMultiplier_coe_ae R hSA f ψ ξ,
    Lp.coeFn_sub (fiberMultiplier R hSA f φ ξ) (fiberMultiplier R hSA f ψ ξ)]
    with t hab ha hb hsub
  change _ = ((fiberMultiplier R hSA f φ ξ) - (fiberMultiplier R hSA f ψ ξ)) t
  rw [hab, hsub, ha, hb]
  exact sub_mul _ _ _

theorem fiberMultiplier_inner (f : H) (φ : BoundedBorelFunction (ResolventSpectrum R))
    (ξ η : ScalarL2 R hSA f) :
    inner ℂ (fiberMultiplier R hSA f φ ξ) η = inner ℂ ξ (fiberMultiplier R hSA f φ.conj η) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fiberMultiplier_coe_ae R hSA f φ ξ,
    fiberMultiplier_coe_ae R hSA f φ.conj η] with t hφ hconj
  rw [hφ, hconj]
  simp only [RCLike.inner_apply', BoundedBorelFunction.conj, map_mul]
  ring

theorem fiberMultiplier_continuous (f : H) (φ : C(ResolventSpectrum R, ℂ)) :
    fiberMultiplier R hSA f (BoundedBorelFunction.ofContinuous φ) = continuousMultiplier R hSA f φ := by
  ext ξ
  apply Lp.ext
  filter_upwards [fiberMultiplier_coe_ae R hSA f (BoundedBorelFunction.ofContinuous φ) ξ,
    continuousMultiplier_coe_ae R hSA f φ ξ] with t hb hc
  exact hb.trans hc.symm

theorem fiberMultiplier_indicator (f : H) (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    fiberMultiplier R hSA f (BoundedBorelFunction.indicator B hB) = borelMultiplier R hSA f B hB := by
  ext ξ
  apply Lp.ext
  filter_upwards [fiberMultiplier_coe_ae R hSA f (BoundedBorelFunction.indicator B hB) ξ,
    borelMultiplier_coe_ae R hSA f B hB ξ] with t hb hc
  rw [hb, hc]
  by_cases ht : t ∈ B <;> simp [BoundedBorelFunction.indicator, ht]

def diagonalBorelMultiplier (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    SpectralSum R hSA →L[ℂ] SpectralSum R hSA :=
  lp.mapCLM 2 (fun i : SpectralIndex R hSA => fiberMultiplier R hSA (i : H) φ)
    φ.bound_nonneg (fun i => fiberMultiplier_opNorm_le R hSA (i : H) φ)

theorem diagonalBorelMultiplier_apply (φ : BoundedBorelFunction (ResolventSpectrum R))
    (ξ : SpectralSum R hSA) (i : SpectralIndex R hSA) :
    diagonalBorelMultiplier R hSA φ ξ i = fiberMultiplier R hSA (i : H) φ (ξ i) := rfl

theorem diagonalBorelMultiplier_opNorm_le (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    ‖diagonalBorelMultiplier R hSA φ‖ ≤ φ.bound :=
  lp.norm_mapCLM_le 2 (fun i : SpectralIndex R hSA => fiberMultiplier R hSA (i : H) φ)
    φ.bound_nonneg (fun i => fiberMultiplier_opNorm_le R hSA (i : H) φ)

def borelFunctionalCalculus (φ : BoundedBorelFunction (ResolventSpectrum R)) : H →L[ℂ] H :=
  (spectralUnitary R hSA).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((diagonalBorelMultiplier R hSA φ).comp
      (spectralUnitary R hSA).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem borelFunctionalCalculus_apply (φ : BoundedBorelFunction (ResolventSpectrum R)) (u : H) :
    borelFunctionalCalculus R hSA φ u =
      spectralUnitary R hSA (diagonalBorelMultiplier R hSA φ ((spectralUnitary R hSA).symm u)) := rfl

theorem borelFunctionalCalculus_coordinates (φ : BoundedBorelFunction (ResolventSpectrum R)) (u : H) :
    (spectralUnitary R hSA).symm (borelFunctionalCalculus R hSA φ u) =
      diagonalBorelMultiplier R hSA φ ((spectralUnitary R hSA).symm u) := by
  rw [borelFunctionalCalculus_apply, (spectralUnitary R hSA).symm_apply_apply]

theorem borelFunctionalCalculus_norm_le (φ : BoundedBorelFunction (ResolventSpectrum R)) (u : H) :
    ‖borelFunctionalCalculus R hSA φ u‖ ≤ φ.bound * ‖u‖ := by
  rw [borelFunctionalCalculus_apply, (spectralUnitary R hSA).norm_map]
  calc
    _ ≤ ‖diagonalBorelMultiplier R hSA φ‖ * ‖(spectralUnitary R hSA).symm u‖ :=
      (diagonalBorelMultiplier R hSA φ).le_opNorm _
    _ ≤ φ.bound * ‖(spectralUnitary R hSA).symm u‖ :=
      mul_le_mul_of_nonneg_right (diagonalBorelMultiplier_opNorm_le R hSA φ) (norm_nonneg _)
    _ = _ := by rw [(spectralUnitary R hSA).symm.norm_map]

theorem borelFunctionalCalculus_opNorm_le (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    ‖borelFunctionalCalculus R hSA φ‖ ≤ φ.bound :=
  (borelFunctionalCalculus R hSA φ).opNorm_le_bound φ.bound_nonneg
    (borelFunctionalCalculus_norm_le R hSA φ)

theorem borelFunctionalCalculus_congr (φ ψ : BoundedBorelFunction (ResolventSpectrum R))
    (h : ∀ t, φ t = ψ t) : borelFunctionalCalculus R hSA φ = borelFunctionalCalculus R hSA ψ := by
  have hd : diagonalBorelMultiplier R hSA φ = diagonalBorelMultiplier R hSA ψ := by
    ext ξ i
    exact congrArg (fun T : ScalarL2 R hSA (i : H) →L[ℂ] ScalarL2 R hSA (i : H) => T (ξ i))
      (fiberMultiplier_congr R hSA (i : H) φ ψ h)
  unfold borelFunctionalCalculus
  rw [hd]

theorem borelFunctionalCalculus_mul (φ ψ : BoundedBorelFunction (ResolventSpectrum R)) :
    borelFunctionalCalculus R hSA (φ.mul ψ) =
      (borelFunctionalCalculus R hSA φ).comp (borelFunctionalCalculus R hSA ψ) := by
  ext u
  apply (spectralUnitary R hSA).symm.injective
  simp only [ContinuousLinearMap.comp_apply, borelFunctionalCalculus_coordinates]
  ext i
  exact congrArg (fun T : ScalarL2 R hSA (i : H) →L[ℂ] ScalarL2 R hSA (i : H) =>
    T (((spectralUnitary R hSA).symm u) i)) (fiberMultiplier_mul R hSA (i : H) φ ψ)

theorem borelFunctionalCalculus_add (φ ψ : BoundedBorelFunction (ResolventSpectrum R)) :
    borelFunctionalCalculus R hSA (φ.add ψ) =
      borelFunctionalCalculus R hSA φ + borelFunctionalCalculus R hSA ψ := by
  ext u
  apply (spectralUnitary R hSA).symm.injective
  simp only [ContinuousLinearMap.add_apply, map_add, borelFunctionalCalculus_coordinates]
  ext i
  exact congrArg (fun T : ScalarL2 R hSA (i : H) →L[ℂ] ScalarL2 R hSA (i : H) =>
    T (((spectralUnitary R hSA).symm u) i)) (fiberMultiplier_add R hSA (i : H) φ ψ)

theorem borelFunctionalCalculus_sub (φ ψ : BoundedBorelFunction (ResolventSpectrum R)) :
    borelFunctionalCalculus R hSA (φ.sub ψ) =
      borelFunctionalCalculus R hSA φ - borelFunctionalCalculus R hSA ψ := by
  ext u
  apply (spectralUnitary R hSA).symm.injective
  simp only [ContinuousLinearMap.sub_apply, map_sub, borelFunctionalCalculus_coordinates]
  ext i
  exact congrArg (fun T : ScalarL2 R hSA (i : H) →L[ℂ] ScalarL2 R hSA (i : H) =>
    T (((spectralUnitary R hSA).symm u) i)) (fiberMultiplier_sub R hSA (i : H) φ ψ)

theorem borelFunctionalCalculus_inner (φ : BoundedBorelFunction (ResolventSpectrum R)) (u v : H) :
    inner ℂ (borelFunctionalCalculus R hSA φ u) v =
      inner ℂ u (borelFunctionalCalculus R hSA φ.conj v) := by
  rw [← (spectralUnitary R hSA).symm.inner_map_map (borelFunctionalCalculus R hSA φ u) v,
    ← (spectralUnitary R hSA).symm.inner_map_map u (borelFunctionalCalculus R hSA φ.conj v),
    borelFunctionalCalculus_coordinates, borelFunctionalCalculus_coordinates,
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  exact tsum_congr fun i => fiberMultiplier_inner R hSA (i : H) φ _ _

theorem borelFunctionalCalculus_conj (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    borelFunctionalCalculus R hSA φ.conj = (borelFunctionalCalculus R hSA φ).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  have h := borelFunctionalCalculus_inner R hSA φ.conj u v
  have hc : borelFunctionalCalculus R hSA φ.conj.conj = borelFunctionalCalculus R hSA φ :=
    borelFunctionalCalculus_congr R hSA _ _ (fun t => star_star (φ t))
  rw [hc] at h
  exact h

theorem borelFunctionalCalculus_continuous (φ : C(ResolventSpectrum R, ℂ)) :
    borelFunctionalCalculus R hSA (BoundedBorelFunction.ofContinuous φ) = complexResolventCFC R hSA φ := by
  have hd : diagonalBorelMultiplier R hSA (BoundedBorelFunction.ofContinuous φ) =
      diagonalContinuous R hSA φ := by
    ext ξ i
    exact congrArg (fun T : ScalarL2 R hSA (i : H) →L[ℂ] ScalarL2 R hSA (i : H) => T (ξ i))
      (fiberMultiplier_continuous R hSA (i : H) φ)
  rw [CFC_unitary_conjugacy]
  unfold borelFunctionalCalculus
  rw [hd]

theorem borelFunctionalCalculus_indicator (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    borelFunctionalCalculus R hSA (BoundedBorelFunction.indicator B hB) =
      globalBorelProjection R hSA B hB := by
  have hd : diagonalBorelMultiplier R hSA (BoundedBorelFunction.indicator B hB) =
      diagonalBorel R hSA B hB := by
    ext ξ i
    exact congrArg (fun T : ScalarL2 R hSA (i : H) →L[ℂ] ScalarL2 R hSA (i : H) => T (ξ i))
      (fiberMultiplier_indicator R hSA (i : H) B hB)
  unfold borelFunctionalCalculus globalBorelProjection
  rw [hd]

theorem fiberMultiplier_const (f : H) (z : ℂ) :
    fiberMultiplier R hSA f (BoundedBorelFunction.const z) =
      z • ContinuousLinearMap.id ℂ (ScalarL2 R hSA f) := by
  ext ξ
  apply Lp.ext
  filter_upwards [fiberMultiplier_coe_ae R hSA f (BoundedBorelFunction.const z) ξ,
    Lp.coeFn_smul z ξ] with t hm hs
  change _ = (z • ξ) t
  rw [hm, hs]
  rfl

theorem borelFunctionalCalculus_const (z : ℂ) :
    borelFunctionalCalculus R hSA (BoundedBorelFunction.const z) =
      z • ContinuousLinearMap.id ℂ H := by
  ext u
  apply (spectralUnitary R hSA).symm.injective
  change (spectralUnitary R hSA).symm
      (borelFunctionalCalculus R hSA (BoundedBorelFunction.const z) u) =
    (spectralUnitary R hSA).symm (z • u)
  rw [borelFunctionalCalculus_coordinates, map_smul]
  ext i
  change fiberMultiplier R hSA (i : H) (BoundedBorelFunction.const z)
    (((spectralUnitary R hSA).symm u) i) = z • (((spectralUnitary R hSA).symm u) i)
  rw [fiberMultiplier_const]
  rfl

theorem borelFunctionalCalculus_selfAdjoint
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (hreal : ∀ t, star (φ t) = φ t) :
    IsSelfAdjoint (borelFunctionalCalculus R hSA φ) := by
  change star (borelFunctionalCalculus R hSA φ) = borelFunctionalCalculus R hSA φ
  rw [ContinuousLinearMap.star_eq_adjoint, ← borelFunctionalCalculus_conj]
  exact borelFunctionalCalculus_congr R hSA _ _ hreal

end
end ImbalancedChen.Part3.GenericBoundedBorelCalculus20261025a