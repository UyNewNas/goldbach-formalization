import ImbalancedChen.Part3NormalizedBoundedPairOperator
import ImbalancedChen.Part3GenericBoundedBorelCalculus

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Native self-adjoint multiplication by an ARBITRARY measurable real function
on the genuine global scalar spectral representation. No boundedness of
that function is assumed. The actual graph, entire domain and action are
identified, including both fiber L2 integrability and whole-family norm
summability. No domain, self-adjointness or spectral representation is
assumed as an output supplier.
-/

namespace ImbalancedChen.Part3.GenericUnboundedRealBorelCalculus20261025a

noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.NormalizedBoundedPairOperator20261025a
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a
open ImbalancedChen.Part3.GenericBoundedBorelCalculus20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

/-- Nonvanishing measurable coefficients give genuinely injective global
multipliers, even without a uniform positive lower bound. -/
theorem calculus_injective_of_ne_zero (φ : BoundedBorelFunction (ResolventSpectrum R))
    (hφ : ∀ t, φ t ≠ 0) : Function.Injective (borelFunctionalCalculus R hSA φ) := by
  intro u v huv
  apply (spectralUnitary R hSA).symm.injective
  ext i
  apply Lp.ext
  have hdiag := congrArg (spectralUnitary R hSA).symm huv
  rw [borelFunctionalCalculus_coordinates, borelFunctionalCalculus_coordinates] at hdiag
  have hi := congrArg (fun ξ : SpectralSum R hSA => ξ i) hdiag
  change fiberMultiplier R hSA (i : H) φ (((spectralUnitary R hSA).symm u) i) =
    fiberMultiplier R hSA (i : H) φ (((spectralUnitary R hSA).symm v) i) at hi
  filter_upwards [fiberMultiplier_coe_ae R hSA (i : H) φ (((spectralUnitary R hSA).symm u) i),
    fiberMultiplier_coe_ae R hSA (i : H) φ (((spectralUnitary R hSA).symm v) i)] with t hu hv
  have ht := congrArg (fun ξ : ScalarL2 R hSA (i : H) => ξ t) hi
  rw [hu, hv] at ht
  exact mul_left_cancel₀ (hφ t) ht

theorem calculus_pair_eq_iff (φ ψ : BoundedBorelFunction (ResolventSpectrum R)) (u v : H) :
    borelFunctionalCalculus R hSA φ v = borelFunctionalCalculus R hSA ψ u ↔
      ∀ i : SpectralIndex R hSA,
        (fun t => φ t * (((spectralUnitary R hSA).symm v) i) t) =ᵐ[scalarMeasure R hSA (i : H)]
          (fun t => ψ t * (((spectralUnitary R hSA).symm u) i) t) := by
  constructor
  · intro huv i
    have hd := congrArg (spectralUnitary R hSA).symm huv
    rw [borelFunctionalCalculus_coordinates, borelFunctionalCalculus_coordinates] at hd
    have hi := congrArg (fun ξ : SpectralSum R hSA => ξ i) hd
    filter_upwards [fiberMultiplier_coe_ae R hSA (i : H) φ (((spectralUnitary R hSA).symm v) i),
      fiberMultiplier_coe_ae R hSA (i : H) ψ (((spectralUnitary R hSA).symm u) i)] with t hv hu
    exact hv.symm.trans ((congrArg (fun ξ : ScalarL2 R hSA (i : H) => ξ t) hi).trans hu)
  · intro h
    apply (spectralUnitary R hSA).symm.injective
    rw [borelFunctionalCalculus_coordinates, borelFunctionalCalculus_coordinates]
    ext i
    apply Lp.ext
    exact (fiberMultiplier_coe_ae R hSA (i : H) φ (((spectralUnitary R hSA).symm v) i)).trans
      ((h i).trans (fiberMultiplier_coe_ae R hSA (i : H) ψ (((spectralUnitary R hSA).symm u) i)).symm)

variable (m : ResolventSpectrum R → ℝ) (hm : Measurable m)

private theorem denominator_pos (t : ResolventSpectrum R) : 0 < 1 + (m t)^2 := by positivity

def normalizerB : BoundedBorelFunction (ResolventSpectrum R) where
  toFun := fun t => ((1 / (1 + (m t)^2) : ℝ) : ℂ)
  measurable_toFun := by fun_prop
  bound := 1
  bound_nonneg := zero_le_one
  norm_le_bound := by
    intro t
    have hd := denominator_pos R m t
    have hden : 1 ≤ 1 + (m t)^2 := le_add_of_nonneg_right (sq_nonneg _)
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_one, abs_of_pos hd] using
      (div_le_one hd).mpr hden

def normalizerC : BoundedBorelFunction (ResolventSpectrum R) where
  toFun := fun t => ((m t / (1 + (m t)^2) : ℝ) : ℂ)
  measurable_toFun := by fun_prop
  bound := 1
  bound_nonneg := zero_le_one
  norm_le_bound := by
    intro t
    have hd := denominator_pos R m t
    have habs : |m t| ≤ 1 + (m t)^2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (m t - 1), sq_nonneg (m t + 1)]
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hd] using
      (div_le_one hd).mpr habs

theorem normalizerB_ne_zero (t : ResolventSpectrum R) : normalizerB R m hm t ≠ 0 := by
  change ((1 / (1 + (m t)^2) : ℝ) : ℂ) ≠ 0
  exact_mod_cast (div_ne_zero one_ne_zero (ne_of_gt (denominator_pos R m t)))

theorem normalizer_scalar_iff (t : ResolventSpectrum R) (z w : ℂ) :
    normalizerB R m hm t * z = normalizerC R m hm t * w ↔ z = (m t : ℂ) * w := by
  have hc : normalizerC R m hm t = normalizerB R m hm t * (m t : ℂ) := by
    change ((m t / (1 + (m t)^2) : ℝ) : ℂ) =
      ((1 / (1 + (m t)^2) : ℝ) : ℂ) * (m t : ℂ)
    push_cast
    ring
  rw [hc, mul_assoc]
  constructor
  · exact mul_left_cancel₀ (normalizerB_ne_zero R m hm t)
  · intro h
    exact congrArg (fun z => normalizerB R m hm t * z) h

def regularizer : H →L[ℂ] H := borelFunctionalCalculus R hSA (normalizerB R m hm)
def regularizedMultiplier : H →L[ℂ] H := borelFunctionalCalculus R hSA (normalizerC R m hm)

theorem regularizer_selfAdjoint : IsSelfAdjoint (regularizer R hSA m hm) :=
  borelFunctionalCalculus_selfAdjoint R hSA _ (fun t => by simp [normalizerB])

theorem regularizedMultiplier_selfAdjoint : IsSelfAdjoint (regularizedMultiplier R hSA m hm) :=
  borelFunctionalCalculus_selfAdjoint R hSA _ (fun t => by simp [normalizerC])

theorem regularizer_injective : Function.Injective (regularizer R hSA m hm) :=
  calculus_injective_of_ne_zero R hSA _ (normalizerB_ne_zero R m hm)

theorem regularizers_commute :
    (regularizer R hSA m hm).comp (regularizedMultiplier R hSA m hm) =
      (regularizedMultiplier R hSA m hm).comp (regularizer R hSA m hm) := by
  unfold regularizer regularizedMultiplier
  rw [← borelFunctionalCalculus_mul, ← borelFunctionalCalculus_mul]
  apply borelFunctionalCalculus_congr
  intro t
  exact mul_comm _ _

theorem regularizers_normalized :
    (regularizer R hSA m hm).comp (regularizer R hSA m hm) +
      (regularizedMultiplier R hSA m hm).comp (regularizedMultiplier R hSA m hm) =
        regularizer R hSA m hm := by
  unfold regularizer regularizedMultiplier
  rw [← borelFunctionalCalculus_mul, ← borelFunctionalCalculus_mul, ← borelFunctionalCalculus_add]
  apply borelFunctionalCalculus_congr
  intro t
  change (((1 / (1 + (m t)^2) : ℝ) : ℂ) * ((1 / (1 + (m t)^2) : ℝ) : ℂ) +
    ((m t / (1 + (m t)^2) : ℝ) : ℂ) * ((m t / (1 + (m t)^2) : ℝ) : ℂ)) =
      ((1 / (1 + (m t)^2) : ℝ) : ℂ)
  have hd : (1 : ℂ) + (m t : ℂ)^2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (denominator_pos R m t))
  push_cast
  field_simp [hd] <;> ring

/-- The actual unbounded operator, constructed from bounded measurable
coefficients. Its domain is not prescribed by a desired conclusion. -/
def unboundedRealBorel : H →ₗ.[ℂ] H :=
  pairOperator (regularizer R hSA m hm) (regularizedMultiplier R hSA m hm)

theorem unboundedRealBorel_isClosed : (unboundedRealBorel R hSA m hm).IsClosed :=
  pairOperator_isClosed _ _ (regularizer_injective R hSA m hm)

theorem unboundedRealBorel_dense_domain : Dense ((unboundedRealBorel R hSA m hm).domain : Set H) :=
  pairOperator_dense_domain _ _ (regularizer_selfAdjoint R hSA m hm)
    (regularizer_injective R hSA m hm) (regularizers_commute R hSA m hm)

theorem unboundedRealBorel_isSelfAdjoint : IsSelfAdjoint (unboundedRealBorel R hSA m hm) :=
  pairOperator_isSelfAdjoint _ _ (regularizer_selfAdjoint R hSA m hm)
    (regularizedMultiplier_selfAdjoint R hSA m hm) (regularizer_injective R hSA m hm)
    (regularizers_commute R hSA m hm) (regularizers_normalized R hSA m hm)

/-- Exact multiplication graph in every actual scalar-measure fiber. -/
theorem unboundedRealBorel_mem_graph_iff (u v : H) :
    (u,v) ∈ (unboundedRealBorel R hSA m hm).graph ↔
      ∀ i : SpectralIndex R hSA,
        ((spectralUnitary R hSA).symm v) i =ᵐ[scalarMeasure R hSA (i : H)]
          (fun t => (m t : ℂ) * (((spectralUnitary R hSA).symm u) i) t) := by
  rw [unboundedRealBorel, pairOperator_mem_graph_iff _ _ (regularizer_injective R hSA m hm)]
  change borelFunctionalCalculus R hSA (normalizerB R m hm) v =
    borelFunctionalCalculus R hSA (normalizerC R m hm) u ↔ _
  rw [calculus_pair_eq_iff]
  constructor
  · intro h i
    filter_upwards [h i] with t ht
    exact (normalizer_scalar_iff R m hm t _ _).mp ht
  · intro h i
    filter_upwards [h i] with t ht
    exact (normalizer_scalar_iff R m hm t _ _).mpr ht

def realProduct (ξ : SpectralSum R hSA) (i : SpectralIndex R hSA) : ResolventSpectrum R → ℂ :=
  fun t => (m t : ℂ) * ξ i t

def RealMultiplierDomain (ξ : SpectralSum R hSA) : Prop :=
  ∃ h : ∀ i : SpectralIndex R hSA,
      MemLp (realProduct R hSA m ξ i) 2 (scalarMeasure R hSA (i : H)),
    Memℓp (fun i : SpectralIndex R hSA => (h i).toLp (realProduct R hSA m ξ i)) 2

theorem realMultiplierDomain_iff_exists (ξ : SpectralSum R hSA) :
    RealMultiplierDomain R hSA m ξ ↔ ∃ η : SpectralSum R hSA,
      ∀ i, η i =ᵐ[scalarMeasure R hSA (i : H)] realProduct R hSA m ξ i := by
  constructor
  · rintro ⟨h, hsum⟩
    exact ⟨⟨fun i => (h i).toLp (realProduct R hSA m ξ i), hsum⟩, fun i => (h i).coeFn_toLp⟩
  · rintro ⟨η, hη⟩
    have h : ∀ i, MemLp (realProduct R hSA m ξ i) 2 (scalarMeasure R hSA (i : H)) :=
      fun i => (memLp_congr_ae (hη i)).mp (Lp.memLp (η i))
    refine ⟨h, ?_⟩
    have heq : (fun i : SpectralIndex R hSA => (h i).toLp (realProduct R hSA m ξ i)) =
        (fun i => η i) := by
      funext i
      exact Lp.ext ((h i).coeFn_toLp.trans (hη i).symm)
    rw [heq]
    exact lp.memℓp η

theorem unboundedRealBorel_domain_iff (u : H) :
    u ∈ (unboundedRealBorel R hSA m hm).domain ↔
      RealMultiplierDomain R hSA m ((spectralUnitary R hSA).symm u) := by
  rw [LinearPMap.mem_domain_iff, realMultiplierDomain_iff_exists]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨(spectralUnitary R hSA).symm v, (unboundedRealBorel_mem_graph_iff R hSA m hm u v).mp hv⟩
  · rintro ⟨η, hη⟩
    refine ⟨spectralUnitary R hSA η, (unboundedRealBorel_mem_graph_iff R hSA m hm _ _).mpr ?_⟩
    simpa only [(spectralUnitary R hSA).symm_apply_apply] using hη

/-- Maximal domain: each actual product belongs to scalar L2 and the
squared output norms are summable over the unrestricted global family. -/
theorem unboundedRealBorel_domain_iff_sum_norm_sq (u : H) :
    u ∈ (unboundedRealBorel R hSA m hm).domain ↔
      ∃ h : ∀ i : SpectralIndex R hSA,
          MemLp (realProduct R hSA m ((spectralUnitary R hSA).symm u) i) 2
            (scalarMeasure R hSA (i : H)),
        Summable (fun i : SpectralIndex R hSA =>
          ‖(h i).toLp (realProduct R hSA m ((spectralUnitary R hSA).symm u) i)‖^2) := by
  rw [unboundedRealBorel_domain_iff]
  unfold RealMultiplierDomain
  apply exists_congr
  intro h
  simpa using (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (f := fun i : SpectralIndex R hSA =>
      (h i).toLp (realProduct R hSA m ((spectralUnitary R hSA).symm u) i)))

theorem unboundedRealBorel_action_ae (u : (unboundedRealBorel R hSA m hm).domain)
    (i : SpectralIndex R hSA) :
    ((spectralUnitary R hSA).symm (unboundedRealBorel R hSA m hm u)) i =ᵐ[scalarMeasure R hSA (i : H)]
      realProduct R hSA m ((spectralUnitary R hSA).symm (u : H)) i :=
  (unboundedRealBorel_mem_graph_iff R hSA m hm _ _).mp (LinearPMap.mem_graph _ u) i

end
end ImbalancedChen.Part3.GenericUnboundedRealBorelCalculus20261025a

