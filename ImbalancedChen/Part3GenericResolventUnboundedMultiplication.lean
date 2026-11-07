import ImbalancedChen.Part3GenericFriedrichsOperator
import ImbalancedChen.Part3GenericResolventScalarZeroAtom

/-!
# Native inverse-coordinate-minus-identity is unbounded lambda multiplication

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

On the genuine scalar L2 space of an arbitrary injective bounded
self-adjoint R, use the EXISTING native friedrichsR of the actual bounded
coordinate multiplier. Its native graph is proved exactly the a.e.
lambda multiplication graph, lambda(t)=(1-t)/t with its total value 0 at
t=0. The original operator domain is exactly MemLp(lambda*g)2. Native
action equals the true toLp lambda product. No parallel partial operator,
assumed multiplication graph, no-atom or domain supplier is introduced.

The zero fiber is proved null by the independent actual cyclic-indicator
theorem; no positivity or contraction of R is needed. Actual Gamma0 unitary
graph transport and scalar lambda-measure pushforward remain downstream.
-/

namespace ImbalancedChen.Part3.GenericResolventUnboundedMultiplication20261025a
noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.GenericFriedrichsOperator20261025a
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.GenericResolventCyclicIntertwining20261025a
open ImbalancedChen.Part3.GenericResolventScalarZeroAtom20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

def lambdaCoordinate (t : ResolventSpectrum R) : ℝ := (1 - (t : ℝ)) / (t : ℝ)

def lambdaProduct (f : H) (g : ScalarL2 R hSA f) (t : ResolventSpectrum R) : ℂ :=
  (lambdaCoordinate R t : ℂ) * g t

theorem lambdaCoordinate_zero {t : ResolventSpectrum R} (ht : (t : ℝ) = 0) :
    lambdaCoordinate R t = 0 := by simp only [lambdaCoordinate,ht,div_zero]

/-- The scalar algebra requires only nonzero coordinate, supplied almost
everywhere by genuine operator injectivity, rather than positivity. -/
theorem scalar_resolvent_equation_iff (t : ResolventSpectrum R) (ht : (t : ℝ) ≠ 0)
    (x y : ℂ) :
    ((t : ℝ) : ℂ) * (x + y) = x ↔ y = (lambdaCoordinate R t : ℂ) * x := by
  have htC : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hλ : (lambdaCoordinate R t : ℂ) = ((t : ℝ) : ℂ)⁻¹ - 1 := by
    simp only [lambdaCoordinate,Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_one]
    field_simp [htC] <;> ring
  rw [hλ]
  constructor
  · intro h
    have he := congrArg (fun z : ℂ => ((t : ℝ) : ℂ)⁻¹ * z) h
    rw [← mul_assoc,inv_mul_cancel₀ htC,one_mul] at he
    calc
      y = ((t : ℝ) : ℂ)⁻¹ * x - x := by linear_combination he
      _ = (((t : ℝ) : ℂ)⁻¹ - 1) * x := by ring
  · intro h
    rw [h]
    calc
      ((t : ℝ) : ℂ) * (x + (((t : ℝ) : ℂ)⁻¹ - 1) * x) =
          ((t : ℝ) : ℂ) * (((t : ℝ) : ℂ)⁻¹ * x) := by ring
      _ = x := by rw [← mul_assoc,mul_inv_cancel₀ htC,one_mul]

/-- The ACTUAL bounded coordinate equation is equivalent to the true
a.e. unbounded multiplier equation. Zero-fiber nullity is derived inside. -/
theorem coordinate_equation_iff_lambdaProduct (hRinj : Function.Injective R) (f : H)
    (g k : ScalarL2 R hSA f) :
    coordinateMultiplier R hSA f (g + k) = g ↔
      k =ᵐ[scalarMeasure R hSA f] lambdaProduct R hSA f g := by
  constructor
  · intro h
    have hm := coordinateMultiplier_coe_ae R hSA f (g + k)
    rw [h] at hm
    filter_upwards [hm,Lp.coeFn_add g k,scalarMeasure_ae_coordinate_ne_zero R hSA hRinj f]
      with t hM hadd ht
    have heq : ((t : ℝ) : ℂ) * (g t + k t) = g t := by
      simpa only [hadd] using hM.symm
    exact (scalar_resolvent_equation_iff R t ht (g t) (k t)).mp heq
  · intro h
    apply Lp.ext
    filter_upwards [coordinateMultiplier_coe_ae R hSA f (g + k),Lp.coeFn_add g k,h,
      scalarMeasure_ae_coordinate_ne_zero R hSA hRinj f] with t hM hadd hλ ht
    rw [hM,hadd]
    exact (scalar_resolvent_equation_iff R t ht (g t) (k t)).mpr hλ

/-- Exact graph of the EXISTING native inverse-M-minus-identity operator.
No new partial operator or separately assumed multiplication graph. -/
theorem coordinateFriedrichs_mem_graph_iff (hRinj : Function.Injective R) (f : H)
    {g k : ScalarL2 R hSA f} :
    (g,k) ∈ (friedrichsR (coordinateMultiplier R hSA f)).graph ↔
      k =ᵐ[scalarMeasure R hSA f] lambdaProduct R hSA f g := by
  rw [friedrichsR_mem_graph_iff (coordinateMultiplier R hSA f)
    (coordinateMultiplier_injective R hSA hRinj f)]
  exact coordinate_equation_iff_lambdaProduct R hSA hRinj f g k

/-- Native domain membership is EXACTLY integrability of lambda times
the actual L2 representative, not existence of an unspecified output. -/
theorem coordinateFriedrichs_domain_iff (hRinj : Function.Injective R) (f : H)
    (g : ScalarL2 R hSA f) :
    g ∈ (friedrichsR (coordinateMultiplier R hSA f)).domain ↔
      MemLp (lambdaProduct R hSA f g) 2 (scalarMeasure R hSA f) := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨k,hk⟩
    have hae := (coordinateFriedrichs_mem_graph_iff R hSA hRinj f).mp hk
    exact (memLp_congr_ae hae).mp (Lp.memLp k)
  · intro hg
    refine ⟨hg.toLp (lambdaProduct R hSA f g), ?_⟩
    apply (coordinateFriedrichs_mem_graph_iff R hSA hRinj f).mpr
    exact hg.coeFn_toLp

/-- The actual L2 output from the proved integrability condition. This
is a vector construction, not a second unbounded operator. -/
def lambdaMultiply (f : H) (g : ScalarL2 R hSA f)
    (hg : MemLp (lambdaProduct R hSA f g) 2 (scalarMeasure R hSA f)) :
    ScalarL2 R hSA f := hg.toLp (lambdaProduct R hSA f g)

theorem lambdaMultiply_coe_ae (f : H) (g : ScalarL2 R hSA f)
    (hg : MemLp (lambdaProduct R hSA f g) 2 (scalarMeasure R hSA f)) :
    lambdaMultiply R hSA f g hg =ᵐ[scalarMeasure R hSA f] lambdaProduct R hSA f g :=
  hg.coeFn_toLp

theorem coordinateFriedrichs_action_ae (hRinj : Function.Injective R) (f : H)
    (g : (friedrichsR (coordinateMultiplier R hSA f)).domain) :
    friedrichsR (coordinateMultiplier R hSA f) g =ᵐ[scalarMeasure R hSA f]
      lambdaProduct R hSA f (g : ScalarL2 R hSA f) :=
  (coordinateFriedrichs_mem_graph_iff R hSA hRinj f).mp (LinearPMap.mem_graph _ g)

/-- The native action is literally the actual toLp lambda product. -/
theorem coordinateFriedrichs_action_eq_lambdaMultiply (hRinj : Function.Injective R) (f : H)
    (g : (friedrichsR (coordinateMultiplier R hSA f)).domain) :
    friedrichsR (coordinateMultiplier R hSA f) g =
      lambdaMultiply R hSA f (g : ScalarL2 R hSA f)
        ((coordinateFriedrichs_domain_iff R hSA hRinj f _).mp g.property) := by
  apply Lp.ext
  exact (coordinateFriedrichs_action_ae R hSA hRinj f g).trans
    (lambdaMultiply_coe_ae R hSA f _ _).symm

end
end ImbalancedChen.Part3.GenericResolventUnboundedMultiplication20261025a
