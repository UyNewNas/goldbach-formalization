import ImbalancedChen.Part3GenericResolventGlobalSpectralAssembly
import ImbalancedChen.Part3GenericResolventUnboundedMultiplication

/-!
# Native global unbounded lambda multiplication on the genuine Hilbert sum

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

Use the existing Zorn-constructed generic scalar Hilbert sum and its
actual bounded diagonal coordinate multiplier D. On the existing native
friedrichsR D, the graph is EXACTLY the family of native fiber graphs,
and hence the family of a.e. lambda multiplier equations. All inputs and
outputs are genuine elements of the whole lp sum: no summability condition
is dropped in the graph equivalence.

The native domain is characterized explicitly by fiberwise MemLp of the
lambda products together with summability of their squared L2 norms. Both
implications and native action are proved. There is no new maximal family,
parallel unbounded operator, assumed global domain, or zero-atom premise.
Actual Gamma0 unitary binding remains downstream.
-/

namespace ImbalancedChen.Part3.GenericResolventGlobalUnboundedMultiplication20261025a
noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.GenericFriedrichsOperator20261025a
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.GenericResolventCyclicIntertwining20261025a
open ImbalancedChen.Part3.GenericResolventScalarZeroAtom20261025a
open ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a
open ImbalancedChen.Part3.GenericResolventUnboundedMultiplication20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

/-- Every actual fiber multiplier is injective, from the actual cyclic
intertwining with the specified injective bounded R. -/
theorem fiberCoordinate_injective (hRinj : Function.Injective R) (i : SpectralIndex R hSA) :
    Function.Injective (coordinateMultiplier R hSA (i : H)) :=
  coordinateMultiplier_injective R hSA hRinj (i : H)

theorem diagonalResolvent_injective (hRinj : Function.Injective R) :
    Function.Injective (diagonalResolvent R hSA) := by
  intro g k hgk
  apply lp.ext
  funext i
  apply fiberCoordinate_injective R hSA hRinj i
  have hi := congrArg (fun x : SpectralSum R hSA => x i) hgk
  simpa only [diagonalResolvent_apply] using hi

/-- Exact native global graph versus native fiber graphs. g and k are
already global lp vectors, so this equivalence preserves ALL norm sums. -/
theorem globalFriedrichs_mem_graph_iff_fiberGraph (hRinj : Function.Injective R)
    {g k : SpectralSum R hSA} :
    (g,k) ∈ (friedrichsR (diagonalResolvent R hSA)).graph ↔
      ∀ i : SpectralIndex R hSA,
        (g i,k i) ∈ (friedrichsR (coordinateMultiplier R hSA (i : H))).graph := by
  constructor
  · intro hg i
    apply (friedrichsR_mem_graph_iff (coordinateMultiplier R hSA (i : H))
      (fiberCoordinate_injective R hSA hRinj i)).mpr
    have hD := (friedrichsR_mem_graph_iff (diagonalResolvent R hSA)
      (diagonalResolvent_injective R hSA hRinj)).mp hg
    have hi := congrArg (fun x : SpectralSum R hSA => x i) hD
    simpa only [diagonalResolvent_apply,lp.coeFn_add,Pi.add_apply] using hi
  · intro hg
    apply (friedrichsR_mem_graph_iff (diagonalResolvent R hSA)
      (diagonalResolvent_injective R hSA hRinj)).mpr
    apply lp.ext
    funext i
    have hi := (friedrichsR_mem_graph_iff (coordinateMultiplier R hSA (i : H))
      (fiberCoordinate_injective R hSA hRinj i)).mp (hg i)
    simpa only [diagonalResolvent_apply,lp.coeFn_add,Pi.add_apply] using hi

def FamilyLambdaGraph (g k : SpectralSum R hSA) : Prop :=
  ∀ i : SpectralIndex R hSA, k i =ᵐ[scalarMeasure R hSA (i : H)]
    lambdaProduct R hSA (i : H) (g i)

/-- The true global native operator graph is literally a.e. lambda
multiplication on every genuine scalar-measure fiber. -/
theorem globalFriedrichs_mem_graph_iff_lambda (hRinj : Function.Injective R)
    {g k : SpectralSum R hSA} :
    (g,k) ∈ (friedrichsR (diagonalResolvent R hSA)).graph ↔ FamilyLambdaGraph R hSA g k := by
  rw [globalFriedrichs_mem_graph_iff_fiberGraph R hSA hRinj]
  constructor
  · intro h i
    exact (coordinateFriedrichs_mem_graph_iff R hSA hRinj (i : H)).mp (h i)
  · intro h i
    exact (coordinateFriedrichs_mem_graph_iff R hSA hRinj (i : H)).mpr (h i)

/-- Explicit whole-sum domain: every product is genuinely in scalar L2,
and the resulting actual toLp outputs form a genuine lp family. -/
def FamilyLambdaDomain (g : SpectralSum R hSA) : Prop :=
  ∃ h : ∀ i : SpectralIndex R hSA,
      MemLp (lambdaProduct R hSA (i : H) (g i)) 2 (scalarMeasure R hSA (i : H)),
    Memℓp (fun i : SpectralIndex R hSA =>
      (h i).toLp (lambdaProduct R hSA (i : H) (g i))) 2

theorem familyLambdaDomain_iff_sum_norm_sq (g : SpectralSum R hSA) :
    FamilyLambdaDomain R hSA g ↔
      ∃ h : ∀ i : SpectralIndex R hSA,
          MemLp (lambdaProduct R hSA (i : H) (g i)) 2 (scalarMeasure R hSA (i : H)),
        Summable (fun i : SpectralIndex R hSA =>
          ‖(h i).toLp (lambdaProduct R hSA (i : H) (g i))‖ ^ 2) := by
  unfold FamilyLambdaDomain
  apply exists_congr
  intro h
  simpa using (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (f := fun i : SpectralIndex R hSA => (h i).toLp (lambdaProduct R hSA (i : H) (g i))))

/-- Actual global output construction in one direction; in the other,
the existing output's lp norm proves the missing global square sum. -/
theorem familyLambdaDomain_iff_exists_graph (g : SpectralSum R hSA) :
    FamilyLambdaDomain R hSA g ↔ ∃ k : SpectralSum R hSA, FamilyLambdaGraph R hSA g k := by
  constructor
  · rintro ⟨h,hsum⟩
    refine ⟨⟨fun i => (h i).toLp (lambdaProduct R hSA (i : H) (g i)),hsum⟩,?_⟩
    intro i
    exact (h i).coeFn_toLp
  · rintro ⟨k,hk⟩
    have h : ∀ i : SpectralIndex R hSA,
        MemLp (lambdaProduct R hSA (i : H) (g i)) 2 (scalarMeasure R hSA (i : H)) := by
      intro i
      exact (memLp_congr_ae (hk i)).mp (Lp.memLp (k i))
    refine ⟨h,?_⟩
    have heq : (fun i : SpectralIndex R hSA =>
        (h i).toLp (lambdaProduct R hSA (i : H) (g i))) = (fun i => k i) := by
      funext i
      apply Lp.ext
      exact (h i).coeFn_toLp.trans (hk i).symm
    rw [heq]
    exact lp.memℓp k

/-- The ORIGINAL native global domain is exactly the explicit fiber
integrability plus global lp norm condition, proved in both directions. -/
theorem globalFriedrichs_domain_iff (hRinj : Function.Injective R) (g : SpectralSum R hSA) :
    g ∈ (friedrichsR (diagonalResolvent R hSA)).domain ↔ FamilyLambdaDomain R hSA g := by
  rw [LinearPMap.mem_domain_iff,familyLambdaDomain_iff_exists_graph]
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k,(globalFriedrichs_mem_graph_iff_lambda R hSA hRinj).mp hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,(globalFriedrichs_mem_graph_iff_lambda R hSA hRinj).mpr hk⟩

/-- The requested explicit summability characterization, without any
assumed global-domain supplier or countability restriction on the index. -/
theorem globalFriedrichs_domain_iff_sum_norm_sq (hRinj : Function.Injective R)
    (g : SpectralSum R hSA) :
    g ∈ (friedrichsR (diagonalResolvent R hSA)).domain ↔
      ∃ h : ∀ i : SpectralIndex R hSA,
          MemLp (lambdaProduct R hSA (i : H) (g i)) 2 (scalarMeasure R hSA (i : H)),
        Summable (fun i : SpectralIndex R hSA =>
          ‖(h i).toLp (lambdaProduct R hSA (i : H) (g i))‖ ^ 2) :=
  (globalFriedrichs_domain_iff R hSA hRinj g).trans (familyLambdaDomain_iff_sum_norm_sq R hSA g)

theorem globalFriedrichs_action_ae (hRinj : Function.Injective R)
    (g : (friedrichsR (diagonalResolvent R hSA)).domain) (i : SpectralIndex R hSA) :
    friedrichsR (diagonalResolvent R hSA) g i =ᵐ[scalarMeasure R hSA (i : H)]
      lambdaProduct R hSA (i : H) ((g : SpectralSum R hSA) i) :=
  (globalFriedrichs_mem_graph_iff_lambda R hSA hRinj).mp (LinearPMap.mem_graph _ g) i

end
end ImbalancedChen.Part3.GenericResolventGlobalUnboundedMultiplication20261025a
