import ImbalancedChen.Part3RadialSmoothCoreDerivativeClosure
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The literal radial C-infinity core is embedded in the actual Hilbert
triple (f,f',exp(r)f) over L2(dr). Its topological closure is a genuine
closed subset of that product. The physical first projection is proved
injective on this completion and has dense range in actual L2(dr).

The proof uses the independently proved closed weak derivative and
closed unbounded exponential multiplication graphs. No hClosed,
hDensity or representation-independence assumption is supplied.
An associated self-adjoint realization and its Green resolvent are not
asserted. The linear closed-form-domain construction remains separate.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open Set MeasureTheory

abbrev RadialHilbertTriple := RadialL2 × (RadialL2 × RadialL2)

def radialFormCoreTriple (T : RadialTest) : RadialHilbertTriple :=
  (radialCoreL2 T, radialDerivativeL2 T, radialExponentialL2 T)

def radialFormCompletion : Set RadialHilbertTriple :=
  closure (Set.range radialFormCoreTriple)

theorem isClosed_radialFormCompletion : IsClosed radialFormCompletion := isClosed_closure

theorem completion_mem_weakDerivative {p : RadialHilbertTriple}
    (hp : p ∈ radialFormCompletion) :
    (p.1, p.2.1) ∈ radialWeakDerivativeGraph := by
  let P : RadialHilbertTriple → RadialL2 × RadialL2 := fun q => (q.1, q.2.1)
  have hP : Continuous P := continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hc : IsClosed (P ⁻¹' radialWeakDerivativeGraph) :=
    isClosed_radialWeakDerivativeGraph.preimage hP
  apply (closure_minimal (t := P ⁻¹' radialWeakDerivativeGraph) ?_ hc) hp
  rintro _ ⟨T, rfl⟩
  exact radialWeakDerivativeGraph_core T

theorem completion_mem_exponentialGraph {p : RadialHilbertTriple}
    (hp : p ∈ radialFormCompletion) :
    (p.1, p.2.2) ∈ exponentialMultiplierGraph := by
  let P : RadialHilbertTriple → RadialL2 × RadialL2 := fun q => (q.1, q.2.2)
  have hP : Continuous P := continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  have hc : IsClosed (P ⁻¹' exponentialMultiplierGraph) :=
    isClosed_exponentialMultiplierGraph.preimage hP
  apply (closure_minimal (t := P ⁻¹' exponentialMultiplierGraph) ?_ hc) hp
  rintro _ ⟨T, rfl⟩
  exact radial_core_exponential_relation T

/-- Both energy coordinates are determined by the physical radial L2
class on the actual graph completion. -/
theorem radialFormCompletion_physical_projection_injective :
    Set.InjOn (Prod.fst : RadialHilbertTriple → RadialL2) radialFormCompletion := by
  intro p hp q hq hfirst
  have hDp := completion_mem_weakDerivative hp
  have hDq := completion_mem_weakDerivative hq
  have hD : p.2.1 = q.2.1 := by
    rw [← hfirst] at hDq
    exact radialWeakDerivativeGraph_right_unique hDp hDq
  have hEp := completion_mem_exponentialGraph hp
  have hEq := completion_mem_exponentialGraph hq
  have hE : p.2.2 = q.2.2 := by
    apply Lp.ext
    filter_upwards [hEp, hEq] with r hrP hrQ
    rw [hrP, hrQ, hfirst]
  exact Prod.ext hfirst (Prod.ext hD hE)

/-- The physical range contains the actual dense compact smooth radial
core, with no density assumption about the completion. -/
theorem radialFormCompletion_dense_physical_range :
    Dense ((Prod.fst : RadialHilbertTriple → RadialL2) '' radialFormCompletion) := by
  apply radialCoreL2_range_dense.mono
  rintro F ⟨T, rfl⟩
  exact ⟨radialFormCoreTriple T, subset_closure ⟨T, rfl⟩, rfl⟩

/-- The potential coordinate is precisely exp(2r)|f(r)|² after squaring,
not the unrelated constant cusp-mode quarter potential. -/
theorem radial_exponential_coordinate_square (f : ℝ → ℂ) (r : ℝ) :
    ‖exponentialProduct f r‖ ^ 2 = Real.exp (2 * r) * ‖f r‖ ^ 2 := by
  have he : Real.exp (2 * r) = Real.exp r ^ 2 := by
    rw [show 2 * r = r + r by ring, Real.exp_add, pow_two]
  rw [exponentialProduct, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos r), mul_pow, he]

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
