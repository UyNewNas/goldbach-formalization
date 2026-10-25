import ImbalancedChen.Part3RadialEnergyTripleCompletion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual closed radial energy domain and its shifted Riesz solution.
The ambient space is PiLp 2, so it has the genuine Hilbert energy norm,
not the max norm of an ordinary Cartesian product. For each kappa>0 the
core vector is (kappa*f,f',exp(r)f). The closed complex span of these
actual vectors is the form domain. The physical projection is injective
and has dense range, by the real derivative and exponential graph proofs.

Taking the adjoint of that actual physical embedding constructs the
unique form solution of (-d²/dr²+exp(2r)+kappa²)u=F. The complete
three-coordinate variational equation is proved. No assumed form,
abstract inverse or closedness/density premise enters the construction.
Equality of the physical solution with an I/K integral remains separate.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open MeasureTheory Set

def radialWeakDerivativeSubmodule : Submodule ℂ (RadialL2 × RadialL2) where
  carrier := radialWeakDerivativeGraph
  zero_mem' := by intro T; simp
  add_mem' := by
    intro p q hp hq T
    change inner ℂ (p.2 + q.2) (radialCoreL2 T) =
      -inner ℂ (p.1 + q.1) (radialDerivativeL2 T)
    rw [inner_add_left, inner_add_left, hp T, hq T]
    ring
  smul_mem' := by
    intro c p hp T
    change inner ℂ (c • p.2) (radialCoreL2 T) =
      -inner ℂ (c • p.1) (radialDerivativeL2 T)
    rw [inner_smul_left, inner_smul_left, hp T]
    ring

def radialExponentialSubmodule : Submodule ℂ (RadialL2 × RadialL2) where
  carrier := exponentialMultiplierGraph
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with r hr
    simp [exponentialProduct, hr]
  add_mem' := by
    intro p q hp hq
    filter_upwards [hp, hq, Lp.coeFn_add p.1 q.1, Lp.coeFn_add p.2 q.2]
      with r hrP hrQ hrIn hrOut
    rw [hrOut, hrIn, hrP, hrQ]
    simp only [exponentialProduct]
    ring
  smul_mem' := by
    intro c p hp
    filter_upwards [hp, Lp.coeFn_smul c p.1, Lp.coeFn_smul c p.2]
      with r hrP hrIn hrOut
    rw [hrOut, hrIn, hrP]
    simp only [exponentialProduct, Pi.smul_apply, smul_eq_mul]
    ring

abbrev RadialEnergyHilbert := PiLp 2 (fun _ : Fin 3 => RadialL2)

def energyPhysicalCoordinate (kappa : ℝ) : RadialEnergyHilbert →L[ℂ] RadialL2 :=
  (kappa⁻¹ : ℂ) • PiLp.proj 2 (fun _ : Fin 3 => RadialL2) 0

def energyDerivativeCoordinate : RadialEnergyHilbert →L[ℂ] RadialL2 :=
  PiLp.proj 2 (fun _ : Fin 3 => RadialL2) 1

def energyExponentialCoordinate : RadialEnergyHilbert →L[ℂ] RadialL2 :=
  PiLp.proj 2 (fun _ : Fin 3 => RadialL2) 2

def radialEnergyCoreVector (kappa : ℝ) (T : RadialTest) : RadialEnergyHilbert :=
  WithLp.toLp 2 ![(kappa : ℂ) • radialCoreL2 T,
    radialDerivativeL2 T, radialExponentialL2 T]

theorem energyPhysical_core (kappa : ℝ) (hkappa : 0 < kappa) (T : RadialTest) :
    energyPhysicalCoordinate kappa (radialEnergyCoreVector kappa T) = radialCoreL2 T := by
  have he : (kappa⁻¹ : ℂ) * (kappa : ℂ) = 1 := by
    exact_mod_cast inv_mul_cancel₀ hkappa.ne'
  change (kappa⁻¹ : ℂ) • ((kappa : ℂ) • radialCoreL2 T) = _
  rw [smul_smul, he, one_smul]

theorem energy_coordinate_zero (kappa : ℝ) (hkappa : 0 < kappa)
    (p : RadialEnergyHilbert) : p 0 = (kappa : ℂ) • energyPhysicalCoordinate kappa p := by
  have he : (kappa : ℂ) * (kappa⁻¹ : ℂ) = 1 := by
    exact_mod_cast mul_inv_cancel₀ hkappa.ne'
  change p 0 = (kappa : ℂ) • ((kappa⁻¹ : ℂ) • p 0)
  rw [smul_smul, he, one_smul]

def radialEnergyGood (kappa : ℝ) : Submodule ℂ RadialEnergyHilbert :=
  (radialWeakDerivativeSubmodule.comap
    ((energyPhysicalCoordinate kappa).prod energyDerivativeCoordinate).toLinearMap) ⊓
  (radialExponentialSubmodule.comap
    ((energyPhysicalCoordinate kappa).prod energyExponentialCoordinate).toLinearMap)

theorem isClosed_radialEnergyGood (kappa : ℝ) :
    IsClosed (radialEnergyGood kappa : Set RadialEnergyHilbert) :=
  (isClosed_radialWeakDerivativeGraph.preimage
    ((energyPhysicalCoordinate kappa).prod energyDerivativeCoordinate).continuous).inter
  (isClosed_exponentialMultiplierGraph.preimage
    ((energyPhysicalCoordinate kappa).prod energyExponentialCoordinate).continuous)

def radialEnergyCoreSpan (kappa : ℝ) : Submodule ℂ RadialEnergyHilbert :=
  Submodule.span ℂ (Set.range (radialEnergyCoreVector kappa))

def radialClosedEnergyDomain (kappa : ℝ) : Submodule ℂ RadialEnergyHilbert :=
  (radialEnergyCoreSpan kappa).topologicalClosure

theorem radialClosedEnergyDomain_le_good (kappa : ℝ) (hkappa : 0 < kappa) :
    radialClosedEnergyDomain kappa ≤ radialEnergyGood kappa := by
  apply (radialEnergyCoreSpan kappa).topologicalClosure_minimal _
    (isClosed_radialEnergyGood kappa)
  apply Submodule.span_le.2
  rintro _ ⟨T, rfl⟩
  constructor
  · change (energyPhysicalCoordinate kappa (radialEnergyCoreVector kappa T),
      radialDerivativeL2 T) ∈ radialWeakDerivativeGraph
    rw [energyPhysical_core kappa hkappa T]
    exact radialWeakDerivativeGraph_core T
  · change (radialExponentialL2 T : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)]
      exponentialProduct (energyPhysicalCoordinate kappa (radialEnergyCoreVector kappa T))
    rw [energyPhysical_core kappa hkappa T]
    exact radial_core_exponential_relation T

instance radialClosedEnergyDomain_complete (kappa : ℝ) :
    CompleteSpace (radialClosedEnergyDomain kappa) := inferInstance

def radialPhysicalEmbedding (kappa : ℝ) :
    radialClosedEnergyDomain kappa →L[ℂ] RadialL2 :=
  (energyPhysicalCoordinate kappa).comp (radialClosedEnergyDomain kappa).subtypeL

def radialClosedDerivative (kappa : ℝ) :
    radialClosedEnergyDomain kappa →L[ℂ] RadialL2 :=
  energyDerivativeCoordinate.comp (radialClosedEnergyDomain kappa).subtypeL

def radialClosedExponential (kappa : ℝ) :
    radialClosedEnergyDomain kappa →L[ℂ] RadialL2 :=
  energyExponentialCoordinate.comp (radialClosedEnergyDomain kappa).subtypeL

theorem radialPhysicalEmbedding_injective (kappa : ℝ) (hkappa : 0 < kappa) :
    Function.Injective (radialPhysicalEmbedding kappa) := by
  intro p q heq
  have hp := radialClosedEnergyDomain_le_good kappa hkappa p.2
  have hq := radialClosedEnergyDomain_le_good kappa hkappa q.2
  have hd : energyDerivativeCoordinate p = energyDerivativeCoordinate q := by
    have hq' := hq.1
    change (energyPhysicalCoordinate kappa q, energyDerivativeCoordinate q) ∈
      radialWeakDerivativeGraph at hq'
    change energyPhysicalCoordinate kappa p = energyPhysicalCoordinate kappa q at heq
    rw [← heq] at hq'
    exact radialWeakDerivativeGraph_right_unique hp.1 hq'
  have he : energyExponentialCoordinate p = energyExponentialCoordinate q := by
    apply Lp.ext
    filter_upwards [hp.2, hq.2] with r hrP hrQ
    change energyPhysicalCoordinate kappa p = energyPhysicalCoordinate kappa q at heq
    rw [hrP, hrQ, heq]
  apply Subtype.ext
  ext i
  fin_cases i
  · rw [energy_coordinate_zero kappa hkappa, energy_coordinate_zero kappa hkappa]
    exact congrArg (fun F : RadialL2 => (kappa : ℂ) • F) heq
  · exact hd
  · exact he

theorem radialPhysicalEmbedding_denseRange (kappa : ℝ) (hkappa : 0 < kappa) :
    DenseRange (radialPhysicalEmbedding kappa) := by
  apply radialCoreL2_range_dense.mono
  rintro F ⟨T, rfl⟩
  refine ⟨⟨radialEnergyCoreVector kappa T,
    (radialEnergyCoreSpan kappa).le_topologicalClosure
      (Submodule.subset_span ⟨T, rfl⟩)⟩, ?_⟩
  exact energyPhysical_core kappa hkappa T

/-- The actual Hilbert norm has exactly the shifted physical energy
pairing, including all off-diagonal terms. -/
theorem radialClosedEnergy_inner (kappa : ℝ) (hkappa : 0 < kappa)
    (u v : radialClosedEnergyDomain kappa) :
    inner ℂ u v =
      (kappa ^ 2 : ℂ) * inner ℂ (radialPhysicalEmbedding kappa u)
        (radialPhysicalEmbedding kappa v) +
      inner ℂ (radialClosedDerivative kappa u) (radialClosedDerivative kappa v) +
      inner ℂ (radialClosedExponential kappa u) (radialClosedExponential kappa v) := by
  change inner ℂ (u : RadialEnergyHilbert) (v : RadialEnergyHilbert) = _
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_succ]
  rw [energy_coordinate_zero kappa hkappa (u : RadialEnergyHilbert),
    energy_coordinate_zero kappa hkappa (v : RadialEnergyHilbert)]
  simp only [inner_smul_left, inner_smul_right, radialPhysicalEmbedding,
    radialClosedDerivative, radialClosedExponential, energyDerivativeCoordinate,
    energyExponentialCoordinate, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

/-- Constructed Riesz solution, not a parameter asserting an inverse. -/
def radialFormRieszSolution (kappa : ℝ) :
    RadialL2 →L[ℂ] radialClosedEnergyDomain kappa :=
  (radialPhysicalEmbedding kappa).adjoint

def radialShiftedVariationalInverse (kappa : ℝ) : RadialL2 →L[ℂ] RadialL2 :=
  (radialPhysicalEmbedding kappa).comp (radialFormRieszSolution kappa)

/-- Actual radial shifted weak equation against every element of the
actual completed energy domain. -/
theorem radialFormRieszSolution_variational (kappa : ℝ) (hkappa : 0 < kappa)
    (F : RadialL2) (v : radialClosedEnergyDomain kappa) :
    (kappa ^ 2 : ℂ) * inner ℂ (radialShiftedVariationalInverse kappa F)
        (radialPhysicalEmbedding kappa v) +
      inner ℂ (radialClosedDerivative kappa (radialFormRieszSolution kappa F))
        (radialClosedDerivative kappa v) +
      inner ℂ (radialClosedExponential kappa (radialFormRieszSolution kappa F))
        (radialClosedExponential kappa v) =
      inner ℂ F (radialPhysicalEmbedding kappa v) := by
  rw [← radialClosedEnergy_inner kappa hkappa]
  exact ContinuousLinearMap.adjoint_inner_left (radialPhysicalEmbedding kappa) v F

theorem radialFormRieszSolution_unique (kappa : ℝ) (F : RadialL2)
    (u : radialClosedEnergyDomain kappa)
    (hu : ∀ v : radialClosedEnergyDomain kappa,
      inner ℂ u v = inner ℂ F (radialPhysicalEmbedding kappa v)) :
    u = radialFormRieszSolution kappa F := by
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [inner_sub_left, hu,
    ContinuousLinearMap.adjoint_inner_left (radialPhysicalEmbedding kappa)
      (u - radialFormRieszSolution kappa F) F, sub_self]

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
