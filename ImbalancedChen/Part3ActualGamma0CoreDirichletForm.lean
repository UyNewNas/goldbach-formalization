import ImbalancedChen.Part3ActualGamma0PoincareEnergy
import ImbalancedChen.Part3ActualDirichletCauchySchwarz

/-!
# The canonical geometric Dirichlet form on the actual Gamma0 smooth core

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The form is defined by the orbit lift of the literal coordinate gradients
of the existing canonical smooth automorphic representatives. Choosing a
finite seed family is used only in proofs of invariance, L1 and Green;
the definition is independent of any such family. The actual operator
pairing is proved equal to the geometric integral on the entire core.

A transient PreInnerProductSpace.Core, with no replacement of the
existing quotient-L2 norm, reuses the pinned Cauchy--Schwarz proof for the
resulting positive semidefinite geometric form. No completion or
Friedrichs operator is constructed here.
-/

namespace ImbalancedChen.Part3.ActualGamma0CoreDirichletForm20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorQuotientL2Core20261025a
open ImbalancedChen.Part3.Gamma0CompactSeedQuotientL2Budget20261025a
open ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientMaassGraph20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothCoreSymmetry20261025a
open ImbalancedChen.Part3.Gamma0SmoothCoreFinitePoincareRepresentation20261025a
open ImbalancedChen.Part3.ActualMobiusDirichletCovariance20261025a
open ImbalancedChen.Part3.ActualDirichletCauchySchwarz20261025a
open ImbalancedChen.Part3.ActualGamma0PoincareEnergy20261025a

/-- The existing canonical H-representative is the actual Poincare
function of ANY finite family representing that same quotient-L2 input. -/
theorem coreRepresentative_eq_finite_family (N : ℕ) [NeZero N] (u : smoothCore N)
    {n : ℕ} (T : Fin n → SmoothCompactTensor)
    (hT : (u : QuotientL2 N) = smoothQuotientPoincareL2 N Finset.univ T) :
    coreRepresentative N u =
      finiteCompactTensorPoincare N Finset.univ (fun i => (T i).toCompactTensor) := by
  let s : SmoothSeed := ⟨n,T⟩
  have hu : u = seedCoreElement N s := Subtype.ext hT
  rw [hu,coreRepresentative_seed]
  rfl

/-- Literal first-gradient density of the canonical smooth H-realizations. -/
def coreDirichletH (N : ℕ) [NeZero N] (u v : smoothCore N) (z : UpperHalfPlane) : ℂ :=
  hyperbolicChartDirichlet (extendUpper (coreRepresentative N u))
    (extendUpper (coreRepresentative N v)) (z.re,z.im)

theorem coreDirichletH_gamma0_invariant (N : ℕ) [NeZero N] (u v : smoothCore N)
    (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    coreDirichletH N u v (γ • z) = coreDirichletH N u v z := by
  obtain ⟨n,T,hT⟩ := exists_finite_poincare_representation N u
  obtain ⟨m,U,hU⟩ := exists_finite_poincare_representation N v
  unfold coreDirichletH
  rw [coreRepresentative_eq_finite_family N u T hT,
    coreRepresentative_eq_finite_family N v U hU]
  exact poincareEnergyH_gamma0_invariant N Finset.univ (fun i => (T i).toCompactTensor)
    Finset.univ (fun i => (U i).toCompactTensor) γ z

/-- The geometric density descends to the actual orbit quotient. Its
definition mentions only the canonical core representatives, not seeds. -/
def coreDirichletDensity (N : ℕ) [NeZero N] (u v : smoothCore N) : Gamma0OrbitSpace N → ℂ :=
  Quotient.lift (coreDirichletH N u v) (by
    intro z w hzw
    obtain ⟨γ,hγ⟩ := MulAction.orbitRel_apply.mp hzw
    rw [← hγ]
    exact coreDirichletH_gamma0_invariant N u v γ w)

@[simp] theorem coreDirichletDensity_projection (N : ℕ) [NeZero N] (u v : smoothCore N)
    (z : UpperHalfPlane) :
    coreDirichletDensity N u v (orbitProjection N z) = coreDirichletH N u v z := rfl

theorem coreDirichletDensity_eq_finite_family (N : ℕ) [NeZero N] (u v : smoothCore N)
    {n m : ℕ} (T : Fin n → SmoothCompactTensor) (U : Fin m → SmoothCompactTensor)
    (hT : (u : QuotientL2 N) = smoothQuotientPoincareL2 N Finset.univ T)
    (hU : (v : QuotientL2 N) = smoothQuotientPoincareL2 N Finset.univ U) :
    coreDirichletDensity N u v =
      quotientPoincareEnergy N Finset.univ (fun i => (T i).toCompactTensor)
        Finset.univ (fun i => (U i).toCompactTensor) := by
  funext q
  refine Quotient.inductionOn q (fun z => ?_)
  change coreDirichletH N u v z = _
  unfold coreDirichletH
  rw [coreRepresentative_eq_finite_family N u T hT,
    coreRepresentative_eq_finite_family N v U hU]
  rfl

/-- Mixed energy is L1 on the original canonical quotient measure for
every pair of actual core vectors. No diagonal-energy supplier is assumed. -/
theorem coreDirichletDensity_integrable (N : ℕ) [NeZero N] (u v : smoothCore N) :
    Integrable (coreDirichletDensity N u v) (carrierPushforward N) := by
  obtain ⟨n,T,hT⟩ := exists_finite_poincare_representation N u
  obtain ⟨m,U,hU⟩ := exists_finite_poincare_representation N v
  rw [coreDirichletDensity_eq_finite_family N u v T U hT hU]
  exact quotientPoincareEnergy_integrable N Finset.univ (fun i => (T i).toCompactTensor)
    Finset.univ (fun i => (U i).toCompactTensor)

/-- Canonical geometric Dirichlet form on the original actual smooth core. -/
def coreDirichletForm (N : ℕ) [NeZero N] (u v : smoothCore N) : ℂ :=
  ∫ q, coreDirichletDensity N u v q ∂carrierPushforward N

/-- The operator-defined pairing used by the energy completion is
proved to be the actual geometric quotient gradient integral. -/
theorem coreDirichletForm_eq_operatorPair (N : ℕ) [NeZero N] (u v : smoothCore N) :
    coreDirichletForm N u v = inner ℂ (u : QuotientL2 N) (actualCoreLaplacian N v) := by
  obtain ⟨n,T,hT,hAT⟩ := exists_finite_input_output_family N u
  obtain ⟨m,U,hU,hAU⟩ := exists_finite_input_output_family N v
  unfold coreDirichletForm
  rw [coreDirichletDensity_eq_finite_family N u v T U hT hU,hT,hAU]
  exact (actual_quotient_poincare_energy N Finset.univ (fun i => (T i).toCompactTensor)
    Finset.univ (fun i => (U i).toCompactTensor)).symm

theorem coreDirichletDensity_star (N : ℕ) [NeZero N] (u v : smoothCore N)
    (q : Gamma0OrbitSpace N) :
    star (coreDirichletDensity N u v q) = coreDirichletDensity N v u q := by
  refine Quotient.inductionOn q (fun z => ?_)
  exact hyperbolicChartDirichlet_star _ _ (z.re,z.im)

theorem coreDirichletDensity_self_re_nonneg (N : ℕ) [NeZero N] (u : smoothCore N)
    (q : Gamma0OrbitSpace N) : 0 ≤ (coreDirichletDensity N u u q).re := by
  refine Quotient.inductionOn q (fun z => ?_)
  exact hyperbolicChartDirichlet_self_re_nonneg _ (z.re,z.im)

theorem coreDirichletForm_self_re_nonneg (N : ℕ) [NeZero N] (u : smoothCore N) :
    0 ≤ (coreDirichletForm N u u).re := by
  unfold coreDirichletForm
  rw [← integral_re (coreDirichletDensity_integrable N u u)]
  exact integral_nonneg (coreDirichletDensity_self_re_nonneg N u)

theorem coreDirichletForm_star (N : ℕ) [NeZero N] (u v : smoothCore N) :
    star (coreDirichletForm N u v) = coreDirichletForm N v u := by
  rw [coreDirichletForm_eq_operatorPair,coreDirichletForm_eq_operatorPair,
    ← actualCoreLaplacian_symmetric N v u]
  exact inner_conj_symm (actualCoreLaplacian N v) (u : QuotientL2 N)

theorem coreDirichletForm_add_left (N : ℕ) [NeZero N] (u v w : smoothCore N) :
    coreDirichletForm N (u+v) w = coreDirichletForm N u w + coreDirichletForm N v w := by
  simp only [coreDirichletForm_eq_operatorPair,Submodule.coe_add,inner_add_left]

theorem coreDirichletForm_add_right (N : ℕ) [NeZero N] (u v w : smoothCore N) :
    coreDirichletForm N u (v+w) = coreDirichletForm N u v + coreDirichletForm N u w := by
  simp only [coreDirichletForm_eq_operatorPair,map_add,inner_add_right]

theorem coreDirichletForm_smul_left (N : ℕ) [NeZero N] (c : ℂ) (u v : smoothCore N) :
    coreDirichletForm N (c • u) v = star c * coreDirichletForm N u v := by
  simp only [coreDirichletForm_eq_operatorPair,Submodule.coe_smul,inner_smul_left]

theorem coreDirichletForm_smul_right (N : ℕ) [NeZero N] (c : ℂ) (u v : smoothCore N) :
    coreDirichletForm N u (c • v) = c * coreDirichletForm N u v := by
  simp only [coreDirichletForm_eq_operatorPair,map_smul,inner_smul_right]

/-- A positive semidefinite pre-inner core for the ACTUAL geometric
form. This object installs no new norm or global inner-product instance. -/
def coreDirichletPreInner (N : ℕ) [NeZero N] : PreInnerProductSpace.Core ℂ (smoothCore N) where
  inner := coreDirichletForm N
  conj_inner_symm u v := coreDirichletForm_star N v u
  re_inner_nonneg := coreDirichletForm_self_re_nonneg N
  add_left := coreDirichletForm_add_left N
  smul_left u v c := coreDirichletForm_smul_left N c u v

/-- Global Cauchy--Schwarz for the actual quotient Dirichlet form,
obtained from its proved positivity/Hermitian structure. -/
theorem coreDirichletForm_normSq_le (N : ℕ) [NeZero N] (u v : smoothCore N) :
    Complex.normSq (coreDirichletForm N u v) ≤
      (coreDirichletForm N u u).re * (coreDirichletForm N v v).re := by
  have h : ‖coreDirichletForm N u v‖ * ‖coreDirichletForm N v u‖ ≤
      (coreDirichletForm N u u).re * (coreDirichletForm N v v).re :=
    InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) (F := smoothCore N)
      (c := coreDirichletPreInner N) u v
  have hnorm : ‖coreDirichletForm N v u‖ = ‖coreDirichletForm N u v‖ := by
    rw [← coreDirichletForm_star N u v,norm_star]
  rw [hnorm] at h
  simpa only [Complex.normSq_eq_norm_sq,pow_two] using h

end
end ImbalancedChen.Part3.ActualGamma0CoreDirichletForm20261025a
