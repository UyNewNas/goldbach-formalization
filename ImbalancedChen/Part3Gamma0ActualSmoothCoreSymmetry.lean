import ImbalancedChen.Part3Gamma0ActualSmoothQuotientMaassGraph
import ImbalancedChen.Part3ActualGamma0PoincareGreen

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Symmetry on the ENTIRE actual smooth quotient core, not only a selected
seed family. The starting matrix identity is the genuine actual quotient
Poincare Green theorem for canonical quotient L2 input/output vectors.
Two finite-span inductions and the already proved complex linear operator
extend that identity to every pair of core vectors. Neither density,
nonnegative energy, an abstract symmetry field nor a desired Green premise
is assumed. This does not claim a closed or self-adjoint extension.
-/

namespace ImbalancedChen.Part3.Gamma0ActualSmoothCoreSymmetry20261025a

noncomputable section
open MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorQuotientL2Core20261025a
open ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientMaassGraph20261025a
open ImbalancedChen.Part3.ActualGamma0PoincareGreen20261025a

/-- Public induction on the actual typed input core, retaining its real
compact smooth Poincare generators rather than a whole-plane tensor span. -/
theorem smoothCore_induction (N : ℕ) [NeZero N] {P : smoothCore N → Prop}
    (hseed : ∀ s : SmoothSeed, P (seedCoreElement N s))
    (hzero : P 0)
    (hadd : ∀ u v : smoothCore N, P u → P v → P (u+v))
    (hsmul : ∀ (c : ℂ) (u : smoothCore N), P u → P (c • u))
    (u : smoothCore N) : P u := by
  rcases u with ⟨u,hu⟩
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨s,rfl⟩ := hu
      exact hseed s
  | zero => exact hzero
  | add u v hu hv ihu ihv => exact hadd ⟨u,hu⟩ ⟨v,hv⟩ ihu ihv
  | smul c u hu ihu => exact hsmul c ⟨u,hu⟩ ihu

/-- The exact actual quotient Green identity instantiated at the SAME
seed input/output objects used by actualCoreLaplacian. -/
theorem actualCoreLaplacian_seed_symmetric (N : ℕ) [NeZero N] (s t : SmoothSeed) :
    inner ℂ (actualCoreLaplacian N (seedCoreElement N s))
        ((seedCoreElement N t : smoothCore N) : QuotientL2 N) =
      inner ℂ ((seedCoreElement N s : smoothCore N) : QuotientL2 N)
        (actualCoreLaplacian N (seedCoreElement N t)) := by
  rw [actualCoreLaplacian_seed,actualCoreLaplacian_seed]
  exact actual_quotient_poincare_L2_symmetric N Finset.univ (seedTensors s)
    Finset.univ (seedTensors t)

/-- Every actual smooth compact-seed quotient-core vector can replace the
second seed. The true input/output Green identity remains the sole base. -/
theorem actualCoreLaplacian_seed_left_symmetric (N : ℕ) [NeZero N]
    (s : SmoothSeed) (v : smoothCore N) :
    inner ℂ (actualCoreLaplacian N (seedCoreElement N s)) (v : QuotientL2 N) =
      inner ℂ ((seedCoreElement N s : smoothCore N) : QuotientL2 N) (actualCoreLaplacian N v) := by
  apply smoothCore_induction N (P := fun v =>
    inner ℂ (actualCoreLaplacian N (seedCoreElement N s)) (v : QuotientL2 N) =
      inner ℂ ((seedCoreElement N s : smoothCore N) : QuotientL2 N) (actualCoreLaplacian N v))
    _ _ _ _ v
  · intro t
    exact actualCoreLaplacian_seed_symmetric N s t
  · simp
  · intro u v hu hv
    simpa only [map_add,Submodule.coe_add,inner_add_right,hu,hv]
  · intro c u hu
    simpa only [map_smul,Submodule.coe_smul,inner_smul_right,hu]

/-- Symmetry of the actual geometric Maass operator on ALL of the actual
smooth quotient-L2 core. No density or symmetry conclusion is a premise. -/
theorem actualCoreLaplacian_symmetric (N : ℕ) [NeZero N] (u v : smoothCore N) :
    inner ℂ (actualCoreLaplacian N u) (v : QuotientL2 N) =
      inner ℂ (u : QuotientL2 N) (actualCoreLaplacian N v) := by
  have hall : ∀ u : smoothCore N, ∀ v : smoothCore N,
      inner ℂ (actualCoreLaplacian N u) (v : QuotientL2 N) =
        inner ℂ (u : QuotientL2 N) (actualCoreLaplacian N v) := by
    intro u
    apply smoothCore_induction N (P := fun u => ∀ v : smoothCore N,
      inner ℂ (actualCoreLaplacian N u) (v : QuotientL2 N) =
        inner ℂ (u : QuotientL2 N) (actualCoreLaplacian N v)) _ _ _ _ u
    · intro s v
      exact actualCoreLaplacian_seed_left_symmetric N s v
    · intro v
      simp
    · intro u w hu hw v
      simpa only [map_add,Submodule.coe_add,inner_add_left,hu v,hw v]
    · intro c u hu v
      simpa only [map_smul,Submodule.coe_smul,inner_smul_left,hu v]
  exact hall u v

/-- A useful consequence for the independent genuine energy supplier. -/
theorem actualCoreLaplacian_quadratic_im_zero (N : ℕ) [NeZero N] (u : smoothCore N) :
    (inner ℂ (u : QuotientL2 N) (actualCoreLaplacian N u)).im = 0 := by
  have hsym := actualCoreLaplacian_symmetric N u u
  have hconj := inner_conj_symm (actualCoreLaplacian N u) (u : QuotientL2 N)
  rw [hsym] at hconj
  have him := congrArg Complex.im hconj
  simp only [Complex.conj_im] at him
  linarith

end
end ImbalancedChen.Part3.Gamma0ActualSmoothCoreSymmetry20261025a
