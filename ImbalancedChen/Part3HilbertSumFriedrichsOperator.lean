import ImbalancedChen.Part3GenericFriedrichsOperator
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The unrestricted Hilbert direct sum of native inverse-shift operators.
Its bounded resolvent is CONSTRUCTED coordinatewise using pinned Mathlib
`lp.mapCLM`; native self-adjointness and closedness are then proved using
the injective inverse-shift construction. Its graph is proved equivalent
to membership in every coordinate graph. Its exact domain requires both
coordinate domain membership AND the square summability of actual
coordinate operator values. No global graph or domain identity is an input.

This is the missing operator-assembly primitive. Physical nonzero-cylinder
instantiation and identification with a closed physical energy completion
require separate suppliers; no whole-cylinder or Gamma theorem is claimed.
-/

namespace ImbalancedChen.Part3.HilbertSumFriedrichsOperator20261026b
noncomputable section
open Set
open GenericFriedrichsOperator20261025a

variable {ι : Type*} {H : ι → Type*}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

abbrev HilbertSum := lp H 2

/-- Uniform contraction is a primitive hypothesis about the bounded
coordinate resolvents, not about the desired unbounded direct sum. -/
def sumResolvent (R : ∀ i, H i →L[ℂ] H i) (hRnorm : ∀ i, ‖R i‖ ≤ 1) :
    HilbertSum (H := H) →L[ℂ] HilbertSum (H := H) :=
  lp.mapCLM 2 R zero_le_one hRnorm

@[simp] theorem sumResolvent_apply (R : ∀ i, H i →L[ℂ] H i)
    (hRnorm : ∀ i, ‖R i‖ ≤ 1) (f : HilbertSum (H := H)) (i : ι) :
    sumResolvent R hRnorm f i = R i (f i) := rfl

theorem sumResolvent_opNorm (R : ∀ i, H i →L[ℂ] H i)
    (hRnorm : ∀ i, ‖R i‖ ≤ 1) : ‖sumResolvent R hRnorm‖ ≤ 1 :=
  lp.norm_mapCLM_le 2 R zero_le_one hRnorm

theorem sumResolvent_injective (R : ∀ i, H i →L[ℂ] H i)
    (hRnorm : ∀ i, ‖R i‖ ≤ 1) (hinj : ∀ i, Function.Injective (R i)) :
    Function.Injective (sumResolvent R hRnorm) := by
  intro f g hfg
  ext i
  exact hinj i (congrArg (fun a : HilbertSum (H := H) => a i) hfg)

theorem sumResolvent_selfAdjoint (R : ∀ i, H i →L[ℂ] H i)
    (hRnorm : ∀ i, ‖R i‖ ≤ 1) (hSA : ∀ i, IsSelfAdjoint (R i)) :
    IsSelfAdjoint (sumResolvent R hRnorm) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  exact (hSA i).isSymmetric (f i) (g i)

private theorem sum_norm_sq (f : HilbertSum (H := H)) :
    HasSum (fun i => ‖f i‖ ^ 2) ‖f‖ ^ 2 := by
  apply_mod_cast lp.hasSum_norm (by norm_num) f

theorem sumResolvent_firm (R : ∀ i, H i →L[ℂ] H i)
    (hRnorm : ∀ i, ‖R i‖ ≤ 1)
    (hfirm : ∀ i (f : H i), ‖R i f‖ ^ 2 ≤ (inner ℂ f (R i f)).re)
    (f : HilbertSum (H := H)) :
    ‖sumResolvent R hRnorm f‖ ^ 2 ≤
      (inner ℂ f (sumResolvent R hRnorm f)).re := by
  exact hasSum_le (fun i => hfirm i (f i))
    (sum_norm_sq (sumResolvent R hRnorm f))
    (Complex.reCLM.hasSum (lp.hasSum_inner f (sumResolvent R hRnorm f)))

/-- A true native unbounded partial map, with its actual range domain. -/
def sumOperator (R : ∀ i, H i →L[ℂ] H i) (hRnorm : ∀ i, ‖R i‖ ≤ 1) :
    HilbertSum (H := H) →ₗ.[ℂ] HilbertSum (H := H) :=
  friedrichsR (sumResolvent R hRnorm)

theorem sumOperator_isClosed (R : ∀ i, H i →L[ℂ] H i)
    (hRnorm : ∀ i, ‖R i‖ ≤ 1) (hinj : ∀ i, Function.Injective (R i)) :
    (sumOperator R hRnorm).IsClosed :=
  friedrichsR_isClosed _ (sumResolvent_injective R hRnorm hinj)

theorem sumOperator_selfAdjoint (R : ∀ i, H i →L[ℂ] H i)
    (hRnorm : ∀ i, ‖R i‖ ≤ 1) (hinj : ∀ i, Function.Injective (R i))
    (hSA : ∀ i, IsSelfAdjoint (R i)) : IsSelfAdjoint (sumOperator R hRnorm) :=
  friedrichsR_isSelfAdjoint _ (sumResolvent_selfAdjoint R hRnorm hSA)
    (sumResolvent_injective R hRnorm hinj)

theorem sumOperator_nonneg (R : ∀ i, H i →L[ℂ] H i)
    (hRnorm : ∀ i, ‖R i‖ ≤ 1) (hinj : ∀ i, Function.Injective (R i))
    (hfirm : ∀ i (f : H i), ‖R i f‖ ^ 2 ≤ (inner ℂ f (R i f)).re)
    (f : (sumOperator R hRnorm).domain) :
    0 ≤ (inner ℂ (f : HilbertSum (H := H)) (sumOperator R hRnorm f)).re :=
  friedrichsR_nonneg _ (sumResolvent_injective R hRnorm hinj)
    (sumResolvent_firm R hRnorm hfirm) f

/-- Exact equality with the unrestricted family of coordinate graphs. -/
theorem sumOperator_graph_iff (R : ∀ i, H i →L[ℂ] H i)
    (hRnorm : ∀ i, ‖R i‖ ≤ 1) (hinj : ∀ i, Function.Injective (R i))
    (u v : HilbertSum (H := H)) :
    (u, v) ∈ (sumOperator R hRnorm).graph ↔
      ∀ i, (u i, v i) ∈ (friedrichsR (R i)).graph := by
  rw [sumOperator, friedrichsR_mem_graph_iff _ (sumResolvent_injective R hRnorm hinj)]
  constructor
  · intro h i
    apply (friedrichsR_mem_graph_iff (R i) (hinj i)).mpr
    exact congrArg (fun a : HilbertSum (H := H) => a i) h
  · intro h
    ext i
    exact (friedrichsR_mem_graph_iff (R i) (hinj i)).mp (h i)

/-- Literal coordinate resolvent identity on every forcing vector. -/
theorem sumOperator_resolvent_coordinate (R : ∀ i, H i →L[ℂ] H i)
    (hRnorm : ∀ i, ‖R i‖ ≤ 1) (hinj : ∀ i, Function.Injective (R i))
    (f : HilbertSum (H := H)) (i : ι) :
    sumOperator R hRnorm (resolventPoint (sumResolvent R hRnorm) f) i =
      f i - R i (f i) := by
  have h := friedrichsR_apply_image (sumResolvent R hRnorm)
    (sumResolvent_injective R hRnorm hinj) f
  exact congrArg (fun a : HilbertSum (H := H) => a i) h

/-- The exact sum-domain includes actual coordinate domain membership
and the finite squared-output sum; no uniform bound on A_i is required. -/
theorem sumOperator_domain_iff_squareSummable (R : ∀ i, H i →L[ℂ] H i)
    (hRnorm : ∀ i, ‖R i‖ ≤ 1) (hinj : ∀ i, Function.Injective (R i))
    (u : HilbertSum (H := H)) :
    u ∈ (sumOperator R hRnorm).domain ↔
      ∃ h : ∀ i, u i ∈ (friedrichsR (R i)).domain,
        Summable (fun i => ‖friedrichsR (R i) ⟨u i, h i⟩‖ ^ 2) := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨v, hv⟩
    have hcoord := (sumOperator_graph_iff R hRnorm hinj u v).mp hv
    have hdom : ∀ i, u i ∈ (friedrichsR (R i)).domain := by
      intro i
      exact LinearPMap.mem_domain_iff.mpr ⟨v i, hcoord i⟩
    refine ⟨hdom, ?_⟩
    have heq : (fun i => friedrichsR (R i) ⟨u i, hdom i⟩) = (fun i => v i) := by
      funext i
      exact LinearPMap.mem_graph_snd_inj (friedrichsR (R i))
        (LinearPMap.mem_graph _ ⟨u i, hdom i⟩) (hcoord i) rfl
    rw [heq]
    exact (sum_norm_sq v).summable
  · rintro ⟨hdom, hsum⟩
    have hmem : Memℓp (fun i => friedrichsR (R i) ⟨u i, hdom i⟩) 2 := by
      apply memℓp_gen
      simpa using hsum
    let v : HilbertSum (H := H) := ⟨fun i => friedrichsR (R i) ⟨u i, hdom i⟩, hmem⟩
    refine ⟨v, (sumOperator_graph_iff R hRnorm hinj u v).mpr ?_⟩
    intro i
    exact LinearPMap.mem_graph _ ⟨u i, hdom i⟩

end
end ImbalancedChen.Part3.HilbertSumFriedrichsOperator20261026b
