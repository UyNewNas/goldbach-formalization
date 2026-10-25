import ImbalancedChen.Part3SelfAdjointPartialMapShift
import ImbalancedChen.Part3InjectiveSelfAdjointPartialInverse

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The generic Friedrichs operator A=R^{-1}-I as a genuine native unbounded
partial linear map on an arbitrary Hilbert space. Its exact domain is
range R, its exact graph is R(u+v)=u, and A(Rf)=f-Rf.

Injective bounded self-adjoint R supplies native self-adjointness through
the independent native inverse theorem and the proved graph-shift theorem.
Closedness is also proved directly from the actual continuous graph
equation, with only injectivity. Nonnegativity is derived from the genuine
firmness inequality ||Rf||^2 <= Re <f,Rf>; neither nonnegativity nor a
shifted self-adjointness conclusion is among the premises.

No old whole-plane construction is renamed, and no claim is made here
that a particular Gamma0 energy resolvent has already been supplied.
-/

namespace ImbalancedChen.Part3.GenericFriedrichsOperator20261025a

noncomputable section
open Set
open ImbalancedChen.Part3.SelfAdjointPartialMapShift20261025a
open ImbalancedChen.Part3.InjectiveSelfAdjointPartialInverse20261025a

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

def friedrichsR (R : H →L[𝕜] H) : H →ₗ.[𝕜] H :=
  shiftMinusIdentity (inverseR R)

theorem friedrichsR_domain (R : H →L[𝕜] H) :
    (friedrichsR R).domain = R.range := by
  rw [friedrichsR, shiftMinusIdentity_domain, inverseR_domain]

/-- The exact equation identifies the ACTUAL native graph. -/
theorem friedrichsR_mem_graph_iff (R : H →L[𝕜] H) (hinj : Function.Injective R)
    {u v : H} : (u, v) ∈ (friedrichsR R).graph ↔ R (u + v) = u := by
  rw [friedrichsR, shiftMinusIdentity_mem_graph_iff, inverseR_mem_graph_iff R hinj]

def friedrichsEquation (R : H →L[𝕜] H) : (H × H) →L[𝕜] H :=
  R.comp (ContinuousLinearMap.fst 𝕜 H H + ContinuousLinearMap.snd 𝕜 H H) -
    ContinuousLinearMap.fst 𝕜 H H

theorem friedrichsR_graph_eq_ker (R : H →L[𝕜] H) (hinj : Function.Injective R) :
    (friedrichsR R).graph = (friedrichsEquation R).ker := by
  apply SetLike.ext
  rintro ⟨u, v⟩
  rw [friedrichsR_mem_graph_iff R hinj]
  change R (u + v) = u ↔ R (u + v) - u = 0
  exact sub_eq_zero.symm

/-- Closedness needs only the actual injective bounded resolvent. -/
theorem friedrichsR_isClosed (R : H →L[𝕜] H) (hinj : Function.Injective R) :
    (friedrichsR R).IsClosed := by
  rw [LinearPMap.IsClosed, friedrichsR_graph_eq_ker R hinj]
  exact (friedrichsEquation R).isClosed_ker

theorem friedrichsR_dense_domain (R : H →L[𝕜] H)
    (hR : IsSelfAdjoint R) (hinj : Function.Injective R) :
    Dense ((friedrichsR R).domain : Set H) :=
  (inverseR_isSelfAdjoint R hR hinj).dense_domain

/-- Native self-adjoint equality, not merely symmetry or formal adjointness. -/
theorem friedrichsR_isSelfAdjoint (R : H →L[𝕜] H)
    (hR : IsSelfAdjoint R) (hinj : Function.Injective R) :
    IsSelfAdjoint (friedrichsR R) :=
  shiftMinusIdentity_isSelfAdjoint (inverseR R) (inverseR_isSelfAdjoint R hR hinj)

def resolventPoint (R : H →L[𝕜] H) (f : H) : (friedrichsR R).domain :=
  ⟨R f, by rw [friedrichsR_domain]; exact ⟨f, rfl⟩⟩

theorem friedrichsR_resolvent_pair (R : H →L[𝕜] H) (hinj : Function.Injective R)
    (f : H) : (R f, f - R f) ∈ (friedrichsR R).graph := by
  apply (friedrichsR_mem_graph_iff R hinj).mpr
  have heq : R f + (f - R f) = f := by abel
  rw [heq]

theorem friedrichsR_apply_image (R : H →L[𝕜] H) (hinj : Function.Injective R)
    (f : H) : friedrichsR R (resolventPoint R f) = f - R f :=
  LinearPMap.mem_graph_snd_inj (friedrichsR R)
    (LinearPMap.mem_graph _ (resolventPoint R f)) (friedrichsR_resolvent_pair R hinj f) rfl

/-- A literal inverse for I+A on every right-hand side. -/
theorem friedrichsR_shift_surjective (R : H →L[𝕜] H) (hinj : Function.Injective R)
    (f : H) : ∃ u : (friedrichsR R).domain, (u : H) + friedrichsR R u = f := by
  refine ⟨resolventPoint R f, ?_⟩
  rw [friedrichsR_apply_image R hinj]
  change R f + (f - R f) = f
  abel

theorem friedrichsR_graph_nonneg (R : H →L[𝕜] H) (hinj : Function.Injective R)
    (hfirm : ∀ f : H, ‖R f‖^2 ≤ RCLike.re (inner 𝕜 f (R f)))
    {u v : H} (huv : (u, v) ∈ (friedrichsR R).graph) :
    0 ≤ RCLike.re (inner 𝕜 u v) := by
  have hu := (friedrichsR_mem_graph_iff R hinj).mp huv
  have h := hfirm (u + v)
  rw [hu, inner_add_left, map_add, inner_self_eq_norm_sq_to_K,
    RCLike.re_ofReal_pow, inner_re_symm] at h
  linarith

/-- Nonnegativity is a proved consequence of firmness, not a supplied
Friedrichs property or a premise about the desired unbounded output. -/
theorem friedrichsR_nonneg (R : H →L[𝕜] H) (hinj : Function.Injective R)
    (hfirm : ∀ f : H, ‖R f‖^2 ≤ RCLike.re (inner 𝕜 f (R f)))
    (u : (friedrichsR R).domain) :
    0 ≤ RCLike.re (inner 𝕜 (u : H) (friedrichsR R u)) :=
  friedrichsR_graph_nonneg R hinj hfirm (LinearPMap.mem_graph _ u)

end
end ImbalancedChen.Part3.GenericFriedrichsOperator20261025a
