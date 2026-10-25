import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Native partial inverse of an injective bounded self-adjoint operator on
an arbitrary real or complex Hilbert space. The inverse domain is exactly
the actual range of R and its graph is exactly R v = u. Its native adjoint
has this same graph, hence equals the inverse AS A LinearPMap, including
equality of domains. Symmetry alone is not substituted for self-adjointness.

Only bounded self-adjointness and injectivity of R are source assumptions.
No inverse self-adjointness, output density or target graph premise occurs.
Instantiation at an actual Gamma0 quotient R is a separate source join.
-/

namespace ImbalancedChen.Part3.InjectiveSelfAdjointPartialInverse20261025a

noncomputable section
open Set

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The native inverse of the total bounded operator, regarded as a
partial linear map with its genuine range domain. -/
def inverseR (R : H →L[𝕜] H) : H →ₗ.[𝕜] H :=
  (R.toPMap ⊤).inverse

theorem totalR_mem_graph_iff (R : H →L[𝕜] H) {u v : H} :
    (u,v) ∈ (R.toPMap ⊤).graph ↔ R u = v := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨x,rfl,hx⟩
    exact hx
  · intro huv
    exact ⟨⟨u,Submodule.mem_top⟩,rfl,huv⟩

theorem totalR_ker_eq_bot (R : H →L[𝕜] H) (hinj : Function.Injective R) :
    LinearMap.ker (R.toPMap ⊤).toFun = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro u hu
  apply Subtype.ext
  exact hinj (by simpa using hu)

/-- The domain is literally the range of R, not merely its closure. -/
theorem inverseR_domain (R : H →L[𝕜] H) :
    (inverseR R).domain = R.range := by
  unfold inverseR
  rw [LinearPMap.inverse_domain]
  apply SetLike.ext
  intro x
  constructor
  · rintro ⟨u,hu⟩
    exact ⟨(u : H),hu⟩
  · rintro ⟨u,hu⟩
    exact ⟨⟨u,Submodule.mem_top⟩,hu⟩

/-- Exact native graph swap, under the genuine injectivity source. -/
theorem inverseR_graph (R : H →L[𝕜] H) (hinj : Function.Injective R) :
    (inverseR R).graph = (R.toPMap ⊤).graph.map
      (LinearEquiv.prodComm 𝕜 H H : (H × H) →ₗ[𝕜] (H × H)) :=
  LinearPMap.inverse_graph (totalR_ker_eq_bot R hinj)

theorem inverseR_mem_graph_iff (R : H →L[𝕜] H) (hinj : Function.Injective R)
    {u v : H} : (u,v) ∈ (inverseR R).graph ↔ R v = u := by
  rw [inverseR_graph R hinj]
  constructor
  · rintro ⟨p,hp,hpEq⟩
    have hpR : R p.1 = p.2 := (totalR_mem_graph_iff R).mp hp
    have hfst : p.2 = u := congrArg Prod.fst hpEq
    have hsnd : p.1 = v := congrArg Prod.snd hpEq
    simpa only [hfst,hsnd] using hpR
  · intro huv
    exact ⟨(v,u),(totalR_mem_graph_iff R).mpr huv,rfl⟩

theorem image_mem_inverseR_domain (R : H →L[𝕜] H) (f : H) :
    R f ∈ (inverseR R).domain := by
  rw [inverseR_domain]
  exact ⟨f,rfl⟩

theorem inverseR_apply_image (R : H →L[𝕜] H) (hinj : Function.Injective R)
    (f : H) : inverseR R ⟨R f,image_mem_inverseR_domain R f⟩ = f := by
  have hg : (R f,f) ∈ (inverseR R).graph :=
    (inverseR_mem_graph_iff R hinj).mpr rfl
  exact (inverseR R).mem_graph_snd_inj
    ((inverseR R).mem_graph ⟨R f,image_mem_inverseR_domain R f⟩) hg rfl

theorem inverseR_apply_spec (R : H →L[𝕜] H) (hinj : Function.Injective R)
    (u : (inverseR R).domain) : R (inverseR R u) = (u : H) :=
  (inverseR_mem_graph_iff R hinj).mp ((inverseR R).mem_graph u)

/-- A bounded self-adjoint injective R has dense actual range, by the
true orthogonal-kernel identity for its bounded Hilbert adjoint. -/
theorem rangeR_dense (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) : Dense (R.range : Set H) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hker : R.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have h := R.orthogonal_ker
  rw [hR.adjoint_eq,hker,Submodule.bot_orthogonal] at h
  exact h.symm

theorem inverseR_dense_domain (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) : Dense ((inverseR R).domain : Set H) := by
  rw [inverseR_domain]
  exact rangeR_dense R hR hinj

/-- Closedness already follows directly from the exact inverse graph and
continuity of the original bounded R; self-adjointness is not needed here. -/
theorem inverseR_isClosed (R : H →L[𝕜] H) (hinj : Function.Injective R) :
    (inverseR R).IsClosed := by
  change IsClosed ((inverseR R).graph : Set (H × H))
  have hset : ((inverseR R).graph : Set (H × H)) =
      {p : H × H | R p.2 = p.1} := by
    ext p
    exact inverseR_mem_graph_iff R hinj
  rw [hset]
  exact isClosed_eq (R.continuous.comp continuous_snd) continuous_fst

/-- Compute the ACTUAL native adjoint graph. Its defining universal
Hilbert pairing reduces, using bounded self-adjointness of R, to R v=u. -/
theorem inverseR_adjoint_graph_eq (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) :
    (inverseR R).adjoint.graph = (inverseR R).graph := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (inverseR_dense_domain R hR hinj)]
  apply SetLike.ext
  intro p
  rw [Submodule.mem_adjoint_iff]
  constructor
  · intro hp
    apply (inverseR_mem_graph_iff R hinj).mpr
    apply ext_inner_left 𝕜
    intro f
    have hf := hp (R f) f ((inverseR_mem_graph_iff R hinj).mpr rfl)
    calc
      inner 𝕜 f (R p.2) = inner 𝕜 (R f) p.2 := (hR.isSymmetric f p.2).symm
      _ = inner 𝕜 f p.1 := (sub_eq_zero.mp hf).symm
  · intro hp a b hab
    have hpR : R p.2 = p.1 := (inverseR_mem_graph_iff R hinj).mp hp
    have habR : R b = a := (inverseR_mem_graph_iff R hinj).mp hab
    rw [← hpR,← habR,hR.isSymmetric b p.2]
    exact sub_self _

/-- Equality of native partial linear maps: both adjoint DOMAIN and
adjoint value agree, rather than a symmetry assertion on a smaller core. -/
theorem inverseR_adjoint_eq (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) : (inverseR R).adjoint = inverseR R :=
  LinearPMap.eq_of_eq_graph (inverseR_adjoint_graph_eq R hR hinj)

theorem inverseR_adjoint_domain (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) : (inverseR R).adjoint.domain = R.range := by
  rw [inverseR_adjoint_eq R hR hinj,inverseR_domain]

theorem inverseR_isSelfAdjoint (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) : IsSelfAdjoint (inverseR R) :=
  LinearPMap.isSelfAdjoint_def.mpr (inverseR_adjoint_eq R hR hinj)

end
end ImbalancedChen.Part3.InjectiveSelfAdjointPartialInverse20261025a
