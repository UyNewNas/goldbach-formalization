import ImbalancedChen.Part3GenericHilbertAdjointSquare

/-!
# Generic weak energy association and the actual adjoint-square equation

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

For arbitrary complete complex Hilbert spaces E,H and a bounded linear
map J:E→H, the weak shifted-energy relation is DEFINED by a genuine
energy-space lift and testing against every energy vector. Its equivalence
with J J*(u+v)=u is PROVED by the native adjoint identity and inner-product
extensionality. Dense range of J then makes the relation single-valued.

No weak-graph equivalence, variational solution, positivity, or desired
operator graph is assumed. No fixed whole-plane space is substituted for
an actual Gamma0 energy or physical space. Actual Gamma0 instantiation and
the separate inverse-graph self-adjoint construction are downstream.
-/

namespace ImbalancedChen.Part3.GenericWeakFriedrichsAssociation20261025a
noncomputable section
open Set
open ImbalancedChen.Part3.GenericHilbertAdjointSquare20261025a

variable {E H : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Genuine shifted energy testing, with the complex inner product linear
in its SECOND argument. The energy lift is part of the definition, not an
assumed solution operator or a desired resolvent equation. -/
def WeakEnergyRelation (J : E →L[ℂ] H) (u v : H) : Prop :=
  ∃ e : E, J e = u ∧ ∀ d : E, inner ℂ d e = inner ℂ (J d) (u + v)

/-- Every genuine weak lift is the native adjoint Riesz lift. -/
theorem weakEnergyLift_eq_rieszLift (J : E →L[ℂ] H) (u v : H) (e : E)
    (he : ∀ d : E, inner ℂ d e = inner ℂ (J d) (u + v)) :
    e = rieszLift J (u + v) :=
  rieszLift_weak_unique J (u + v) e he

/-- The genuine variational relation is EXACTLY the inverse-shift graph
of the actual adjoint square. This is a theorem, not an ABI premise. -/
theorem weakEnergyRelation_iff_adjointSquare (J : E →L[ℂ] H) (u v : H) :
    WeakEnergyRelation J u v ↔ adjointSquare J (u + v) = u := by
  constructor
  · rintro ⟨e,hJe,he⟩
    have heq := weakEnergyLift_eq_rieszLift J u v e he
    change J (rieszLift J (u + v)) = u
    rw [← heq]
    exact hJe
  · intro hR
    exact ⟨rieszLift J (u + v), hR, rieszLift_weak J (u + v)⟩

/-- The actual Riesz lift is a canonical witness in the energy space. -/
theorem weakEnergyRelation_canonical_lift (J : E →L[ℂ] H) {u v : H}
    (huv : WeakEnergyRelation J u v) :
    J (rieszLift J (u + v)) = u ∧
      ∀ d : E, inner ℂ d (rieszLift J (u + v)) = inner ℂ (J d) (u + v) :=
  ⟨(weakEnergyRelation_iff_adjointSquare J u v).mp huv, rieszLift_weak J (u + v)⟩

/-- The dense physical image makes the weak association single-valued.
No uniqueness conclusion is supplied separately as an input. -/
theorem weakEnergyRelation_output_unique (J : E →L[ℂ] H) (hJdense : DenseRange J)
    {u v w : H} (hv : WeakEnergyRelation J u v) (hw : WeakEnergyRelation J u w) : v = w := by
  have hsum : u + v = u + w := (adjointSquare_injective J hJdense)
    (((weakEnergyRelation_iff_adjointSquare J u v).mp hv).trans
      ((weakEnergyRelation_iff_adjointSquare J u w).mp hw).symm)
  exact add_left_cancel hsum

/-- Every physical forcing f has the actual pair (R f, f-R f), obtained
from the constructed adjoint square rather than assumed solvability. -/
theorem weakEnergyRelation_resolvent (J : E →L[ℂ] H) (f : H) :
    WeakEnergyRelation J (adjointSquare J f) (f - adjointSquare J f) := by
  apply (weakEnergyRelation_iff_adjointSquare J _ _).mpr
  have hsum : adjointSquare J f + (f - adjointSquare J f) = f := by abel
  rw [hsum]

/-- The shifted weak equation has a unique PHYSICAL solution even before
density of J is imposed. -/
theorem weakEnergyRelation_resolvent_unique (J : E →L[ℂ] H) (f u : H)
    (hu : WeakEnergyRelation J u (f - u)) : u = adjointSquare J f := by
  have h := (weakEnergyRelation_iff_adjointSquare J u (f - u)).mp hu
  have hsum : u + (f - u) = f := by abel
  rw [hsum] at h
  exact h.symm

theorem existsUnique_shifted_weak_solution (J : E →L[ℂ] H) (f : H) :
    ∃! u : H, WeakEnergyRelation J u (f - u) := by
  exact ⟨adjointSquare J f, weakEnergyRelation_resolvent J f,
    fun u hu => weakEnergyRelation_resolvent_unique J f u hu⟩

/-- The true weak relation domain is exactly the actual range of R. -/
theorem weakEnergyRelation_domain_iff_range (J : E →L[ℂ] H) (u : H) :
    (∃ v : H, WeakEnergyRelation J u v) ↔ u ∈ Set.range (adjointSquare J) := by
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨u + v, (weakEnergyRelation_iff_adjointSquare J u v).mp hv⟩
  · rintro ⟨f,rfl⟩
    exact ⟨f - adjointSquare J f, weakEnergyRelation_resolvent J f⟩

theorem weakEnergyRelation_domain_dense (J : E →L[ℂ] H) (hJdense : DenseRange J) :
    Dense {u : H | ∃ v : H, WeakEnergyRelation J u v} := by
  have heq : {u : H | ∃ v : H, WeakEnergyRelation J u v} =
      Set.range (adjointSquare J) := Set.ext (weakEnergyRelation_domain_iff_range J)
  rw [heq]
  exact adjointSquare_denseRange J hJdense

/-- Closedness is derived from the bounded adjoint-square equation; no
closed graph or unbounded operator supplier is assumed. -/
theorem weakEnergyRelation_graph_isClosed (J : E →L[ℂ] H) :
    IsClosed {p : H × H | WeakEnergyRelation J p.1 p.2} := by
  have heq : {p : H × H | WeakEnergyRelation J p.1 p.2} =
      {p : H × H | adjointSquare J (p.1 + p.2) = p.1} := by
    ext p
    exact weakEnergyRelation_iff_adjointSquare J p.1 p.2
  rw [heq]
  exact isClosed_eq ((adjointSquare J).continuous.comp (continuous_fst.add continuous_snd))
    continuous_fst

end
end ImbalancedChen.Part3.GenericWeakFriedrichsAssociation20261025a
