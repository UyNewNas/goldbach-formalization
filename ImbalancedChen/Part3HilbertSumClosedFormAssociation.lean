import ImbalancedChen.Part3HilbertSumFriedrichsOperator
import ImbalancedChen.Part3GenericWeakFriedrichsAssociation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The actual closed-energy/direct-sum join primitive. A uniformly
contractive family of genuine energy embeddings J_i is assembled on the
complete unrestricted energy Hilbert sum. Its native Hilbert adjoint is
proved coordinatewise, so its actual Riesz resolvent Jsum*Jsum.adjoint
is the coordinate direct sum of J_i*J_i.adjoint. The global weak relation
and all coordinate weak relations are proved equivalent to the same
constructed native unbounded operator graph.

Only the original bounded energy embeddings, their norm bounds, and their
dense physical images are premises. No global operator graph, form
isometry, resolvent identity, or global energy-completion equivalence is
assumed. Identification with a geometric cylinder energy completion is
separate and remains open until its genuine finite-mode core is supplied.
-/

namespace ImbalancedChen.Part3.HilbertSumClosedFormAssociation20261026b
noncomputable section
open GenericHilbertAdjointSquare20261025a
open GenericFriedrichsOperator20261025a
open GenericWeakFriedrichsAssociation20261025a
open HilbertSumFriedrichsOperator20261026b

variable {ι : Type*} {E H : ι → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
variable [∀ i, CompleteSpace (E i)]
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

def sumEmbedding (J : ∀ i, E i →L[ℂ] H i) (hJnorm : ∀ i, ‖J i‖ ≤ 1) :
    lp E 2 →L[ℂ] lp H 2 := lp.mapCLM 2 J zero_le_one hJnorm

@[simp] theorem sumEmbedding_apply (J : ∀ i, E i →L[ℂ] H i)
    (hJnorm : ∀ i, ‖J i‖ ≤ 1) (e : lp E 2) (i : ι) :
    sumEmbedding J hJnorm e i = J i (e i) := rfl

theorem sumEmbedding_opNorm (J : ∀ i, E i →L[ℂ] H i)
    (hJnorm : ∀ i, ‖J i‖ ≤ 1) : ‖sumEmbedding J hJnorm‖ ≤ 1 :=
  lp.norm_mapCLM_le 2 J zero_le_one hJnorm

private theorem adjoint_norm_le (J : ∀ i, E i →L[ℂ] H i)
    (hJnorm : ∀ i, ‖J i‖ ≤ 1) (i : ι) : ‖(J i).adjoint‖ ≤ 1 := by
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact hJnorm i

/-- The adjoint is derived from its defining pairings on the genuine
infinite Hilbert sums, rather than assumed to act coordinatewise. -/
theorem sumEmbedding_adjoint (J : ∀ i, E i →L[ℂ] H i)
    (hJnorm : ∀ i, ‖J i‖ ≤ 1) :
    (sumEmbedding J hJnorm).adjoint =
      lp.mapCLM 2 (fun i => (J i).adjoint) zero_le_one (adjoint_norm_le J hJnorm) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f e
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  exact (J i).adjoint_inner_left (e i) (f i)

@[simp] theorem sumEmbedding_adjoint_apply (J : ∀ i, E i →L[ℂ] H i)
    (hJnorm : ∀ i, ‖J i‖ ≤ 1) (f : lp H 2) (i : ι) :
    (sumEmbedding J hJnorm).adjoint f i = (J i).adjoint (f i) := by
  rw [sumEmbedding_adjoint]
  rfl

def coordinateR (J : ∀ i, E i →L[ℂ] H i) (i : ι) : H i →L[ℂ] H i :=
  adjointSquare (J i)

theorem coordinateR_opNorm (J : ∀ i, E i →L[ℂ] H i)
    (hJnorm : ∀ i, ‖J i‖ ≤ 1) (i : ι) : ‖coordinateR J i‖ ≤ 1 :=
  adjointSquare_opNorm_le_one (J i) (hJnorm i)

/-- The actual global energy Riesz resolvent equals the assembled
coordinate resolvent as a continuous linear map. -/
theorem sumEmbedding_adjointSquare (J : ∀ i, E i →L[ℂ] H i)
    (hJnorm : ∀ i, ‖J i‖ ≤ 1) :
    adjointSquare (sumEmbedding J hJnorm) =
      sumResolvent (coordinateR J) (coordinateR_opNorm J hJnorm) := by
  ext f i
  change J i ((sumEmbedding J hJnorm).adjoint f i) =
    J i ((J i).adjoint (f i))
  rw [sumEmbedding_adjoint_apply]

def energySumOperator (J : ∀ i, E i →L[ℂ] H i)
    (hJnorm : ∀ i, ‖J i‖ ≤ 1) : lp H 2 →ₗ.[ℂ] lp H 2 :=
  sumOperator (coordinateR J) (coordinateR_opNorm J hJnorm)

theorem energySumOperator_selfAdjoint (J : ∀ i, E i →L[ℂ] H i)
    (hJnorm : ∀ i, ‖J i‖ ≤ 1) (hJdense : ∀ i, DenseRange (J i)) :
    IsSelfAdjoint (energySumOperator J hJnorm) :=
  sumOperator_selfAdjoint _ _ (fun i => adjointSquare_injective (J i) (hJdense i))
    (fun i => adjointSquare_selfAdjoint (J i))

theorem energySumOperator_nonneg (J : ∀ i, E i →L[ℂ] H i)
    (hJnorm : ∀ i, ‖J i‖ ≤ 1) (hJdense : ∀ i, DenseRange (J i))
    (u : (energySumOperator J hJnorm).domain) :
    0 ≤ (inner ℂ (u : lp H 2) (energySumOperator J hJnorm u)).re :=
  sumOperator_nonneg _ _ (fun i => adjointSquare_injective (J i) (hJdense i))
    (fun i => adjointSquare_firm (J i) (hJnorm i)) u

/-- Exact graph of the weak closed form on the genuine energy Hilbert
sum. No global weak relation or graph identity is supplied as a premise. -/
theorem energySumOperator_graph_iff_weak (J : ∀ i, E i →L[ℂ] H i)
    (hJnorm : ∀ i, ‖J i‖ ≤ 1) (hJdense : ∀ i, DenseRange (J i))
    (u v : lp H 2) :
    (u, v) ∈ (energySumOperator J hJnorm).graph ↔
      WeakEnergyRelation (sumEmbedding J hJnorm) u v := by
  rw [weakEnergyRelation_iff_adjointSquare, sumEmbedding_adjointSquare]
  exact friedrichsR_mem_graph_iff _
    (sumResolvent_injective _ _ (fun i => adjointSquare_injective (J i) (hJdense i)))

/-- A genuinely square-summable global energy lift exists exactly when
every coordinate satisfies the actual closed weak equation. The global
lift is constructed by the native adjoint; it is not assumed summable. -/
theorem weakEnergyRelation_sum_iff_coordinates (J : ∀ i, E i →L[ℂ] H i)
    (hJnorm : ∀ i, ‖J i‖ ≤ 1) (hJdense : ∀ i, DenseRange (J i))
    (u v : lp H 2) :
    WeakEnergyRelation (sumEmbedding J hJnorm) u v ↔
      ∀ i, WeakEnergyRelation (J i) (u i) (v i) := by
  rw [← energySumOperator_graph_iff_weak J hJnorm hJdense u v]
  change (u, v) ∈
    (sumOperator (coordinateR J) (coordinateR_opNorm J hJnorm)).graph ↔ _
  rw [sumOperator_graph_iff _ _ (fun i => adjointSquare_injective (J i) (hJdense i))]
  apply forall_congr'
  intro i
  rw [weakEnergyRelation_iff_adjointSquare]
  exact friedrichsR_mem_graph_iff _ (adjointSquare_injective (J i) (hJdense i))

end
end ImbalancedChen.Part3.HilbertSumClosedFormAssociation20261026b
