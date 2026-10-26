import ImbalancedChen.Part3Gamma0FixedCoreFiniteNetProjection

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
The literal quotient finite-net orthogonal projections approximate the
ACTUAL truncated resolvent in operator norm. Each approximant has proved
finite dimensional range in canonical Gamma0 quotient L2. The estimate
uses J_Y J* and the proved contraction of the ORIGINAL energy inclusion.
No all-cusps tail, global resolvent compactness, or discreteness is claimed. -/

namespace ImbalancedChen.Part3.Gamma0TruncatedResolventFiniteRank20261026b
noncomputable section
open Set
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0CompletedFormFixedCoreRellich20261026b
open Gamma0FixedCoreCompactOperator20261026b
open Gamma0FixedCoreFiniteNetProjection20261026b

theorem projectedTruncatedResolvent_finiteRange (N : ℕ) [NeZero N] (Y : ℝ)
    (S : Finset (QuotientL2 N)) :
    FiniteDimensional ℂ ((finiteNetProjection N S).comp (actualTruncatedResolvent N Y)).range := by
  letI : FiniteDimensional ℂ (finiteNetProjection N S).range := finiteNetProjection_finiteRange N S
  apply Submodule.finiteDimensional_of_le
    (show ((finiteNetProjection N S).comp (actualTruncatedResolvent N Y)).range ≤
      (finiteNetProjection N S).range from ?_)
  rintro y ⟨f,rfl⟩
  exact ⟨actualTruncatedResolvent N Y f,rfl⟩

/-- A norm approximation for J_Y immediately gives the SAME error for
the actual J_Y J* resolvent truncation, because the true J* is contractive. -/
theorem projectedTruncatedResolvent_error_le (N : ℕ) [NeZero N] (Y : ℝ)
    (P : QuotientL2 N →L[ℂ] QuotientL2 N) (ε : ℝ) (hε : 0 ≤ ε)
    (hP : ‖completedCoreRestriction N Y-P.comp (completedCoreRestriction N Y)‖ ≤ ε) :
    ‖actualTruncatedResolvent N Y-P.comp (actualTruncatedResolvent N Y)‖ ≤ ε := by
  have he : actualTruncatedResolvent N Y-P.comp (actualTruncatedResolvent N Y) =
      (completedCoreRestriction N Y-P.comp (completedCoreRestriction N Y)).comp
        (physicalProjection N).adjoint := by
    ext f
    rfl
  have hJ : ‖(physicalProjection N).adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact physicalProjection_opNorm_le_one N
  rw [he]
  calc
    _ ≤ ‖completedCoreRestriction N Y-P.comp (completedCoreRestriction N Y)‖ *
        ‖(physicalProjection N).adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ε*1 := mul_le_mul hP hJ (norm_nonneg _) hε
    _ = ε := mul_one ε

/-- Actual finite-rank quotient operator approximation of the compact
fixed-truncation resolvent, by the literal finite-net span projections. -/
theorem exists_actualTruncatedResolvent_finiteRank_approximation (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset (QuotientL2 N),
      FiniteDimensional ℂ ((finiteNetProjection N S).comp (actualTruncatedResolvent N Y)).range ∧
      IsIdempotentElem (finiteNetProjection N S) ∧ IsSelfAdjoint (finiteNetProjection N S) ∧
      ‖actualTruncatedResolvent N Y-
        (finiteNetProjection N S).comp (actualTruncatedResolvent N Y)‖ ≤ ε := by
  obtain ⟨S,_hnet,happrox⟩ := exists_actual_finite_net_orthogonal_approximation N Y hY ε hε
  exact ⟨S,projectedTruncatedResolvent_finiteRange N Y S,
    finiteNetProjection_idempotent N S,finiteNetProjection_selfAdjoint N S,
    projectedTruncatedResolvent_error_le N Y (finiteNetProjection N S) ε hε.le happrox⟩

end
end ImbalancedChen.Part3.Gamma0TruncatedResolventFiniteRank20261026b
