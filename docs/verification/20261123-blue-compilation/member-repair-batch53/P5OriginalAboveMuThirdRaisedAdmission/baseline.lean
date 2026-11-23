import ImbalancedChen.P5OriginalAboveMuThirdLowerPhysicalCoefficient
import ImbalancedChen.ActualHistoricalThirdTupleDictionary
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The third selected-pair fallback's complete inherited upper predicate
at the new physical cap follows from its literal first/third cube gates.
This discharges the explicit prefix-admissibility input of the corrected
Phase7 negative ordinary-lower residual identity on an actual old-parent
rank-three frontier. The finite compact cell compiler and rough tail
remain separate. Phase5's wrong parity source is not imported.
-/

namespace ImbalancedChen.P5OriginalAboveMuThirdRaisedAdmission

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P5OriginalAboveMuThirdLowerPhysicalCoefficient

/-- Complete three-prime admission at the raised physical level. The
existing tuple dictionary retains both first and third cubes and the
strict total-product cutoff; the selected-pair region pays them all. -/
theorem selected_pair_three_admissible
    (N : ℕ) (hN : 1 < N) (p : Fin 3 → ℕ)
    (hpos : ∀ i, 0 < p i)
    (horder : p 2 < p 1 ∧ p 1 < p 0)
    (hregion : ThirdRegion
      (actualPrimeTupleLog N p 0)
      (actualPrimeTupleLog N p 1)
      (actualPrimeTupleLog N p 2)) :
    ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ v (actualPrimeTupleLog N p 1 +
        actualPrimeTupleLog N p 2)) [p 2, p 1, p 0] := by
  let x := actualPrimeTupleLog N p 0
  let y := actualPrimeTupleLog N p 1
  let z := actualPrimeTupleLog N p 2
  have hfirst : 3 * x < v x :=
    above_mu_old_cap_gt_cube hregion.1 hregion.2.1
  obtain ⟨_, _, _, hthird, _, hraised⟩ :=
    third_initial_physical_gates hregion
  have hlog : 3 * x < v (y + z) ∧
      x + y + 3 * z < v (y + z) := by
    constructor <;> linarith
  have hcubes :=
    (HistoricalThirdCoarse.P1ActualTuple.cube_tests_iff_log hN
      (v (y + z)) (v (y + z)) p hpos).mpr
      ⟨hlog.1, hlog.1, hlog.2⟩
  exact (historicalUnorderedThird_admissible_iff
    ((N : ℝ) ^ v (y + z)) (p 0) (p 1) (p 2)
    (hpos 2) horder.1 horder.2).mpr ⟨hcubes.1, hcubes.2.2⟩

/-- Every actual rank-three frontier history has a literal ordered
three-prime tuple. No abstract history-to-cell receiver is supplied. -/
theorem third_frontier_tuple
    (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (z : ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 3
      (secondPolicy e chi m omega (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 z)) :
    let p := primeHistoryTuple 3 state.selectedPrefix
    state.selectedPrefix = [p 2, p 1, p 0] ∧
      (∀ i, 0 < p i) ∧ p 2 < p 1 ∧ p 1 < p 0 := by
  let p := primeHistoryTuple 3 state.selectedPrefix
  have hlen := firstExitDepthFrontier_selected_length 3
    (secondPolicy e chi m omega (N : ℝ))
    (fun q : ℕ => 1 / ((q : ℝ) - 1)) []
    (roughPrimeUniverse N cap 0 z) true 1 (by simp) state hstate
  have hlist : state.selectedPrefix = [p 2, p 1, p 0] := by
    simpa [List.ofFn_succ, p] using
      (primeHistoryTuple_reverse_ofFn hlen).symm
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 3
    (secondPolicy e chi m omega (N : ℝ))
    (fun q : ℕ => 1 / ((q : ℝ) - 1))
    (roughPrimeUniverse N cap 0 z) state hstate
  have hpos (i : Fin 3) : 0 < p i := by
    have hi : p i ∈ state.selectedPrefix.reverse := by
      rw [hlist]
      fin_cases i <;> simp
    exact (mem_roughPrimeUniverse_prime (hsub.subset hi)).pos
  have hsort := (actualPrimeFrontier_geometry 3 (by omega)
    (secondPolicy e chi m omega (N : ℝ)) N cap z state hstate).2.1
  rw [hlist] at hsort
  have h21 : p 1 < p 0 :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).1 (p 0) (by simp)
  have h32 : p 2 < p 1 :=
    (List.pairwise_cons.mp hsort).1 (p 1) (by simp)
  exact ⟨hlist, hpos, h32, h21⟩

/-- The corrected actual third subtree has its signed lower residual
with no separate inherited-prefix admissibility premise. The exact
physical quotient and original ancestor are those of Phase7. -/
theorem third_frontier_signed_lower_density_from_region
    (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 3
      (secondPolicy e chi m omega (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 z))
    (hregion : ThirdRegion
      (primeHistoryLogCoordinates (N : ℝ) 3 state.selectedPrefix 0)
      (primeHistoryLogCoordinates (N : ℝ) 3 state.selectedPrefix 1)
      (primeHistoryLogCoordinates (N : ℝ) 3 state.selectedPrefix 2)) :
    v (primeHistoryLogCoordinates (N : ℝ) 3 state.selectedPrefix 0) <
        v (primeHistoryLogCoordinates (N : ℝ) 3 state.selectedPrefix 1 +
          primeHistoryLogCoordinates (N : ℝ) 3 state.selectedPrefix 2) ∧
      firstExitRetainedPolynomial
        (finalPolicy e chi m omega (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) state.selectedPrefix
        state.positive state.mass state.remaining =
        -state.mass * actualSmallRosserMinusDensity N cap
          (state.selectedPrefix.headD 0 : ℝ)
          (thirdQ (N : ℝ) state.selectedPrefix /
            (state.selectedPrefix.prod : ℝ)) := by
  let p := primeHistoryTuple 3 state.selectedPrefix
  obtain ⟨hlist, hp, h32, h21⟩ :=
    third_frontier_tuple e chi m omega N cap z state hstate
  have hregion' : ThirdRegion
      (actualPrimeTupleLog N p 0)
      (actualPrimeTupleLog N p 1)
      (actualPrimeTupleLog N p 2) := by
    simpa [actualPrimeTupleLog, primeHistoryLogCoordinates, p] using hregion
  have hpre := selected_pair_three_admissible N hN p hp ⟨h32, h21⟩ hregion'
  have hpre' : ordinaryRosserPrefixAdmissible false
      (thirdQ (N : ℝ) state.selectedPrefix) state.selectedPrefix := by
    simpa [thirdQ, primeHistoryLogCoordinates, actualPrimeTupleLog, p, hlist]
      using hpre
  exact third_frontier_signed_lower_density e chi m omega N cap z state
    hstate hregion hpre'

end
end ImbalancedChen.P5OriginalAboveMuThirdRaisedAdmission
