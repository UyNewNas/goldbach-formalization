import ImbalancedChen.P5OriginalChildIntegerWireBinding
import ImbalancedChen.P5SharpQ80ActualFinitePolicy
import ImbalancedChen.P1ActualVariableFifthFullMean

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
The independent ORIGINAL integer geometry/exact_floor expression is bound
to the sharp128 rational expression, then to ONE finite original policy
and that SAME policy's actual arithmetic fifth saving. The analytic mean
is reused from the existing concrete full-mean theorem, not introduced as
a desired-mean premise. The policy is fixed before eventual even N.

The stored parent values are kept as a symbolic sum. No aggregate is
numerically evaluated, no full historical bank J5 is identified, and the
original selected-owner clipping remains paid by the actual reserve.
-/
namespace ImbalancedChen.P5OriginalWireSamePolicySaving
noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation
open P1OriginalVariableFourthContinuation
open P2OriginalFourthCapProducerInterface
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthRawBoxSelectorEquivalence
open P1OriginalFifthMovingScaleLimit
open P1FifthNamedParentsConcreteJ5
open P5OldFifthExact64ChildTiling
open P5NamedFifthAllChildren
open P5NamedFifthQ80FloorSoundness
open P5SharpQ80ActualFinitePolicy
open P5OriginalChildIntegerWireBinding
open P5NamedAllChildrenSelectedJensen
open P1ActualVariableFifthGlobalSourceAssembly

/-- Actual original integer field expression; not defined from childFloorQ. -/
def wireSymbolicTotal : ℚ :=
  ∑ tag : Bool, ∑ c : ChildIndex,
    (originalExactFloor (originalFields (namedParent tag) c) : ℚ) / (2 : ℚ)^80

/-- Equality uses the independently reconstructed original integer formula
and its finite arithmetic proof, not two identical candidate definitions. -/
theorem wireSymbolicTotal_eq_sharp128 : wireSymbolicTotal = namedSharpQ80Total := by
  unfold wireSymbolicTotal namedSharpQ80Total
  simp_rw [original_all128_expanded_floors_exact]
  simp [childFloorQ, ImbalancedChen.Certificates.P2DirectedLogRounding.dyadicScale]

/-- A symbolic stored-field identity only. The two integer constants came
from the independently hashed block0 fields; the sum is not evaluated. -/
theorem wireSymbolicTotal_eq_stored_parent_fields :
    wireSymbolicTotal = ∑ tag : Bool, (storedParentNew tag : ℚ) / (2 : ℚ)^80 := by
  unfold wireSymbolicTotal
  apply Finset.sum_congr rfl
  intro tag _
  rw [stored_first_two_new_eq_complete_child_sum]
  push_cast
  simp [Finset.sum_div]

/-- ONE actual named finite policy achieves the independent wire-expression
saving integral AND the same actual signed arithmetic saving for all
sufficiently large even N. The tolerance is split only between the actual
owner reserve and the independently proved concrete mean convergence.

The cap assumption is the original finite source-carrier cutoff. It is
not an assumed upper density, saving, PP estimate or desired integral. -/
theorem exists_same_policy_integral_and_eventual_wire_saving
    (tol omega : ℝ) (htol : 0 < tol) (homega : 0 < omega) (hw : omega ≤ 1 / 400)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    ∃ e : ℚ, ∃ q : ℕ,
      0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧ 0 < q ∧
      (∑ tag : Bool, namedReserveTotal tag e ((e : ℝ) / 20) (refinedMesh q) omega
        (namedJ5 (refinedMesh q))) < tol / 2 ∧
      (wireSymbolicTotal : ℝ) - tol / 2 ≤
        P1ActualVariableFifthUntruncatedDomination.fullSelectedIntegral e ((e : ℝ) / 20)
          (refinedMesh q) omega rows4 licensed4 (namedJ5 (refinedMesh q))
          (decodedFamily P1FifthNamedParentActualIntegral.namedRecords q) ∧
      ∀ᶠ N : ℕ in evenTargets,
        (wireSymbolicTotal : ℝ) - tol <
          actualFifthSaving e ((e : ℝ) / 20) (refinedMesh q) omega rows4 licensed4
            (namedJ5 (refinedMesh q))
            (decodedFamily P1FifthNamedParentActualIntegral.namedRecords q)
            N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) * Real.log (N : ℝ) / singularSeries N ∧
        (wireSymbolicTotal : ℝ) - tol <
          (originalFourthRetained e ((e : ℝ) / 20) (refinedMesh q) omega
              N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) rows4 licensed4 -
            variableFifthRetained e ((e : ℝ) / 20) (refinedMesh q) omega
              N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) rows4 licensed4
              (namedJ5 (refinedMesh q))
              (decodedFamily P1FifthNamedParentActualIntegral.namedRecords q)) *
            Real.log (N : ℝ) / singularSeries N ∧
        ((wireSymbolicTotal : ℝ) - tol) * singularSeries N / Real.log (N : ℝ) <
          actualFifthSaving e ((e : ℝ) / 20) (refinedMesh q) omega rows4 licensed4
            (namedJ5 (refinedMesh q))
            (decodedFamily P1FifthNamedParentActualIntegral.namedRecords q)
            N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) := by
  obtain ⟨e, q, he, hemax, hq, hreserve, hI⟩ :=
    exists_actual_named_policy_ge_sharpQ80_sub_tolerance (tol / 2) omega
      (by positivity) homega hw rows4 licensed4 hgeometry
  have heQ : 0 ≤ e := by exact_mod_cast he.le
  have homegaRho : omega < (19 / 96 : ℝ) := by linarith
  let m := refinedMesh q
  let chi := (e : ℝ) / 20
  let J5 := namedJ5 m
  let rows5 := decodedFamily P1FifthNamedParentActualIntegral.namedRecords q
  let I := P1ActualVariableFifthUntruncatedDomination.fullSelectedIntegral
    e chi m omega rows4 licensed4 J5 rows5
  have hbase : (wireSymbolicTotal : ℝ) - tol / 2 ≤ I := by
    rw [wireSymbolicTotal_eq_sharp128]
    exact hI
  have hmean := P1ActualVariableFifthFullMean.tendsto_normalizedSaving_fullSelectedIntegral
    e heQ chi m omega homega homegaRho rows4 licensed4 J5 rows5 cap hcap
  have hret := P1ActualVariableFifthFullMean.tendsto_retainedFourth_sub_variableFifth_fullIntegral
    e heQ chi m omega homega homegaRho rows4 licensed4 J5 rows5 cap hcap
  have hmeanLower := hmean.eventually
    (lt_mem_nhds (show I - tol / 2 < I by linarith))
  have hretLower := hret.eventually
    (lt_mem_nhds (show I - tol / 2 < I by linarith))
  refine ⟨e, q, he, hemax, hq, hreserve, hbase, ?_⟩
  filter_upwards [hmeanLower, hretLower,
    (eventually_gt_atTop (1 : ℕ)).filter_mono
      (show evenTargets ≤ atTop from inf_le_left)] with N hmeanN hretN hN
  have hsave : (wireSymbolicTotal : ℝ) - tol <
      normalizedSaving e chi m omega rows4 licensed4 J5 rows5 N (cap N) := by
    linarith
  have hdiff : (wireSymbolicTotal : ℝ) - tol <
      (originalFourthRetained e chi m omega N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) rows4 licensed4 -
        variableFifthRetained e chi m omega N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ))
          rows4 licensed4 J5 rows5) * Real.log (N : ℝ) / singularSeries N := by
    linarith
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hS : 0 < singularSeries N := singularSeries_pos N
  have hraw := mul_lt_mul_of_pos_right hsave (div_pos hS hlog)
  have hid : normalizedSaving e chi m omega rows4 licensed4 J5 rows5 N (cap N) *
      (singularSeries N / Real.log (N : ℝ)) =
      actualFifthSaving e chi m omega rows4 licensed4 J5 rows5
        N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) := by
    unfold normalizedSaving
    field_simp [hlog.ne', hS.ne']
    <;> ring
  rw [hid] at hraw
  refine ⟨hsave, hdiff, ?_⟩
  simpa only [div_eq_mul_inv, mul_assoc] using hraw

end
end ImbalancedChen.P5OriginalWireSamePolicySaving
