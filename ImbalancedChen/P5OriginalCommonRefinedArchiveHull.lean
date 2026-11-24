import ImbalancedChen.P5OriginalCommonRefinedSeedHull
import ImbalancedChen.P1HistoricalFifthCommonAncestorExcess

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Specialization to the independently indexed full original FIFTH archive,
its strict licensed-owner filters, decoded masks and global owner bank.
The fourth rows/licence remain the ORIGINAL uninstantiated inputs of the
archive adapter.  This is not an assertion that the whole original adopted
P4/P5 bank, common compact approximation or archived gain is complete.
-/
namespace ImbalancedChen.P5OriginalCommonRefinedArchiveHull
noncomputable section
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedSeedHull
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthCommonPolicyInputs

variable (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
  (e : ℚ) (q : ℕ) (chi omega N : ℝ)

theorem archive_common_fifth_exact_hull (pre : List ℕ) :
    exponent5 (sourceData rows4 licensed4 e q chi omega) N pre =
      max (P1OriginalVariableFifthContinuation.exponent5 e chi (refinedMesh q) omega N
        rows4 licensed4 (globalOwners e q chi omega) (licensedRows e q chi omega) pre)
        (inheritedFallback (sourceData rows4 licensed4 e q chi omega) N pre) :=
  fifth_eq_old_max_fallback _ N pre

/-- The independently exported archive residual and this exact hull refer
to the same actual changed ancestor, not merely equal-shaped policies. -/
theorem archive_changedParents_eq :
    changedParents (sourceData rows4 licensed4 e q chi omega) N =
      changedParentPrefixes rows4 licensed4 e q chi omega N := rfl

theorem archive_changed_parent_exact_region (pre : List ℕ) :
    pre ∈ changedParentPrefixes rows4 licensed4 e q chi omega N ↔
      pre.length = 5 ∧
        P1OriginalVariableFifthContinuation.inherited4 e chi (refinedMesh q) omega N
          rows4 licensed4 pre <
            inheritedFallback (sourceData rows4 licensed4 e q chi omega) N pre :=
  changedParents_iff_fallback _ N pre

/-- The entire true seed excess is the positive part of a concrete
fallback-minus-original-fourth comparison. No smallness is postulated. -/
theorem archive_parentExcess_eq_positive_part (pre : List ℕ) :
    P1HistoricalFifthCommonAncestorExcess.parentExcess
      rows4 licensed4 e q chi omega N pre =
        max 0 (inheritedFallback (sourceData rows4 licensed4 e q chi omega) N pre -
          P1OriginalVariableFifthContinuation.inherited4 e chi (refinedMesh q) omega N
            rows4 licensed4 pre) := by
  change commonInherited (sourceData rows4 licensed4 e q chi omega) N pre -
    oldInherited (sourceData rows4 licensed4 e q chi omega) N pre = _
  rw [inherited_eq_old_max_fallback]
  by_cases h : inheritedFallback (sourceData rows4 licensed4 e q chi omega) N pre ≤
      oldInherited (sourceData rows4 licensed4 e q chi omega) N pre
  · rw [max_eq_left h, sub_self, max_eq_left (sub_nonpos.mpr h)]
  · have hh := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right hh, max_eq_right (sub_nonneg.mpr hh)]

end
end ImbalancedChen.P5OriginalCommonRefinedArchiveHull
