import ImbalancedChen.P2OriginalSaving19Cell00AllPrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19HigherMomentsPrefix
import ImbalancedChen.P2OriginalLogMomentQ96ArithmeticBridge

/-! Exact semantic transport of all 56 cell00 prefix certificates to the
unchanged rationalMoment and original Q96 namespace. This owner requires
its own normal and independent kernel receipts. It connects the concrete
decoded cell00 arrays; the Archive aliases and other cells remain separate. -/
namespace ImbalancedChen.P2OriginalSaving19Cell00AllOriginalFloorBridge

set_option maxRecDepth 1000000
set_option Elab.async false

open scoped BigOperators
open P2OriginalSaving19Archive
open P2OriginalSaving19Geometry00Decoding
open P2OriginalSaving19Geometry00BoundedAccess
open P2OriginalSaving19Moment00Decoding
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19HigherMomentsPrefix
open P2OriginalSaving19Cell00AllPrefixFloorChecks

noncomputable def originalMoments (r : Fin 56) (j : Fin 10) (k : Nat) : ℚ :=
  P2OriginalSaving19HigherMoments.rationalMoment
    (fun i => gapQ (boundedRowVertex r i))
    (fun i => 1 - factorsQ (boundedRowVertex r i) j / topsOf (boundedRow r) j) k

theorem prefixMoments_eq_original (r : Fin 56) (j : Fin 10) (k : Nat) (hk : k ≤ 6) :
    prefixMoments r j k = originalMoments r j k := by
  rw [prefixMoments_eq_normalized]
  exact normalizedMoment_eq_encoded (gapNumerators r) (deviationNumerators r j)
    (deviationDenominators r j) (gapScales r) k
    (all_deviationDenominators_ne r j) (all_gapScales_ne r) hk
    (fun i => gapQ (boundedRowVertex r i))
    (fun i => 1 - factorsQ (boundedRowVertex r i) j / topsOf (boundedRow r) j)
    (all_gap_encoding r) (all_deviation_encoding r j)

theorem original_gap_eq (r : Fin 56) (j : Fin 10) :
    gapEvaluator (originalMoments r j) = gapEvaluator (prefixMoments r j) := by
  unfold gapEvaluator
  apply Finset.sum_congr rfl
  intro k hk
  rw [← prefixMoments_eq_original r j (k + 2)
    (by have h := Finset.mem_range.mp hk; omega),
    ← prefixMoments_eq_original r j 1 (by decide)]

theorem original_first_moment (r : Fin 56) (j : Fin 10) :
    originalMoments r j 1 = 1 - meansOf (boundedRow r) j / topsOf (boundedRow r) j := by
  rw [← prefixMoments_eq_original r j 1 (by decide)]
  exact all_first_moments r j

theorem original_saved_Q80 (r : Fin 56) (j : Fin 10) :
    (momentConcrete00.rows[r.val]!).factorFloorsQ80[j.val]! =
      P2OriginalLogMomentQ96CheckerSourceOnly.factorFloorQ80 (originalMoments r j) := by
  rw [← P2OriginalLogMomentQ96ArithmeticBridge.factorFloorQ80_eq]
  unfold factorFloorQ80
  rw [original_gap_eq]
  exact all_saved_Q80 r j

theorem original_Q80_bounds (r : Fin 56) (j : Fin 10) :
    (((momentConcrete00.rows[r.val]!).factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
        P2OriginalLogMomentQ96CheckerSourceOnly.gapEvaluator (originalMoments r j) * (2 : ℚ)^80 ∧
      P2OriginalLogMomentQ96CheckerSourceOnly.gapEvaluator (originalMoments r j) * (2 : ℚ)^80 <
        (((momentConcrete00.rows[r.val]!).factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1 := by
  rw [← P2OriginalLogMomentQ96ArithmeticBridge.gapEvaluator_eq, original_gap_eq]
  exact all_Q80_bounds r j

theorem original_total_eq (r : Fin 56) :
    totalLowerQ80 (originalMoments r) = totalLowerQ80 (prefixMoments r) := by
  unfold totalLowerQ80 factorLowerQ80 roundDownQ
  apply Finset.sum_congr rfl
  intro j hj
  rw [original_gap_eq]

theorem original_saved_new_Q96 (r : Fin 56) :
    (momentConcrete00.rows[r.val]!).newFloorQ96 =
      max (P2OriginalLogMomentQ96CheckerSourceOnly.oldFloorQ96
          (massOf (boundedRow r)) (meansOf (boundedRow r)))
        (P2OriginalLogMomentQ96CheckerSourceOnly.newFloorQ96
          (massOf (boundedRow r)) (meansOf (boundedRow r)) (originalMoments r)) := by
  rw [← P2OriginalLogMomentQ96ArithmeticBridge.oldFloorQ96_eq,
    ← P2OriginalLogMomentQ96ArithmeticBridge.newFloorQ96_eq]
  change (momentConcrete00.rows[r.val]!).newFloorQ96 =
    max (oldFloorQ96 (massOf (boundedRow r)) (meansOf (boundedRow r)))
      (fixedNumerator 96 (oldEvaluator (massOf (boundedRow r)) (meansOf (boundedRow r)) *
        cubicQ (totalLowerQ80 (originalMoments r))))
  rw [original_total_eq]
  exact all_saved_new_Q96_max r

def OriginalFloorChecksFor (row : GeometryRow) (momentRow : MomentRecord)
    (moments : Fin 10 → Nat → ℚ) : Prop :=
  (∀ j : Fin 10, moments j 1 = 1 - meansOf row j / topsOf row j) ∧
  (∀ j : Fin 10, momentRow.factorFloorsQ80[j.val]! =
    P2OriginalLogMomentQ96CheckerSourceOnly.factorFloorQ80 (moments j)) ∧
  momentRow.oldFloorQ96 = row.jensenFloorQ96 ∧
  momentRow.oldFloorQ96 =
    P2OriginalLogMomentQ96CheckerSourceOnly.oldFloorQ96 (massOf row) (meansOf row) ∧
  momentRow.newFloorQ96 =
    max (P2OriginalLogMomentQ96CheckerSourceOnly.oldFloorQ96 (massOf row) (meansOf row))
      (P2OriginalLogMomentQ96CheckerSourceOnly.newFloorQ96 (massOf row) (meansOf row) moments)

theorem all_original_floor_formula (r : Fin 56) :
    OriginalFloorChecksFor (boundedRow r) (momentConcrete00.rows[r.val]!)
      (originalMoments r) := by
  refine ⟨original_first_moment r, original_saved_Q80 r,
    (all_bounded_prefix_floor_checks r).2.2.1, ?_, original_saved_new_Q96 r⟩
  rw [← P2OriginalLogMomentQ96ArithmeticBridge.oldFloorQ96_eq]
  exact (all_bounded_prefix_floor_checks r).2.2.2.1

noncomputable def rawVertices (r : Fin 56) (i : Fin 9) (j : Fin 8) : ℚ :=
  (concreteGeometry00.vertices[(concreteGeometry00.rows[r.val]!).vertexIds[i.val]!]!)[j.val]!

theorem rawVertices_eq (r : Fin 56) : rawVertices r = boundedRowVertex r := by
  funext i j
  exact raw_vertex_no_fallback r i j

noncomputable def rawOriginalMoments (r : Fin 56) (j : Fin 10) (k : Nat) : ℚ :=
  P2OriginalSaving19HigherMoments.rationalMoment
    (fun i => gapQ (rawVertices r i))
    (fun i => 1 - factorsQ (rawVertices r i) j /
      topsOf (concreteGeometry00.rows[r.val]!) j) k

theorem rawOriginalMoments_eq (r : Fin 56) : rawOriginalMoments r = originalMoments r := by
  funext j k
  unfold rawOriginalMoments originalMoments
  rw [rawVertices_eq, row_lookup_no_fallback]

theorem all_original_raw_floor_formula (r : Fin 56) :
    OriginalFloorChecksFor (concreteGeometry00.rows[r.val]!)
      (momentConcrete00.rows[r.val]!) (rawOriginalMoments r) := by
  rw [row_lookup_no_fallback, rawOriginalMoments_eq]
  exact all_original_floor_formula r

#print axioms prefixMoments_eq_original
#print axioms original_gap_eq
#print axioms original_first_moment
#print axioms original_saved_Q80
#print axioms original_Q80_bounds
#print axioms original_total_eq
#print axioms original_saved_new_Q96
#print axioms all_original_floor_formula
#print axioms rawVertices_eq
#print axioms rawOriginalMoments_eq
#print axioms all_original_raw_floor_formula

end ImbalancedChen.P2OriginalSaving19Cell00AllOriginalFloorBridge
