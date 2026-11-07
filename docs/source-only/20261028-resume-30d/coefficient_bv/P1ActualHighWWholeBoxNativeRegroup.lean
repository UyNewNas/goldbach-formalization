import ImbalancedChen.P1ActualHighRankPairFactorCaller
import ImbalancedChen.ActualPrimeFineWordSlotRegrouping

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Extend the actual high branch to the W-winning row4 program.  Its close,
gap, first-overflow and full-vector-repair programs preserve the original
slot occurrences.  The resulting permutation is independent of arithmetic
queries and gives a fixed whole-box normalized three-group expansion.

The original sorted-source scalar and SAME full-q native rho are preserved
exactly. The original causal gate remains explicitly evaluated at the full
product in the final test. This is NOT a claim that this remaining coupled
rho/gate has been replaced by a separated three-convolution coefficient.
That further whole-atom gate/factorability connection remains open.
-/

namespace ImbalancedChen.P1ActualHighWWholeBoxNativeRegroup
noncomputable section
open Classical
open scoped BigOperators
open P1ActualCompactUpperBVBranchSplit P1ActualHighRankPairFactorCaller
open P1ActualCompactUpperLowRankIntegerBinding
open ImbalancedChen.Part3.ActualWThreeCapacityRun
open ImbalancedChen.Part3.ActualWResidualCompletion
open ImbalancedChen.Part3.ActualWFineWordAdapter
open ImbalancedChen.Part3.ActualWCloseFullRepair
open ImbalancedChen.Part3.ActualWSameKeyMonomials
open ImbalancedChen.Part3.ActualWSmallThirdAttachment

/-- Structural occurrence trace; no numerical capacity is assumed. -/
theorem finish_trace {α : Type*} (key : α → ℝ) (A : ℝ)
    (input : List α) (g : Bins α) : Trace g input (finish key A g input) := by
  induction input generalizing g with
  | nil => exact Trace.nil g
  | cons p input ih =>
      unfold finish
      split_ifs
      · exact Trace.left g p (ih (putLeft g p))
      · exact Trace.right g p (ih (putRight g p))

/-- Both real complete-program outcomes retain every original occurrence:
first overflow inserts that same slot into the middle, then finishes. -/
theorem complete_trace {α : Type*} (key : α → ℝ) (A B C : ℝ)
    (input : List α) (g : Bins α) : Trace g input (complete key A B C g input) := by
  induction input generalizing g with
  | nil => exact Trace.nil g
  | cons p input ih =>
      unfold complete
      rw [run]
      split_ifs
      · exact Trace.left g p (ih (putLeft g p))
      · exact Trace.middle g p (ih (putMiddle g p))
      · exact Trace.right g p (ih (putRight g p))
      · exact Trace.middle g p (finish_trace key A input (putMiddle g p))

theorem fine_slots_perm (N : ℕ) (sigma A B C : ℝ)
    (labels : Fin 3 → ℕ) (tail : List ℕ) :
    (flatten (fineSlots N sigma A B C labels tail)).Perm
      (labels 0 :: labels 1 :: labels 2 :: tail) := by
  have htr := complete_trace
    (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) A B C
    (labels 2 :: tail) (fineInitial N sigma A labels)
  exact (trace_perm htr).trans
    ((fineInitial_perm N sigma A labels).append_right (labels 2 :: tail))

theorem close_slots_perm (N : ℕ) (sigma D A : ℝ) (label : ℕ) (rest : List ℕ) :
    (flatten (closeSlots N sigma D A label rest)).Perm (label :: rest) := by
  let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
  by_cases hC : 1 ≤ D / (A * key label)
  · have hpart := actualTwoCapacityGreedy_partition key A rest
    have hmove :
        ((actualTwoCapacityGreedy key A rest).1 ++ [label] ++
          (actualTwoCapacityGreedy key A rest).2).Perm
          ([label] ++ ((actualTwoCapacityGreedy key A rest).1 ++
            (actualTwoCapacityGreedy key A rest).2)) := by
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := (actualTwoCapacityGreedy key A rest).1)
          (l₂ := [label])).append_right (actualTwoCapacityGreedy key A rest).2
    simpa only [closeSlots, if_pos hC, flatten] using
      hmove.trans (hpart.perm.append_left [label])
  · simpa only [closeSlots, if_neg hC, flatten, List.append_nil] using
      (actualTwoCapacityGreedy_partition key A (label :: rest)).perm

/-- The SAME row4 program used by the physical monomial theorem is one
fixed whole-word permutation, including the true below-one repair. -/
theorem row4_slots_perm (N : ℕ) (e sigma : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) (t : Fin 3 → ℝ) (A : ℝ)
    (labels : Fin 3 → ℕ) (tail : List ℕ) :
    (flatten (row4Slots N e sigma m j t A labels tail)).Perm
      (labels 0 :: labels 1 :: labels 2 :: tail) := by
  unfold row4Slots
  split_ifs
  · exact close_slots_perm N sigma _ A (labels 0) (labels 1 :: labels 2 :: tail)
  · exact fine_slots_perm N sigma A _ _ labels tail

/-- Nonzero native rho forces squarefreeness of the complete modulus,
hence also of any displayed rough factor n. This is proved from actual
physical support, not imposed as a new source filter. -/
theorem native_nonzero_rough_squarefree {e h epsilon : ℝ} {m N small n : ℕ}
    (hactive : rho e h epsilon m N (small * n) ≠ 0) : Squarefree n := by
  have hn : actualExtendedThirdCompactRho e h m N N ((N : ℝ) ^ (epsilon ^ 2))
      ((N : ℝ) ^ (19 / 96 : ℝ)) ((N : ℝ) ^ epsilon) (small * n) ≠ 0 := by
    simpa only [rho, P1ActualCompactUpperLowRankFixedLevelBV.actualAttachedCompact_rho_eq]
      using hactive
  obtain ⟨_, _, _, _, _, _, _, hmem, _, _, _⟩ :=
    compact_upper_active_integer_lowrank_binding e h m N N
      ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ))
      ((N : ℝ) ^ epsilon) (small * n) hn
  exact Squarefree.squarefree_of_dvd (dvd_mul_left n small)
    (actualExtendedThirdCompactModuli_squarefree e h m N N _ _ hmem)

/-- Insert Mobius twice to reuse the original sorted-word multiplicity
identity for the ACTUAL native source; nonsquarefree products already vanish. -/
theorem native_moebius_insertion (e h epsilon : ℝ) (m N small n : ℕ) (F : ℕ → ℝ) :
    (ArithmeticFunction.moebius n : ℝ) *
        ((ArithmeticFunction.moebius n : ℝ) * rho e h epsilon m N (small * n) * F (small * n)) =
      rho e h epsilon m N (small * n) * F (small * n) := by
  by_cases hzero : rho e h epsilon m N (small * n) = 0
  · simp only [hzero, mul_zero, zero_mul]
  · have hsq : (ArithmeticFunction.moebius n : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (native_nonzero_rough_squarefree hzero)
    calc
      _ = (ArithmeticFunction.moebius n : ℝ) ^ 2 *
          rho e h epsilon m N (small * n) * F (small * n) := by ring
      _ = _ := by rw [hsq, one_mul]

/-- The original sorted source, including its literal original label
multiplicity. No replacement scalar and no omitted squarefree gate. -/
theorem native_sorted_to_ordered (e h epsilon : ℝ) (m N small : ℕ)
    (hN : 1 ≤ N) {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (word : List ℕ) (horder : word.Pairwise (· ≥ ·)) (c : ℝ) (F : ℕ → ℝ) :
    c * (∑ n ∈ ((actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) word).filter
        List.SortedGT).image List.prod,
      rho e h epsilon m N (small * n) * F (small * n)) =
    (c / (actualPrimeFineWordMultiplicity word : ℝ)) *
      ∑ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) word,
        rho e h epsilon m N (small * ps.prod) * F (small * ps.prod) := by
  have hs := actualPrimeFineWord_original_scalar hN hsigma word horder 1 c
    (fun n => (ArithmeticFunction.moebius n : ℝ) *
      rho e h epsilon m N (small * n) * F (small * n))
  simpa only [one_mul, native_moebius_insertion] using hs.symm

/-- Exact ordered box expansion on the row4 program's own fixed slots. -/
theorem row4_signed_box_regroup (N : ℕ) (e sigma : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) (t : Fin 3 → ℝ) (A : ℝ)
    (labels : Fin 3 → ℕ) (tail : List ℕ) (c : ℝ) (F : ℕ → ℝ) :
    let out := row4Slots N e sigma m j t A labels tail
    let T1 := actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left
    let T2 := actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle
    let T3 := actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right
    (∑ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma)
        (labels 0 :: labels 1 :: labels 2 :: tail), c * F ps.prod) =
      ∑ a ∈ T1.image List.prod, ∑ b ∈ T2.image List.prod, ∑ d ∈ T3.image List.prod,
        (c * (out.left.length.factorial : ℝ) * (out.middle.length.factorial : ℝ) *
          (out.right.length.factorial : ℝ)) *
          actualNormalizedPrimeTupleCoefficient T1 out.left.length a *
          actualNormalizedPrimeTupleCoefficient T2 out.middle.length b *
          actualNormalizedPrimeTupleCoefficient T3 out.right.length d * F (a * b * d) := by
  let out := row4Slots N e sigma m j t A labels tail
  rw [← actualPrimeSlotBox_product_sum_perm (actualPrimeFineLabelFinset N sigma)
    (row4_slots_perm N e sigma m j t A labels tail) (fun n => c * F n)]
  simp only [flatten]
  rw [actualPrimeSlotBox_product_sum_append]
  simp_rw [actualPrimeSlotBox_product_sum_append]
  simpa only [flatten, mul_assoc] using actualPrimeTuple_threeGroup_sum_normalized
    (actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left)
    (actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle)
    (actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right)
    out.left.length out.middle.length out.right.length c F

/-- Three independent one-bounded tuple-convolution factors on precisely
those slots. Repeated interval labels and prime collisions are included. -/
theorem row4_group_one_bounds (N : ℕ) (e sigma : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) (t : Fin 3 → ℝ) (A : ℝ)
    (labels : Fin 3 → ℕ) (tail : List ℕ) (a b d : ℕ) :
    let out := row4Slots N e sigma m j t A labels tail
    |actualNormalizedPrimeTupleCoefficient
      (actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left) out.left.length a| ≤ 1 ∧
    |actualNormalizedPrimeTupleCoefficient
      (actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle) out.middle.length b| ≤ 1 ∧
    |actualNormalizedPrimeTupleCoefficient
      (actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right) out.right.length d| ≤ 1 := by
  exact ⟨actualPrimeFineWord_normalized_abs_le_one N sigma _ a,
    actualPrimeFineWord_normalized_abs_le_one N sigma _ b,
    actualPrimeFineWord_normalized_abs_le_one N sigma _ d⟩

/-- The original sorted native-rho source on a REAL row4 whole box. The
scalar c/Mword and the three restoring factorials occur exactly once.
The SAME rho is still evaluated at the complete physical small*a*b*d;
no claim of removing its remaining coupled causal gate is made. -/
theorem row4_sorted_native_three_groups (e h epsilon sigma : ℝ) (m N small : ℕ)
    (hN : 1 ≤ N) (hsigma : 0 ≤ sigma) (j : ActualExtendedThirdDyadicLabel m)
    (t : Fin 3 → ℝ) (A : ℝ) (labels : Fin 3 → ℕ) (tail : List ℕ)
    (horder : (labels 0 :: labels 1 :: labels 2 :: tail).Pairwise (· ≥ ·))
    (c : ℝ) (F : ℕ → ℝ) :
    let word := labels 0 :: labels 1 :: labels 2 :: tail
    let out := row4Slots N e sigma m j t A labels tail
    let T1 := actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left
    let T2 := actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle
    let T3 := actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right
    c * (∑ n ∈ ((actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) word).filter
        List.SortedGT).image List.prod,
        rho e h epsilon m N (small * n) * F (small * n)) =
      ∑ a ∈ T1.image List.prod, ∑ b ∈ T2.image List.prod, ∑ d ∈ T3.image List.prod,
        ((c / (actualPrimeFineWordMultiplicity word : ℝ)) *
          (out.left.length.factorial : ℝ) * (out.middle.length.factorial : ℝ) *
          (out.right.length.factorial : ℝ)) *
          actualNormalizedPrimeTupleCoefficient T1 out.left.length a *
          actualNormalizedPrimeTupleCoefficient T2 out.middle.length b *
          actualNormalizedPrimeTupleCoefficient T3 out.right.length d *
          (rho e h epsilon m N (small * (a * b * d)) * F (small * (a * b * d))) := by
  rw [native_sorted_to_ordered e h epsilon m N small hN hsigma _ horder c F,
    Finset.mul_sum]
  exact row4_signed_box_regroup N e sigma m j t A labels tail
    (c / (actualPrimeFineWordMultiplicity (labels 0 :: labels 1 :: labels 2 :: tail) : ℝ))
    (fun n => rho e h epsilon m N (small * n) * F (small * n))

/-- Extend the constructed high frontier to the actual W-winning row4,
using the SAME program whose signed whole-box sum was regrouped above. -/
theorem actual_high_row4_realization {e h epsilon sigma A : ℝ} {m N q : ℕ}
    (H : HighFrontier e h epsilon m N q)
    (hN : 2 ≤ N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hsigma0 : 0 ≤ sigma) (hsigma : sigma ≤ e / 64)
    (hwidth : sigma * (H.rank + 1) ≤ e / 2) (heps : epsilon ≤ e / 128)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (howned : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 H.state.selectedPrefix) ∈
      actualExtendedThirdOwnedCell m j)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ VariableEnvelope.mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hwinner : actualExtendedThirdLeastWinningIndex e m j = 4)
    (p labels : Fin 3 → ℕ) (primeTail labelTail : List ℕ)
    (hshape : H.state.selectedPrefix.reverse = p 0 :: p 1 :: p 2 :: primeTail)
    (hatom : H.state.selectedPrefix.reverse ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma)
      (labels 0 :: labels 1 :: labels 2 :: labelTail))
    (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ)) :
    let out := row4Slots N e sigma m j t A labels labelTail
    ∃ ls ms rs,
      ls ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left ∧
      ms ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle ∧
      rs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right ∧
      ls.prod * ms.prod * (H.small * rs.prod) = q ∧ (ls.prod : ℝ) ≤ A ∧
      Monomials (N : ℝ) (e / 128) A (ls.prod : ℝ) (ms.prod : ℝ) (H.small * rs.prod : ℕ) ∧
      ∀ x : ℝ, 1 < x → LocalMonomials (N : ℝ) x (e / 128) A
        (ls.prod : ℝ) (ms.prod : ℝ) (H.small * rs.prod : ℕ) := by
  have hsmall : 0 < H.small := Nat.pos_of_ne_zero
    (actualSmallRosserSupport_squarefree N N _ H.small_mem).ne_zero
  obtain ⟨_, _, hwhole⟩ := actual_row4_atom_small_attachment
    e h sigma epsilon m N N H.rank H.rank_ge
    ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho) (fun _ => 1)
    H.state H.original hN he0 he hsigma0 hsigma hwidth heps hmesh
    hj howned hfull ht hwinner p labels primeTail labelTail hshape hatom
    A hA hAupper H.small hsmall H.small_size.le
  obtain ⟨ls, ms, rs, hls, hms, hrs, hprod, hleft, hmono, hlocal⟩ :=
    hwhole H.state.selectedPrefix.reverse hatom
  refine ⟨ls, ms, rs, hls, hms, hrs, ?_, hleft, hmono, hlocal⟩
  exact (by simpa only [List.prod_reverse] using hprod).trans H.full_product.symm

end
end ImbalancedChen.P1ActualHighWWholeBoxNativeRegroup
