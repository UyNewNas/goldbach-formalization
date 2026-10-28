import ImbalancedChen.P2ActualPairWholeQWallPayment

/-!
# Actual canonical-tent admission walls with FIXED joint cap heights

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The joint form includes both external pair coordinates. Its intercept is
one of the fixed concrete plan's actual cap alphabet, chosen before N.
This closes the varying-pairRoot-intercept gap for these actual admission
walls and consumes a whole physical-q arithmetic payment. It does not
identify this tent subbank with complete adopted W/L56, nor conclude the
full beta-attached same-rho density convergence.
-/

namespace ImbalancedChen.P2CanonicalTentJointAdmissionWallPayment

noncomputable section
open scoped Classical BigOperators
open P2LowerCapPlanIntegerRetention P2OriginalPairRootRoughProducer
open P2OriginalPairSourceReceiver P2OriginalCanonicalPairTentBank
open P2CanonicalTentFiniteCapsAndCoarsePayment P2ActualPairJointPrefixWallCarrier
open P2ActualPairWholeQWallPayment P2LowerFiniteCellRounding P5SelectedMaskTransport

abbrev CapIndex (R : PairRange) (mesh : ℕ) (buffer seed : ℚ) :=
  Fin (Fintype.card {c : ℝ // c ∈ capAlphabet R mesh buffer seed})

def fixedCapHeights (R : PairRange) (mesh : ℕ) (buffer seed : ℚ) :
    CapIndex R mesh buffer seed → ℝ :=
  fun i => ((Fintype.equivFin {c : ℝ // c ∈ capAlphabet R mesh buffer seed}).symm i).val

theorem actual_cap_has_fixed_index (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    {c : ℝ} (hc : c ∈ capAlphabet R mesh buffer seed) :
    ∃ i : CapIndex R mesh buffer seed, fixedCapHeights R mesh buffer seed i = c := by
  refine ⟨Fintype.equivFin _ ⟨c, hc⟩, ?_⟩
  simp only [fixedCapHeights, Equiv.symm_apply_apply]

/-- Root and preceding rough slots have coefficient one; the current
rough slot has coefficient three. The cap is the fixed affine height. -/
def jointAdmissionForm (j : ℕ) : (Fin (2 + (j + 1)) → ℝ) →L[ℝ] ℝ :=
  (∑ i : Fin (2 + (j + 1)), ContinuousLinearMap.proj i) +
    (2 : ℝ) • ContinuousLinearMap.proj (Fin.last (2 + j))

def admissionForms (R : PairRange) (mesh : ℕ) (buffer seed : ℚ) (j : ℕ) :
    CapIndex R mesh buffer seed → (Fin (2 + (j + 1)) → ℝ) →L[ℝ] ℝ :=
  fun _ => jointAdmissionForm j

theorem jointAdmissionForm_ne_zero (j : ℕ) : jointAdmissionForm j ≠ 0 := by
  intro h
  have heq := congrArg (fun f : (Fin (2 + (j + 1)) → ℝ) →L[ℝ] ℝ => f (fun _ => 1)) h
  simp [jointAdmissionForm] at heq
  have hj : 0 ≤ (j : ℝ) := by positivity
  norm_num at heq
  linarith

private theorem take_succ_getD (xs : List ℝ) (j : ℕ) (hj : j < xs.length) :
    xs.take (j + 1) = xs.take j ++ [xs.getD j 0] := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
      cases j with
      | zero => simp
      | succ j =>
          simpa only [List.take_succ_cons, List.getD_cons_succ, List.cons_append] using
            congrArg (List.cons x) (ih j (by simpa using hj))

/-- Every variable in the true incoming admission is a coordinate of the
same actual joint prime tuple used by the arithmetic wall payment. -/
theorem jointAdmissionForm_actual_coordinate_identity (N : ℕ) (p : ℕ × ℕ)
    (r j : ℕ) (hj : j < r.primeFactorsList.length) :
    jointAdmissionForm j (actualPrimeTupleLog N (jointPrefix (j + 1) p r)) =
      (pairRoot N p 0).word.sum +
        ((physicalWord N r.primeFactorsList).take j).sum +
          3 * (physicalWord N r.primeFactorsList).getD j 0 := by
  have hof := jointPrefix_ofFn p (show j + 1 ≤ r.primeFactorsList.length by omega)
  have hmap := congrArg (List.map (coordinate N)) hof
  rw [List.map_ofFn] at hmap
  have hsum := congrArg List.sum hmap
  rw [List.sum_ofFn] at hsum
  change (∑ i, actualPrimeTupleLog N (jointPrefix (j + 1) p r) i) =
    ((jointWord (j + 1) p r).map (coordinate N)).sum at hsum
  have hlast : jointPrefix (j + 1) p r (Fin.last (2 + j)) =
      P2CanonicalWallFullResidualPayment.canonicalPrefix (j + 1) r (Fin.last j) := by
    simp only [jointPrefix, P2CanonicalWallFullResidualPayment.canonicalPrefix,
      primeHistoryTuple, List.reverse_reverse, Fin.val_last]
    rw [show 2 + j = j + 2 by omega]
    simp only [jointWord, List.getD_cons_succ]
  have hcoord := canonical_last_coordinate N r j
  change coordinate N
    (P2CanonicalWallFullResidualPayment.canonicalPrefix (j + 1) r (Fin.last j)) =
      (physicalWord N r.primeFactorsList).getD j 0 at hcoord
  have hlastCoord : actualPrimeTupleLog N (jointPrefix (j + 1) p r) (Fin.last (2 + j)) =
      (physicalWord N r.primeFactorsList).getD j 0 := by
    change coordinate N _ = _
    rw [hlast, hcoord]
  have hjword : j < (physicalWord N r.primeFactorsList).length := by
    simpa only [physicalWord, List.length_map, List.length_reverse] using hj
  have htake := take_succ_getD (physicalWord N r.primeFactorsList) j hjword
  simp only [jointAdmissionForm, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hsum, hlastCoord]
  have hsumTake : ((r.primeFactorsList.reverse.take (j + 1)).map (coordinate N)).sum =
      ((physicalWord N r.primeFactorsList).take j).sum +
        (physicalWord N r.primeFactorsList).getD j 0 := by
    rw [List.map_take]
    change ((physicalWord N r.primeFactorsList).take (j + 1)).sum = _
    rw [htake, List.sum_append]
    simp only [List.sum_cons, List.sum_nil, add_zero]
  simp only [jointWord, List.map_cons, List.sum_cons, pairRoot]
  rw [hsumTake]
  simp only [List.sum_cons, List.sum_nil, add_zero]
  ring

/-- The actual frozen admission wall enters the fixed joint catalogue.
Its cap comes from the independently computed plan's alphabet; the seed's
word-coordinate independence is explicit and no c(N,p) is introduced. -/
theorem actual_admission_enters_fixed_joint_wall
    (R : PairRange) (mesh : ℕ) (buffer seed : ℚ) (N enum : ℕ) (p : ℕ × ℕ)
    (omega : ℝ) (r j : ℕ) (width : ℝ)
    (hp : p ∈ sixthSupport N)
    (hr : r ∈ universe N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent))
    (hj : j < r.primeFactorsList.length)
    (hw : |(run (plan R mesh buffer seed) R.epsilon ceiling (pairRoot N p seed)
      ((physicalWord N r.primeFactorsList).take j)).word.sum +
        3 * (physicalWord N r.primeFactorsList).getD j 0 -
      (run (plan R mesh buffer seed) R.epsilon ceiling (pairRoot N p seed)
        ((physicalWord N r.primeFactorsList).take j)).cap| ≤ width) :
    ((p.1 * p.2) * r) ∈ jointWallProducts N enum omega
      (admissionForms R mesh buffer seed j) (fixedCapHeights R mesh buffer seed) width := by
  obtain ⟨c, hc, hwall⟩ := actual_pair_admission_finite_cap_wall
    R mesh buffer seed N p (physicalWord N r.primeFactorsList) j width hw
  obtain ⟨i, hi⟩ := actual_cap_has_fixed_index R mesh buffer seed hc
  apply Finset.mem_image.mpr
  refine ⟨(p, r), ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨hp, hr⟩, by omega, i, ?_⟩
  change |jointAdmissionForm j (actualPrimeTupleLog N (jointPrefix (j + 1) p r)) -
    fixedCapHeights R mesh buffer seed i| ≤ width
  rw [jointAdmissionForm_actual_coordinate_identity N p r j hj, hi]
  simpa only [pairRoot] using hwall

/-- The fixed catalogue is independent of N,p and contains the true
admissions just proved above; the WHOLE physical q charge is paid before N.
No full beta-attached norm or adoption identity is a premise/conclusion. -/
theorem exists_actual_joint_admission_whole_q_payment
    (R : PairRange) (mesh : ℕ) (buffer seed : ℚ) (j : ℕ)
    (omega : ℝ) (homega : 0 < omega) (hgap : omega < aExponent)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ enum : ℕ,
      ∀ (keep : ℕ × ℕ → List ℕ → Bool) (tau : ℝ),
        wholeQWallCharge keep N enum omega tau
          (admissionForms R mesh buffer seed j) (fixedCapHeights R mesh buffer seed) delta < eta := by
  exact exists_uniform_whole_q_joint_wall_payment omega homega hgap
    (admissionForms R mesh buffer seed j) (fixedCapHeights R mesh buffer seed)
    (fun _ => jointAdmissionForm_ne_zero j) eta heta

end
end ImbalancedChen.P2CanonicalTentJointAdmissionWallPayment
