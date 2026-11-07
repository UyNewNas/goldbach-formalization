import ImbalancedChen.P2OriginalMixedThirdBranchTableTrace
import ImbalancedChen.P1SignedExitCoefficientDifference
import ImbalancedChen.FixedEvenRoughCoefficients
import ImbalancedChen.FirstExitFrontierInvariants
import ImbalancedChen.FirstExitValidSelection

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The rank-three-only stage of the actual mixed compiler is compared with
its seed stage. Later fourth/fifth updates belong to the subsequent I4/I5
steps and are not silently included in I3. Its signed fixed rough modulus
coefficient is selected once before any tested integer or source family.
The reached frontier and its source labels are computed from actual Trace
policies. This does not identify complete small-prime-attached rho_N.
-/
namespace ImbalancedChen.P2OriginalMixedThirdSignedFrontier
noncomputable section
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalLowerSelectedCapConstructor (Code BranchTable)
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerAffineTieSelector
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalMixedThirdWTentSelector
open P2OriginalMixedThirdBranchTableTrace

structure ThirdStage (mesh : ℕ) where
  start : CompactStart
  rho : ℝ
  screen : ℚ
  buffer : ℚ
  delta : ℚ
  inherited : Code mesh → LabeledBranch 5
  argument : Fin 6 → Code mesh → SourceForm → ℚ

def emptyRows (mesh : ℕ) : BranchTable mesh := ⟨fun _ _ => none⟩

def ThirdStage.seedPlan {mesh : ℕ} (D : ThirdStage mesh) : CapPlan 5 mesh :=
  compactPlan D.start (emptyRows mesh) D.rho

def ThirdStage.thirdPlan {mesh : ℕ} (D : ThirdStage mesh) : CapPlan 5 mesh :=
  mixedPlan D.start (emptyRows mesh) D.rho D.screen D.buffer D.delta
    D.inherited D.argument

def ThirdStage.oldPolicy {mesh : ℕ} (D : ThirdStage mesh) (N : ℕ) :
    Bool → List ℕ → Bool :=
  evenFirstExitPolicy (retainEven D.seedPlan (D.start.epsilon : ℝ)
    (startCutoff D.start.start : ℝ) (baselineCap D.rho) N)

def ThirdStage.newPolicy {mesh : ℕ} (D : ThirdStage mesh) (N : ℕ) :
    Bool → List ℕ → Bool :=
  evenFirstExitPolicy (retainEven D.thirdPlan (D.start.epsilon : ℝ)
    (startCutoff D.start.start : ℝ) (baselineCap D.rho) N)

/-- Choice at rank three is made after its admission. Hence no choice can
change any of the retained tests through that rank. This is proved for the
actual Trace evaluator, not assumed as a splice-interface equality. -/
private theorem retainEven_le_three {mesh : ℕ} (P Q : CapPlan 5 mesh)
    (a w seed : ℝ) (N : ℕ) (pre : List ℕ) (hlen : pre.length ≤ 3) :
    retainEven P a w seed N pre = retainEven Q a w seed N pre := by
  cases pre with
  | nil => rfl
  | cons p ps =>
    cases ps with
    | nil =>
      simp [retainEven, integerTrace, physicalWord, run, root, step,
        planChoice, admission, CapChoice.freeze]
    | cons q qs =>
      cases qs with
      | nil =>
        simp [retainEven, integerTrace, physicalWord, run, root, step,
          planChoice, admission, CapChoice.freeze]
      | cons r rs =>
        cases rs with
        | nil =>
          simp [retainEven, integerTrace, physicalWord, run, root, step,
            planChoice, admission, CapChoice.freeze]
        | cons s ss => simp only [List.length_cons] at hlen; omega

theorem ThirdStage.newPolicy_eq_actual_depthSplice {mesh : ℕ}
    (D : ThirdStage mesh) (N : ℕ) :
    firstExitDepthSplicePolicy 3 (D.oldPolicy N) (D.newPolicy N) =
      D.newPolicy N := by
  funext positive pre
  by_cases hlen : pre.length ≤ 3
  · simp only [firstExitDepthSplicePolicy, if_pos hlen]
    unfold ThirdStage.oldPolicy ThirdStage.newPolicy evenFirstExitPolicy
    rw [retainEven_le_three D.seedPlan D.thirdPlan _ _ _ N pre hlen]
  · simp only [firstExitDepthSplicePolicy, if_neg hlen]

/-- Source labels are read from the geometric prefix code; neither local
arithmetic divisor indicators nor outer source weights enter this lookup. -/
def ThirdStage.sourceLabel {mesh : ℕ} (D : ThirdStage mesh) (N : ℕ)
    (pre : List ℕ) : Option SelectedBranchData :=
  mixedWinner D.start D.rho D.screen D.buffer D.delta D.inherited D.argument
    (incomingCode (D.start.epsilon : ℝ) (startCutoff D.start.start : ℝ)
      5 mesh 3 (marked (physicalWord N pre)))

/-- Actual reached states retain history, sign, accumulated local mass and
unprocessed prime carrier, with their independently computed source label. -/
def ThirdStage.taggedFrontier {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z : ℝ) (h : ℕ → ℝ) :
    List (FirstExitDepthState ℕ × Option SelectedBranchData) :=
  (firstExitDepthFrontier 3 (D.oldPolicy N) h [] true 1
    (roughPrimeUniverse N cap 0 z)).map
      (fun state => (state, D.sourceLabel N state.selectedPrefix))

private theorem eq_three_of_length (pre : List ℕ) (hlen : pre.length = 3) :
    ∃ p3 p2 p1, pre = [p3,p2,p1] := by
  cases pre with
  | nil => simp at hlen
  | cons p3 ps =>
    cases ps with
    | nil => simp at hlen
    | cons p2 qs =>
      cases qs with
      | nil => simp at hlen
      | cons p1 rs =>
        have hrs : rs.length = 0 := by simp only [List.length_cons] at hlen; omega
        have he : rs = [] := List.length_eq_zero.mp hrs
        exact ⟨p3,p2,p1,by rw [he]⟩

private theorem valid_three_trace_retained {mesh : ℕ} (P : CapPlan 5 mesh)
    (a w seed : ℝ) (N : ℕ) (pre : List ℕ) (hlen : pre.length = 3)
    (hv : FirstExitValidSelection
      (evenFirstExitPolicy (retainEven P a w seed N)) [] true pre.reverse) :
    retainEven P a w seed N pre = true := by
  obtain ⟨p3,p2,p1,rfl⟩ := eq_three_of_length pre hlen
  have htwo : retainEven P a w seed N [p2,p1] = true := by
    simpa [FirstExitValidSelection, evenFirstExitPolicy] using hv
  rw [odd_rank_bypass P a w seed N p3 [p2,p1] (by simp) (by norm_num)]
  exact htwo

/-- Every actual tagged frontier state has passed the original seed tests.
Its sign is genuinely odd and its label is the literal geometric lookup. -/
theorem ThirdStage.taggedFrontier_invariants {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z : ℝ) (h : ℕ → ℝ)
    (tag : FirstExitDepthState ℕ × Option SelectedBranchData)
    (htag : tag ∈ D.taggedFrontier N cap z h) :
    tag.1.selectedPrefix.length = 3 ∧ tag.1.positive = false ∧
      tag.1.mass = (tag.1.selectedPrefix.map h).prod ∧
      tag.1.selectedPrefix.reverse <+ roughPrimeUniverse N cap 0 z ∧
      tag.2 = D.sourceLabel N tag.1.selectedPrefix ∧
      retainEven D.seedPlan (D.start.epsilon : ℝ)
        (startCutoff D.start.start : ℝ) (baselineCap D.rho)
        N tag.1.selectedPrefix = true := by
  obtain ⟨state, hs, rfl⟩ := List.mem_map.mp htag
  have hlen : state.selectedPrefix.length = 3 :=
    firstExitDepthFrontier_selected_length 3 (D.oldPolicy N) h []
      (roughPrimeUniverse N cap 0 z) true 1 (by simp) state hs
  have hsign := mem_firstExitDepthFrontier_positive_eq_evenListLength
    3 (D.oldPolicy N) h (roughPrimeUniverse N cap 0 z) state hs
  have hsign' : state.positive = false := by
    obtain ⟨p3,p2,p1,hpre⟩ := eq_three_of_length state.selectedPrefix hlen
    simpa [hpre, evenListLength] using hsign
  have hmass := mem_firstExitDepthFrontier_mass_eq_selected_prod
    3 (D.oldPolicy N) h (roughPrimeUniverse N cap 0 z) state hs
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist
    3 (D.oldPolicy N) h (roughPrimeUniverse N cap 0 z) state hs
  have hl := firstExitDepthFrontier_toLeaf_mem 3 (D.oldPolicy N) h []
    (roughPrimeUniverse N cap 0 z) true 1 state hs
  obtain ⟨chosen, _, hv, heq⟩ := exists_validSelection_of_mem_firstExitRetainedLeaves
    (D.oldPolicy N) h [] (roughPrimeUniverse N cap 0 z) true 1 _ hl
  have hchosen : chosen = state.selectedPrefix.reverse := by
    have hh := congrArg List.reverse heq
    simpa using hh.symm
  rw [hchosen] at hv
  have hret := valid_three_trace_retained D.seedPlan
    (D.start.epsilon : ℝ) (startCutoff D.start.start : ℝ)
    (baselineCap D.rho) N state.selectedPrefix hlen hv
  exact ⟨hlen, hsign', hmass, hsub, rfl, hret⟩

/-- A W-labelled reached state freezes the very same mixed table cap.
The label is extracted from the tagged actual frontier, not supplied as a
free source-form witness unrelated to that state. -/
theorem ThirdStage.tagged_W_trace_cap {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z : ℝ) (h : ℕ → ℝ)
    (tag : FirstExitDepthState ℕ × Option SelectedBranchData)
    (htag : tag ∈ D.taggedFrontier N cap z h) (code : Code mesh)
    (hcode : incomingCode (D.start.epsilon : ℝ) (startCutoff D.start.start : ℝ)
      5 mesh 3 (marked (physicalWord N tag.1.selectedPrefix)) = code)
    (hlabel : tag.2 = some (wRow D.start
      (P2OriginalLowerSelectedCapConstructor.prefixCode 3 code) D.buffer)) :
    (integerTrace D.thirdPlan (D.start.epsilon : ℝ)
      (startCutoff D.start.start : ℝ) (baselineCap D.rho)
      N tag.1.selectedPrefix).cap =
      (P2OriginalLowerWThirdPhysicalRow.wCap D.start
        (P2OriginalLowerSelectedCapConstructor.prefixCode 3 code) D.buffer : ℝ) := by
  have hi := D.taggedFrontier_invariants N cap z h tag htag
  rw [hi.2.2.2.2.1] at hlabel
  unfold ThirdStage.sourceLabel at hlabel
  rw [hcode] at hlabel
  obtain ⟨p3,p2,p1,hpre⟩ := eq_three_of_length tag.1.selectedPrefix hi.1
  have hc : incomingCode (D.start.epsilon : ℝ) (startCutoff D.start.start : ℝ)
      5 mesh 3 (marked (physicalWord N [p3,p2,p1])) = code := by
    simpa only [hpre] using hcode
  rw [hpre]
  exact mixed_W_actual_third_trace D.start (emptyRows mesh) D.rho D.screen
    D.buffer D.delta D.inherited D.argument N p1 p2 p3 code hc hlabel

def ThirdStage.frontierTerm {mesh : ℕ} (D : ThirdStage mesh)
    (N : ℕ) (h : ℕ → ℝ)
    (tag : FirstExitDepthState ℕ × Option SelectedBranchData) : ℝ :=
  firstExitRetainedPolynomial (D.newPolicy N) h tag.1.selectedPrefix
      tag.1.positive tag.1.mass tag.1.remaining -
    firstExitRetainedPolynomial (D.oldPolicy N) h tag.1.selectedPrefix
      tag.1.positive tag.1.mass tag.1.remaining

/-- Exact actual mixed-stage I3 difference at the same seed frontier.
The signs in the reached states are retained rather than overwritten. -/
theorem ThirdStage.actual_third_sub_eq_tagged_frontier {mesh : ℕ}
    (D : ThirdStage mesh) (N cap : ℕ) (z : ℝ) (h : ℕ → ℝ) :
    firstExitRetainedPolynomial (D.newPolicy N) h [] true 1
        (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (D.oldPolicy N) h [] true 1
        (roughPrimeUniverse N cap 0 z) =
      ((D.taggedFrontier N cap z h).map (D.frontierTerm N h)).sum := by
  rw [← D.newPolicy_eq_actual_depthSplice N]
  rw [firstExitRetainedPolynomial_depthSplice_root_sub_eq_frontier_sum]
  simp only [ThirdStage.taggedFrontier, ThirdStage.frontierTerm, List.map_map,
    Function.comp_apply]

def ThirdStage.moduli {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z : ℝ) : Finset ℕ :=
  p1PolicyUnionModuli (D.oldPolicy N) (D.newPolicy N)
    (roughPrimeUniverse N cap 0 z)

/-- Fixed signed NEW-minus-OLD coefficient, with the same modulus on both
sides. It is not its absolute value and is not reselected for n. -/
def ThirdStage.rhoI3 {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z : ℝ) (d : ℕ) : ℝ :=
  (p1PolicyCoefficientDifference (D.oldPolicy N) (D.newPolicy N)
    (roughPrimeUniverse N cap 0 z) d : ℝ)

theorem ThirdStage.same_rho_polynomial_eq_tagged_frontier {mesh : ℕ}
    (D : ThirdStage mesh) (N cap : ℕ) (z : ℝ) (h : ℕ → ℝ) :
    (∑ d ∈ D.moduli N cap z, D.rhoI3 N cap z d * d.primeFactors.prod h) =
      ((D.taggedFrontier N cap z h).map (D.frontierTerm N h)).sum := by
  change (∑ d ∈ p1PolicyUnionModuli (D.oldPolicy N) (D.newPolicy N)
    (roughPrimeUniverse N cap 0 z),
    (p1PolicyCoefficientDifference (D.oldPolicy N) (D.newPolicy N)
      (roughPrimeUniverse N cap 0 z) d : ℝ) * d.primeFactors.prod h) = _
  rw [← p1_retainedPolynomial_sub_eq_union_coefficient_sum
    (D.oldPolicy N) (D.newPolicy N) h (roughPrimeUniverse N cap 0 z)
    (roughPrimeUniverse_nodup N cap 0 z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp)]
  exact D.actual_third_sub_eq_tagged_frontier N cap z h

/-- Same coefficient, exact arithmetic divisor sum, including zero. -/
theorem ThirdStage.same_rho_divisor_eq_tagged_frontier {mesh : ℕ}
    (D : ThirdStage mesh) (N cap : ℕ) (z : ℝ) (n : ℕ) :
    physicalDivisorSum (D.moduli N cap z) (D.rhoI3 N cap z) n =
      ((D.taggedFrontier N cap z (integerDivisorIndicator (n : ℤ))).map
        (D.frontierTerm N (integerDivisorIndicator (n : ℤ)))).sum := by
  have hc := p1_retainedPolynomial_sub_eq_union_divisor_sum
    (D.oldPolicy N) (D.newPolicy N) (roughPrimeUniverse N cap 0 z)
    (roughPrimeUniverse_nodup N cap 0 z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) (n : ℤ)
  have hf := D.actual_third_sub_eq_tagged_frontier N cap z
    (integerDivisorIndicator (n : ℤ))
  have hnat : (n : ℤ).natAbs = n := by simp
  rw [hnat] at hc
  exact hc.symm.trans hf

/-- The count uses N-m with its literal finite source weight. Applications
with a residue interpretation retain their own m≤N support condition. -/
def ThirdStage.sourceCount {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z : ℝ) (A : Finset ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ m ∈ A, weight m *
    physicalDivisorSum (D.moduli N cap z) (D.rhoI3 N cap z) (N-m)

def ThirdStage.exactCoprimeMean {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z : ℝ) (A : Finset ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D.moduli N cap z, D.rhoI3 N cap z d *
    ((∑ m ∈ A, if Nat.Coprime m d then weight m else 0) / (Nat.totient d : ℝ))

def ThirdStage.signedDiscrepancy {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z : ℝ) (A : Finset ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D.moduli N cap z, D.rhoI3 N cap z d *
    ((∑ m ∈ A, if d ∣ N-m then weight m else 0) -
      (∑ m ∈ A, if Nat.Coprime m d then weight m else 0) / (Nat.totient d : ℝ))

theorem ThirdStage.sourceCount_eq_same_rho_count {mesh : ℕ}
    (D : ThirdStage mesh) (N cap : ℕ) (z : ℝ)
    (A : Finset ℕ) (weight : ℕ → ℝ) :
    D.sourceCount N cap z A weight =
      ∑ d ∈ D.moduli N cap z, D.rhoI3 N cap z d *
        (∑ m ∈ A, if d ∣ N-m then weight m else 0) := by
  unfold ThirdStage.sourceCount physicalDivisorSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hdm : d ∣ N-m <;> simp [hdm, mul_comm]

/-- The identical fixed signed rho occurs in the count and exact coprime
mean. No total mass or absolute discrepancy is substituted. -/
theorem ThirdStage.signedDiscrepancy_eq_count_sub_exact_mean {mesh : ℕ}
    (D : ThirdStage mesh) (N cap : ℕ) (z : ℝ)
    (A : Finset ℕ) (weight : ℕ → ℝ) :
    D.signedDiscrepancy N cap z A weight =
      D.sourceCount N cap z A weight - D.exactCoprimeMean N cap z A weight := by
  rw [D.sourceCount_eq_same_rho_count]
  unfold ThirdStage.signedDiscrepancy ThirdStage.exactCoprimeMean
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- A signed I3 discrepancy identity for the actual computed third-stage
Trace and source labels, retaining the whole exact coprime mean. -/
theorem ThirdStage.actual_trace_signed_discrepancy {mesh : ℕ}
    (D : ThirdStage mesh) (N cap : ℕ) (z : ℝ)
    (A : Finset ℕ) (weight : ℕ → ℝ) :
    D.signedDiscrepancy N cap z A weight =
      (∑ m ∈ A, weight m *
        ((D.taggedFrontier N cap z (integerDivisorIndicator ((N-m : ℕ) : ℤ))).map
          (D.frontierTerm N (integerDivisorIndicator ((N-m : ℕ) : ℤ)))).sum) -
      D.exactCoprimeMean N cap z A weight := by
  rw [D.signedDiscrepancy_eq_count_sub_exact_mean]
  unfold ThirdStage.sourceCount
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [D.same_rho_divisor_eq_tagged_frontier]

end
end ImbalancedChen.P2OriginalMixedThirdSignedFrontier
