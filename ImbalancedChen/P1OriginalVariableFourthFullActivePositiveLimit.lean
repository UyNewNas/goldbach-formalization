import ImbalancedChen.P1OriginalVariableFourthActiveOnly

/-!
Genuine actual positive-source means for the FULL active variable fourth.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The original sourceBranch includes the actual inclusive omega cutoff even
when its coarse mesh box crosses omega. Its original firstStop false branch
is empty. Finite mixed affine gates pay both the rough face and exact row
box faces; no lower mesh endpoint or global profile continuity is assumed.
Bounded PLUS quotient replacement then proves the arithmetic branch mean.
-/

namespace ImbalancedChen.P1OriginalVariableFourthFullActivePositiveLimit
noncomputable section
open Filter Topology MeasureTheory Set
open scoped Classical BigOperators
open HistoricalThirdCoarse VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P1OriginalCoarseContinuation
open HistoricalThirdCoarse.P1OriginalFourth
open P1FourthFullCellIntegral
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthCellTestLimit
open P1OriginalVariableFourthSourceLimit
open P1OriginalVariableFourthEligibilityPartition
open P1OriginalVariableFourthBoundedSourceLimit
open P1OriginalVariableFourthFullSourceActivation
open P1OriginalVariableFourthActiveOnly

/-- Original six strict rows followed by the inclusive rough face. -/
def activeForms : Fin (6 + 1) → Point →L[ℝ] ℝ :=
  Fin.append gateForms (fun _ : Fin 1 => -ContinuousLinearMap.proj (2 : Fin 4))

def activeBounds (old seed omega : ℝ) : Fin (6 + 1) → ℝ :=
  Fin.append (gateBounds old seed) (fun _ : Fin 1 => -omega)

theorem activeForms_ne_zero : ∀ i, activeForms i ≠ 0 := by
  have hp : (ContinuousLinearMap.proj (2 : Fin 4) : Point →L[ℝ] ℝ) ≠ 0 := by
    intro h
    have hh := congrArg (fun F : Point →L[ℝ] ℝ => F (fun _ => 1)) h
    simp at hh
  simp only [activeForms, Fin.forall_fin_add, Fin.append_left, Fin.append_right]
  exact ⟨gateForms_ne_zero, fun _ => neg_ne_zero.mpr hp⟩

/-- Actual mixed-gate prime transport on a full active source atom.
The cutoff omega is pointwise; the mesh cell may straddle it. -/
theorem tendsto_active_source_atom_test
    (e chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (j : FourthCell m) (rows : Finset ProducerRow) (s : Pattern rows)
    (f : Point → ℝ) (hf : ContinuousOn f (univ.pi (fun _ : Fin 4 => Icc a (19 / 96 : ℝ)))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
      ((sourceBranch e chi m omega (j, true) ∩ wallAtom rows s).indicator f)) atTop
      (𝓝 (∫ t in logPrimeBox (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)) ∩
          (sourceBranch e chi m omega (j, true) ∩ wallAtom rows s),
        f t * ∏ i, 1 / t i)) := by
  rw [sourceBranch_eq_firstStop_if]
  by_cases hs : firstStopCellCheck e m j = true
  · simp only [if_pos hs]
    let lo := logPrimeMeshLo 0 (19 / 96) m j
    let hi := logPrimeMeshHi 0 (19 / 96) m j
    let seed := branchSeed e chi m (j, true)
    apply tendsto_test_source_wallAtom a (19 / 96) ha haRho
      (primeIcoBoxGateForms activeForms) (primeIcoBoxGateBounds lo hi (activeBounds (initial e) seed omega))
      (primeIcoBoxGateForms_ne_zero activeForms activeForms_ne_zero)
      (meshBranch m omega (j, true) ∩ primeAffineGateRegion gateForms (gateBounds (initial e) seed))
      ((measurableSet_meshBranch m omega (j, true)).inter (measurableSet_primeAffineGateRegion _ _))
      ?_ ?_ rows s f hf
    · intro t ht
      obtain ⟨hb, hg⟩ := (mem_primeIcoBoxStrictGateRegion lo hi activeForms
        (activeBounds (initial e) seed omega) t).mp ht
      have hg' : (∀ i : Fin 6, gateForms i t < gateBounds (initial e) seed i) ∧
          (∀ _ : Fin 1, omega < t 2) := by
        simpa only [primeAffineGateRegion, mem_setOf_eq, activeForms, activeBounds,
          Fin.forall_fin_add, Fin.append_left, Fin.append_right, neg_apply,
          ContinuousLinearMap.proj_apply, neg_lt_neg_iff] using hg
      exact ⟨⟨mem_logPrimeBox.mpr (fun i => ⟨(hb i).1.le, (hb i).2⟩),
        by simpa [activationRegion] using (hg'.2 0).le⟩, hg'.1⟩
    · intro t ht
      have hrough : omega ≤ t 2 := by simpa [activationRegion] using ht.1.2
      have hactive : ∀ i, activeForms i t ≤ activeBounds (initial e) seed omega i := by
        simp only [activeForms, activeBounds, Fin.forall_fin_add, Fin.append_left,
          Fin.append_right, neg_apply, ContinuousLinearMap.proj_apply, neg_le_neg_iff]
        exact ⟨fun i => (ht.2 i).le, fun _ => hrough⟩
      simp only [primeIcoBoxGateForms, primeIcoBoxGateBounds, Fin.forall_fin_add,
        Fin.append_left, Fin.append_right, neg_apply,
        ContinuousLinearMap.proj_apply, neg_le_neg_iff]
      exact ⟨fun i => (mem_logPrimeBox.mp ht.1.1 i).1,
        fun i => (mem_logPrimeBox.mp ht.1.1 i).2.le, hactive⟩
  · simp only [if_neg hs, empty_inter, inter_empty, indicator_empty,
      actualPrimeBoxTestSum, Pi.zero_apply, mul_zero, Finset.sum_const_zero, integral_empty]
    exact tendsto_const_nhds

/-- Actual original source gates give strict legal PLUS residuals, without
any comparison between the initial and current third exponent. -/
theorem sourceBranch_plus_legal (e chi : ℝ) (m : ℕ) (omega : ℝ) (label : Label m)
    {t : Point} (ht : t ∈ sourceBranch e chi m omega label) :
    (∑ i, t i) + t (Fin.last 3) < branchSeed e chi m label := by
  have hg := (mem_gateRegion _ _ _).mp ht.2.1
  have h32 := hg.1 (by decide : (2 : Fin 4) < 3)
  have hsum : (∑ i, t i) = t 0 + t 1 + t 2 + t 3 := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [hsum]
  linarith [hg.2.2.2]

/-- Exact finite integral over the row-wall refinement of one full branch. -/
def refinedBranchIntegral (e chi : ℝ) (m : ℕ) (omega a : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (label : Label m) : ℝ :=
  ∑ s : Pattern rows, ∫ t in logPrimeBox (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)) ∩
      (sourceBranch e chi m omega label ∩ wallAtom rows s),
    fixedCellTest e rows (eligibleRows rows licensed s) (branchSeed e chi m label) t * ∏ i, 1 / t i

/-- Genuine prime-test mean for the full active source. Every row face is
refined before continuous test transport; no assumed htest supplier. -/
theorem tendsto_active_branch_test_refinedIntegral
    (e chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (j : FourthCell m) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
      ((sourceBranch e chi m omega (j, true)).indicator (fun t =>
        extendedProfile (branchSeed e chi m (j, true)) t -
          extendedProfile (producerProfile4 e rows licensed (branchSeed e chi m (j, true)) t) t))) atTop
      (𝓝 (refinedBranchIntegral e chi m omega a rows licensed (j, true))) := by
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Pattern rows)) (fun s _ =>
    tendsto_active_source_atom_test e chi m omega a ha haRho j rows s
      (fixedCellTest e rows (eligibleRows rows licensed s) (branchSeed e chi m (j, true)))
      (continuousOn_fixedCellTest e rows (eligibleRows rows licensed s)
        (branchSeed e chi m (j, true)) a (19 / 96) ha))
  apply hlim.congr'
  exact Eventually.of_forall (fun N => (original_variable_test_eq_sum_refined e
    (branchSeed e chi m (j, true)) rows licensed (sourceBranch e chi m omega (j, true))
      N a (19 / 96)).symm)

/-- Bounded PLUS arithmetic replacement on the full branch is independent
of its crossing-omega geometry and of all discontinuous row eligibility. -/
theorem tendsto_branchResidualSum_sub_actual_test
    (e chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (label : Label m) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => branchResidualSum e chi m omega a rows licensed N (cap N) label -
      actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
        ((sourceBranch e chi m omega label).indicator (fun t =>
          extendedProfile (branchSeed e chi m label) t -
            extendedProfile (producerProfile4 e rows licensed (branchSeed e chi m label) t) t)))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  let R := sourceBranch e chi m omega label
  let seed := branchSeed e chi m label
  let profile := producerProfile4 e rows licensed seed
  have hlegal : ∀ t ∈ R, (∑ i, t i) + t (Fin.last 3) ≤ seed :=
    fun t ht => (sourceBranch_plus_legal e chi m omega label ht).le
  have hold := tendsto_bounded_movingBoxResidualSum_error a (19 / 96) seed seed ha haRho R
    (fun _ => seed) (fun _ _ => ⟨le_rfl, le_rfl⟩) hlegal cap hcap
  have hnew := tendsto_bounded_movingBoxResidualSum_error a (19 / 96) seed
    (max seed (VariableEnvelope.cap - 2 * e)) ha haRho R profile
    (fun t _ => producerProfile_mem_interval e seed rows licensed t)
    (fun t ht => (hlegal t ht).trans (producerProfile4_seed_le e rows licensed seed t)) cap hcap
  have hlim := hold.sub hnew
  rw [sub_zero] at hlim
  apply hlim.congr'
  apply Eventually.of_forall
  intro N
  have hbranch : branchResidualSum e chi m omega a rows licensed N (cap N) label =
      movingBoxResidualSum N (cap N) a (19 / 96) R (fun _ => seed) -
        movingBoxResidualSum N (cap N) a (19 / 96) R profile := by
    unfold branchResidualSum movingBoxResidualSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hs : actualPrimeTupleLog N p ∈ R
    · simp only [R] at hs
      simp only [if_pos hs]
      ring
    · simp only [R] at hs
      simp only [if_neg hs, mul_zero, sub_self]
  have htest : actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
      ((sourceBranch e chi m omega label).indicator (fun t => extendedProfile seed t -
        extendedProfile (profile t) t)) =
      actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
        (R.indicator (extendedProfile seed)) -
      actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
        (R.indicator (fun t => extendedProfile (profile t) t)) := by
    unfold actualPrimeBoxTestSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hs : actualPrimeTupleLog N p ∈ R
    · simp only [R] at hs
      simp only [indicator_of_mem hs]
      ring
    · simp only [R] at hs
      simp only [indicator_of_not_mem hs, mul_zero, sub_self]
  rw [hbranch, htest]
  ring

/-- Actual full active branch discrete-to-integral mean, including original
firstStop and the pointwise rough gate on cells crossing omega. -/
theorem tendsto_active_branchResidualSum
    (e chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (j : FourthCell m) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => branchResidualSum e chi m omega a rows licensed N (cap N) (j, true))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (refinedBranchIntegral e chi m omega a rows licensed (j, true))) := by
  have herror := tendsto_branchResidualSum_sub_actual_test e chi m omega a ha haRho
    (j, true) rows licensed cap hcap
  have htest := (tendsto_active_branch_test_refinedIntegral e chi m omega a ha haRho j rows licensed).mono_left
    (show (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) ≤ atTop from inf_le_left)
  simpa only [sub_add_cancel, zero_add] using herror.add htest

/-- Finite full active source mean with all adopted THIRD ancestors,
without a whole-active fourth-cell selection premise. -/
theorem tendsto_all_activeAdopted_branchResidualSums
    (e chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => ∑ label ∈ activeAdoptedLabels e chi m,
      branchResidualSum e chi m omega a rows licensed N (cap N) label)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (∑ label ∈ activeAdoptedLabels e chi m,
        refinedBranchIntegral e chi m omega a rows licensed label)) := by
  apply tendsto_finsetSum (activeAdoptedLabels e chi m)
  intro label hl
  have hflag := ((mem_activeAdoptedLabels e chi m label).mp hl).1
  have heq : label = (label.1, true) := Prod.ext rfl hflag
  rw [heq]
  exact tendsto_active_branchResidualSum e chi m omega a ha haRho label.1 rows licensed cap hcap

/-- Actual complete positive-box source mean for the original rawQ3 to
variable-Q4 correction. Exact inactive/unselected cancellation and the full
admitted-source dictionary connect it to the active branch integral sum. -/
theorem tendsto_full_positive_original_correction
    (e chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if p ∈ firstExitAdmittedTuples 4 (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
            (roughPrimeUniverse N (cap N) 0 ((N : ℝ) ^ (19 / 96 : ℝ))) then
            P1OriginalCoarseFourthResidual.literalTupleResidualDifference
              (rawLevel e chi m omega (N : ℝ))
              (producerLevel4 e chi m omega (N : ℝ) rows licensed) N (cap N) p else 0))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (∑ label ∈ activeAdoptedLabels e chi m,
        refinedBranchIntegral e chi m omega a rows licensed label)) := by
  apply (tendsto_all_activeAdopted_branchResidualSums e chi m omega a ha haRho rows licensed cap hcap).congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hcap] with N hN hc
  exact (full_variable_correction_eq_activeAdopted e chi m omega a ha.le N (cap N) hN hc rows licensed).symm

end
end ImbalancedChen.P1OriginalVariableFourthFullActivePositiveLimit

