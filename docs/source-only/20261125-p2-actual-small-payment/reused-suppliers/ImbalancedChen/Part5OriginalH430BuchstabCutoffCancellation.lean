import ImbalancedChen.Part5OriginalH430SelectedBuchstabPhysicalTrim
import ImbalancedChen.Part5OriginalH430CutoffCoherence

/-!
P5.6/h34: the generated request histories ALREADY preserve CutoffFits.
Consequently the physical ceiling does not move the Buchstab integration
start on any actual selected occurrence. This is NOT a general statement
about arbitrary PhysicalNode values, and it is not an original U3/U4
selected-count identity. No prior 106-bank gap or base/seed obligation is
discarded. SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430BuchstabCutoffCancellation
noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2Selected430CausalOccurrenceExporter P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430CutoffCoherence Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430PhysicalRoots Part5OriginalH430ImmutableBankProfiles
open Part5OriginalBuchstabImmutable430Budget
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedMember Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430RequestedNonbankSupply
open Part5OriginalH430RequestedNonbankLevel
open Part5OriginalH430AllActionOccurrenceSource
open Part5OriginalH430ActualReadEdgeDefect
open Part5OriginalH430BuchstabDefectIntegralBridge
open Part5OriginalH430SelectedBuchstabPhysicalTrim

/-- No new physical-ceiling assumption: Coherent was proved from the
frozen root and preserved through every actually chosen LocalDomain. -/
theorem coherent_start_eq_base {N : ℕ} {Q : ℝ} {r : Request}
    (hc : Coherent N Q r) :
    physicalStart r.node.upper r.node.physical =
      baseStart r.node.upper r.node.physical :=
  physicalStart_eq_baseStart hc.ceiling_pos hc.cutoff_fits

/-- The two integrals agree for a genuinely resolved Buchstab request,
including a specified-cell winner and the lower-direction guard at 2. -/
theorem selected_integrals_eq {N : ℕ} {Q : ℝ}
    {r : Request} {g : Fin 430} {i : Fin 200}
    (hc : Coherent N Q r) (hs : Selected g.val r i .buchstab) :
    originalProfile r.node.upper r.node.physical.argument
        (precedingH g) (precedingh g) =
      idealProfile r.node.upper r.node.physical
        (precedingH g) (precedingh g) := by
  exact (idealProfile_eq_original hc.ceiling_pos hc.cutoff_fits
    (requested_buchstab_guard hc hs) (precedingH g) (precedingh g)).symm

/-- Literal integer suffix uses the actual g+1 resolver and g predecessor.
Under the proved cutoff invariant, no extra integral-start loss remains. -/
theorem selected_buchstab_read_le_ideal {N : ℕ} {Q : ℝ}
    {r : Request} {g : Fin 430} {i : Fin 200}
    (hc : Coherent N Q r) (hs : Selected g.val r i .buchstab) :
    requestValue (iterate (g.val+1)) r ≤
      idealProfile r.node.upper r.node.physical
        (precedingH g) (precedingh g) := by
  have hr := actual_buchstab_request_le_untrimmed hc hs
  rwa [selected_integrals_eq hc hs] at hr

/-- Every summand is zero at its OWN chosen occurrence. No quotient by
catalog labels, no replacement of specified-cell by scalar selection,
and no nonzero-Theta or normalized mark assumption. -/
theorem actual_buchstab_physical_trim_eq_zero (N n : ℕ)
    (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    buchstabPhysicalTrim N n root tau p g = 0 := by
  unfold buchstabPhysicalTrim
  apply Finset.sum_eq_zero
  intro l hl
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hl).2
  have hc := rootHistory_coherent (by omega : 1 < N)
    ht ht' hn hp hband (levelOccurrence_source l).1
  have heq := selected_integrals_eq (g := g) hc hi
  simp only [heq, sub_self, mul_zero]

/-- The previously unpaid signed integer suffix residual is nonpositive:
the genuine physical trim vanishes on coherent generated histories. -/
theorem actual_buchstab_residual_nonpos (N n : ℕ)
    (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    buchstabReadIntegralResidual N n root tau p g ≤ 0 := by
  have hb := buchstab_read_residual_le_physical_trim
    N n root tau p g hN ht ht' hn hp hband
  have hz := actual_buchstab_physical_trim_eq_zero
    N n root tau p g hN ht ht' hn hp hband
  simpa only [hz] using hb

/-- Only the Buchstab trim is eliminated. The absolute strict-prime
row error and all 106 genuine bank candidate gaps are still on the RHS. -/
theorem actual_one_generation_without_trim (N n : ℕ)
    (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    levelReadMass N n root tau p g - levelChildMass N n root tau p g ≤
      buchstabLevelError N n root tau p g +
        (∑ a : Original106Action,
          ∑ l ∈ selectedLevel N n root tau p g a,
            bankCandidateGap N n root tau p g a l) := by
  have hstep := actual_one_generation_physical_trim_upper
    N n root tau p g hN ht ht' hn hp hband
  have hz := actual_buchstab_physical_trim_eq_zero
    N n root tau p g hN ht ht' hn hp hband
  simpa only [hz, zero_add] using hstep

/-- The original single pre-N threshold remains uniform over real roots,
all generations and both read modes. No extra loss, no altered coefficient. -/
theorem uniform_actual_one_generation_without_trim
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N → ∀ n : ℕ, ∀ root : Root,
      ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 →
        1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
        physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430,
        levelReadMass N n root tau p g -
            levelChildMass N n root tau p g ≤
          epsilon * buchstabLevelTheta N n root tau p g +
            (∑ a : Original106Action,
              ∑ l ∈ selectedLevel N n root tau p g a,
                bankCandidateGap N n root tau p g a l) := by
  obtain ⟨T,hT,hstep⟩ :=
    uniform_actual_one_generation_physical_trim_upper he
  refine ⟨T,hT,?_⟩
  intro N hN n root tau ht ht' hn p hp hband g
  have h := hstep N hN n root tau ht ht' hn p hp hband g
  have hz := actual_buchstab_physical_trim_eq_zero
    N n root tau p g (hT.trans hN) ht ht' hn hp hband
  simpa only [hz, zero_add] using h

end
end ImbalancedChen.Part5OriginalH430BuchstabCutoffCancellation
