import ImbalancedChen.Part5OriginalH430BuchstabDefectIntegralBridge
import ImbalancedChen.Part5OriginalH430OwnedBuchstabLower

/-!
P5.6/h34: the REAL resolved Buchstab request's rounded suffix is below
the original untruncated profile. The remaining deficit is the genuine
physical-ceiling integral trim, NOT zero. Keeps real read mode, same Q,
parent Theta, positive path marks, polarities and occurrence positions.
SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430SelectedBuchstabPhysicalTrim
noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2Selected430CausalOccurrenceExporter P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430PhysicalRoots Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ImmutableBankProfiles
open Part5OriginalBuchstabImmutable430Budget
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedMember Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430RequestedNonbankSupply
open Part5OriginalH430RequestedNonbankLevel
open Part5OriginalH430AllActionOccurrenceSource
open Part5OriginalH430ActualReadEdgeDefect
open Part5OriginalH430BuchstabDefectIntegralBridge
open Part5OriginalH430OwnedBuchstabLower

/-- Real chosen cell, even for a specified-cell request. No replacement
by the scalar closed-min winner or by the new generation's old array. -/
theorem actual_buchstab_request_le_untrimmed {N : ℕ} {Q : ℝ}
    {r : Request} {g : Fin 430} {i : Fin 200}
    (hc : Coherent N Q r) (hs : Selected g.val r i .buchstab) :
    requestValue (iterate (g.val+1)) r ≤
      originalProfile r.node.upper r.node.physical.argument
        (precedingH g) (precedingh g) := by
  rw [requested_buchstab_value hs]
  have ha : 50 ≤ i.val :=
    Part5OriginalH430RequestedReads.selected_allowed hs
  have hcell : r.node.physical.argument ∈ queryCell i :=
    resolve_contains hc.read_valid hs.1
  exact buchstabValue_le_cell_profile (iterate g.val)
    (iterate_nonneg g.val) r.node.upper i ha hcell

/-- The original full Buchstab table integral starts at baseStart.
The actual strictly ceiling-filtered ideal starts at physicalStart =
max(baseStart, residual/ceiling-1). This exact difference is unpaid. -/
def buchstabPhysicalTrim (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g,
    levelMark l *
      (thetaAtom N (rootQ N n root tau p)
        (parentProduct (levelOccurrence l).current.old) *
        (originalProfile (levelOccurrence l).current.node.upper
           (levelOccurrence l).current.node.physical.argument
           (precedingH g) (precedingh g) -
         idealProfile (levelOccurrence l).current.node.upper
           (levelOccurrence l).current.node.physical
           (precedingH g) (precedingh g)))

/-- The previously unpaid signed integer suffix residual is bounded
above by the physical moving-ceiling integral difference. -/
theorem buchstab_read_residual_le_physical_trim (N n : ℕ)
    (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    buchstabReadIntegralResidual N n root tau p g ≤
      buchstabPhysicalTrim N n root tau p g := by
  unfold buchstabReadIntegralResidual buchstabPhysicalTrim
  apply Finset.sum_le_sum
  intro l hl
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hl).2
  have hc := rootHistory_coherent (by omega : 1 < N)
    ht ht' hn hp hband (levelOccurrence_source l).1
  have hw := (rootHistory_support (by omega : 1 < N)
    ht ht' hn hp hband (levelOccurrence_source l).1).1
  have htheta : 0 ≤ thetaAtom N (rootQ N n root tau p)
      (parentProduct (levelOccurrence l).current.old) :=
    thetaAtom_nonneg hN hw.2.1 (parentWindow_logs hw).2.1
  have hread := actual_buchstab_request_le_untrimmed hc hi
  have hscaled := mul_le_mul_of_nonneg_left hread htheta
  have hshift := sub_le_sub_right hscaled
    (thetaAtom N (rootQ N n root tau p)
      (parentProduct (levelOccurrence l).current.old) *
      idealProfile (levelOccurrence l).current.node.upper
        (levelOccurrence l).current.node.physical
        (precedingH g) (precedingh g))
  have hweighted := mul_le_mul_of_nonneg_left hshift (mark_pos _).le
  unfold readTerm
  convert hweighted using 1 <;> ring

/-- Retention cancels. Strict-prime/integral error is charged once,
and original 106-bank candidates remain literal, not already paid. -/
theorem actual_one_generation_physical_trim_upper (N n : ℕ)
    (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    levelReadMass N n root tau p g - levelChildMass N n root tau p g ≤
      (buchstabPhysicalTrim N n root tau p g +
        buchstabLevelError N n root tau p g) +
      (∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a,
          bankCandidateGap N n root tau p g a l) := by
  have hstep := actual_one_generation_integral_residual_upper
    N n root tau p g hN ht ht' hn hp hband
  have htrim := buchstab_read_residual_le_physical_trim
    N n root tau p g hN ht ht' hn hp hband
  linarith only [hstep,htrim]

/-- Same pre-N threshold as prior strict-prime row supplier. Neither
the physical trim nor the original bank gap is estimated here. -/
theorem uniform_actual_one_generation_physical_trim_upper
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
          (buchstabPhysicalTrim N n root tau p g +
            epsilon * buchstabLevelTheta N n root tau p g) +
          (∑ a : Original106Action,
            ∑ l ∈ selectedLevel N n root tau p g a,
              bankCandidateGap N n root tau p g a l) := by
  obtain ⟨T,hT,hstep⟩ :=
    uniform_actual_one_generation_integral_residual_upper he
  refine ⟨T,hT,?_⟩
  intro N hN n root tau ht ht' hn p hp hband g
  have hu := hstep N hN n root tau ht ht' hn p hp hband g
  have htrim := buchstab_read_residual_le_physical_trim N n
    root tau p g (hT.trans hN) ht ht' hn hp hband
  linarith only [hu,htrim]

end
end ImbalancedChen.Part5OriginalH430SelectedBuchstabPhysicalTrim
