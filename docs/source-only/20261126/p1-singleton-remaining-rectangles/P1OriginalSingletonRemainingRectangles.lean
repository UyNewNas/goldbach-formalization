import ImbalancedChen.P1OriginalSingletonOneLongRectangle
import ImbalancedChen.P1OriginalSingletonLogNormalization

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The original remaining-Type-I selector is expanded into its original
singleton HB rectangles. This keeps firstMedium = none, excludes exactly
one long block, and retains every original signed +3,-3,+1 HB scalar.
The arbitrary K, physical N, Q/rho and complete product are unchanged.
The existing actual_row_reindex owns the full right-closed rectangle and
the removal of the integer cap 2*N; neither is proved again here.

A nonzero selected occurrence atom then supplies a genuine original
factor tuple. Its nonzero assigned weight, original chart and literal
remaining source test are conclusions of the finite dictionary. A dead
selected atom is separated before any Fourier insertion. No statement
about its Fourier amplitude vanishing is used or asserted.

There is no analytic estimate, mass premise, Fourier payment, scale
absorption or final remainingTypeIAtlas norm bound in this module.
-/

namespace ImbalancedChen.P1OriginalSingletonRemainingRectangles
noncomputable section
open Classical
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.LiteralHeathBrownOccurrenceWords (factorTuples factorTuples_spec)
open P5Z.ActualRoughHeathBrownWords (roles)
open P5Z.ActualHBDyadicOccurrenceFamily (blockWords assignedWeight)
open P5Z.ActualHBMediumBranchPartition (firstMedium longBlocks)
open P5Z.PerGroupIntegerHBAtlasPushforward
  (Row hbCutoff hbCap originalProducts typeIValue atlasEval)
open P5Z.ExactOriginalSmoothDyadicPartition
  (beforeHBCutoff words words_sum_cons chartBank cutoffIndex)
open P5Z.LicensedOriginalIntegerProfile (listExtension)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (originalChart)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5Z.AllGroupHBLogNormalization (atlas_normalized_licence)
open P5Z.ExistingIndependentFamilyLogNormalization (normalizedLicence)
open P5Z.ActualLowerNormalizedAtlasOccurrence
  (scalarProfile normalized_singleton_profile)
open P5Z.ActualLabelledPrimeSmoothCharts (chartTerm trimmedWeight)
open P5Z.IndependentPrimeSourceWordDictionary (wordKernel)
open P5Z.ActualEtaPsiOccurrenceBudget (eta)
open P5ActualUpperPairHBLogTransport (numeratorAtlas)
open P5CanonicalTentNarrowSingletonTransfer (actualLicence)
open Part3.OriginalProperPowerActualChart
open P1OriginalSingletonOneLongRectangle
  (sourceTest remainingTypeIValue remainingTypeIAtlas occurrenceAtom actual_row_reindex)
open P1OriginalSingletonLogNormalization (scalarProfile_eq_originalChart_div_log)
open P1OriginalSingletonRemainingTypeIGeometry (singleton_remaining_predicate_iff)

/-- Exactly the two tests in the original remaining selector. -/
def Remaining (lo hi : ℝ) (bs : List Block) : Prop :=
  firstMedium lo hi bs = none ∧ (longBlocks hi bs).length ≠ 1

theorem remainingTypeIValue_eq_ite (lo hi : ℝ) (F : List Row → ℂ)
    (rows : List Row) :
    remainingTypeIValue lo hi F rows =
      if Remaining lo hi (rows.flatMap Row.blocks) then F rows else 0 := by
  by_cases hm : firstMedium lo hi (rows.flatMap Row.blocks) = none <;>
    by_cases hl : (longBlocks hi (rows.flatMap Row.blocks)).length = 1 <;>
    simp [remainingTypeIValue, typeIValue, Remaining, hm, hl]

def normalizedRemainingAtlas (kap : ℝ) (B N K cap : ℕ) (kap0 lo hi : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) : ℂ :=
  ∑ ps ∈ integerWords cap 1,
    numeratorAtlas P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js ps
      (fun rows =>
        (listExtension (normalizedLicence (actualLicence kap B N)) (originalProducts rows) : ℂ) *
          remainingTypeIValue lo hi (fun rows =>
            (eta (((originalProducts rows).prod : ℝ)/(N : ℝ)^(1-kap0)) : ℂ) *
              wordKernel Q rho N (originalProducts rows)) rows)

/-- The existing all-integer log normalizer accepts this literal
row-dependent selector, without any new nonzero or positivity premise. -/
theorem actual_log_normalization (kap : ℝ) (B N K cap : ℕ) (kap0 lo hi : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) :
    remainingTypeIAtlas (actualLicence kap B N) K cap N kap0 lo hi Q rho js =
      normalizedRemainingAtlas kap B N K cap kap0 lo hi Q rho js := by
  unfold remainingTypeIAtlas normalizedRemainingAtlas
  apply Finset.sum_congr rfl
  intro ps hps
  have move : remainingTypeIValue lo hi (sourceTest (actualLicence kap B N) N kap0 Q rho) =
      (fun rows => (listExtension (actualLicence kap B N) (originalProducts rows) : ℂ) *
        remainingTypeIValue lo hi (fun rows =>
          (eta (((originalProducts rows).prod : ℝ)/(N : ℝ)^(1-kap0)) : ℂ) *
            wordKernel Q rho N (originalProducts rows)) rows) := by
    funext rows
    by_cases h : Remaining lo hi (rows.flatMap Row.blocks) <;>
      simp [remainingTypeIValue_eq_ite, sourceTest, h, mul_assoc]
  rw [move]
  exact atlas_normalized_licence (actualLicence kap B N) _ _ js ps _

def occurrenceChart (kap : ℝ) (B N cj K : ℕ) (kap0 lo hi : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range 3, P5Z.SmoothChartHBDyadicPartition.scalar j *
    ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
      if Remaining lo hi bs then occurrenceAtom kap B N cj K kap0 j bs Q rho else 0

/-- Exact finite source identity. The original signed HB scalars stay
outside their own complete rectangles, with the same physical N/Q/rho. -/
theorem source_to_actual_rectangles (kap : ℝ) (hkap : kap < 1)
    (B N cj K : ℕ) (kap0 lo hi : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    remainingTypeIAtlas (actualLicence kap B N) K (2*N) N kap0 lo hi Q rho [cj] =
      occurrenceChart kap B N cj K kap0 lo hi Q rho := by
  rw [actual_log_normalization]
  unfold normalizedRemainingAtlas integerWords
  rw [words_sum_cons]
  simp only [words, Finset.sum_singleton]
  have hpwise (p : ℕ) :
      numeratorAtlas P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K [cj]) [cj] [p]
        (fun rows =>
          (listExtension (normalizedLicence (actualLicence kap B N)) (originalProducts rows) : ℂ) *
            remainingTypeIValue lo hi (fun rows =>
              (eta (((originalProducts rows).prod : ℝ)/(N : ℝ)^(1-kap0)) : ℂ) *
                wordKernel Q rho N (originalProducts rows)) rows) =
        ∑ j ∈ Finset.range 3, P5Z.SmoothChartHBDyadicPartition.scalar j *
          ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
            if Remaining lo hi bs then
              ∑ fs ∈ factorTuples (2*(j+1)) p,
                assignedWeight (beforeHBCutoff K [cj]) (hbCutoff cj) (roles j) bs fs *
                  ((scalarProfile kap B N cj kap0 fs.prod : ℂ) * wordKernel Q rho N [fs.prod])
            else 0 := by
    simp only [numeratorAtlas, originalProducts, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, remainingTypeIValue_eq_ite,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro bs hbs
    by_cases hgate : Remaining lo hi bs
    · simp only [if_pos hgate, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro fs hfs
      have hprod := (factorTuples_spec (2*(j+1)) p fs hfs).2.1
      rw [←hprod, ←normalized_singleton_profile kap B N cj kap0 fs.prod]
      ring
    · simp [hgate]
  simp_rw [hpwise]
  unfold occurrenceChart
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [←Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro bs hbs
  by_cases hgate : Remaining lo hi bs
  · simp only [if_pos hgate]
    exact actual_row_reindex kap hkap B N cj K kap0 j bs hbs Q rho
  · simp [hgate]

/-- The original chart bank is rewritten by its existing singleton-word
recursion. No new atlas, chart carrier or coefficient family is introduced. -/
theorem original_remaining_to_actual_rectangles (kap : ℝ) (hkap : kap < 1)
    (B N K : ℕ) (kap0 zeta : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    (∑ js ∈ chartBank (2*N) 1,
      remainingTypeIAtlas (actualLicence kap B N) K (2*N) N kap0
        (originalMediumLow zeta js) (originalMediumHigh zeta js) Q rho js) =
      ∑ cj ∈ Finset.range (cutoffIndex (2*N)+1),
        occurrenceChart kap B N cj K kap0
          (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj]) Q rho := by
  unfold chartBank
  rw [words_sum_cons]
  simp only [words, Finset.sum_singleton]
  apply Finset.sum_congr rfl
  intro cj hcj
  exact source_to_actual_rectangles kap hkap B N cj K kap0 _ _ Q rho

/-- A real source tuple, including its original complete integer cap.
These are conclusions extracted below, not extra inputs to a payment. -/
def ActualSourceTuple (kap : ℝ) (B N cj K : ℕ) (kap0 lo hi : ℝ)
    (j : ℕ) (bs : List Block) (Q : Finset ℕ) (rho : ℕ → ℂ)
    (fs : List ℕ) : Prop :=
  fs.prod ∈ Finset.Icc 1 (2*N) ∧
    fs ∈ factorTuples (2*(j+1)) fs.prod ∧
    originalChart (actualLicence kap B N) N kap0 [cj] [fs.prod] ≠ 0 ∧
    assignedWeight (beforeHBCutoff K [cj]) (hbCutoff cj) (roles j) bs fs ≠ 0 ∧
    remainingTypeIValue lo hi (sourceTest (actualLicence kap B N) N kap0 Q rho)
      [{order := j, blocks := bs, factors := fs}] ≠ 0

/-- Nonzero finite atom -> one nonzero original ordered source tuple.
The same signed kernel is retained; no aggregate blockCoefficient is
inferred nonzero. The reused log identity is valid even at totalized logs. -/
theorem nonzero_selected_occurrence_has_source_tuple (kap : ℝ) (hkap : kap < 1)
    (B N cj K : ℕ) (kap0 lo hi : ℝ) (j : ℕ) (bs : List Block)
    (hbs : bs ∈ blockWords (hbCap cj) (2*(j+1)))
    (Q : Finset ℕ) (rho : ℕ → ℂ) (hgate : Remaining lo hi bs)
    (hne : occurrenceAtom kap B N cj K kap0 j bs Q rho ≠ 0) :
    ∃ fs, ActualSourceTuple kap B N cj K kap0 lo hi j bs Q rho fs := by
  have hex : ∃ p ∈ Finset.Icc 1 (2*N), ∃ fs ∈ factorTuples (2*(j+1)) p,
      assignedWeight (beforeHBCutoff K [cj]) (hbCutoff cj) (roles j) bs fs *
        ((scalarProfile kap B N cj kap0 fs.prod : ℂ) * wordKernel Q rho N [fs.prod]) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    rw [←actual_row_reindex kap hkap B N cj K kap0 j bs hbs Q rho]
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro fs hfs
    exact h p hp fs hfs
  obtain ⟨p, hp, fs, hfs, hterm⟩ := hex
  have hprod := (factorTuples_spec (2*(j+1)) p fs hfs).2.1
  have hassigned := (mul_ne_zero_iff.mp hterm).1
  have hscalar := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hterm).2).1
  have hkernel := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hterm).2).2
  have hchart : originalChart (actualLicence kap B N) N kap0 [cj] [fs.prod] ≠ 0 := by
    intro hz
    apply hscalar
    rw [scalarProfile_eq_originalChart_div_log, hz, zero_div]
  have htrimmed :
      trimmedWeight eta (fun ns => (listExtension (actualLicence kap B N) ns : ℂ))
        (N : ℝ) kap0 [fs.prod] ≠ 0 :=
    (mul_ne_zero_iff.mp hchart).2
  have hbase :
      (listExtension (actualLicence kap B N) [fs.prod] : ℂ) *
        (eta ((fs.prod : ℝ)/(N : ℝ)^(1-kap0)) : ℂ) ≠ 0 := by
    simpa only [trimmedWeight, List.prod_cons, List.prod_nil, mul_one, mul_comm] using htrimmed
  have htest : sourceTest (actualLicence kap B N) N kap0 Q rho
      [{order := j, blocks := bs, factors := fs}] ≠ 0 := by
    simpa only [sourceTest, originalProducts, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one] using mul_ne_zero hbase hkernel
  have hremaining : remainingTypeIValue lo hi
      (sourceTest (actualLicence kap B N) N kap0 Q rho)
      [{order := j, blocks := bs, factors := fs}] ≠ 0 :=
    (singleton_remaining_predicate_iff lo hi
      (sourceTest (actualLicence kap B N) N kap0 Q rho)
      {order := j, blocks := bs, factors := fs}).mpr ⟨hgate.2, hgate.1, htest⟩
  refine ⟨fs, ?_, ?_, hchart, hassigned, hremaining⟩
  · simpa only [hprod] using hp
  · simpa only [hprod] using hfs

/-- This form supplies the invoice's literal Row premises. Its order and
block list are the original outer indices, not a newly selected chart. -/
theorem nonzero_selected_occurrence_has_source_row (kap : ℝ) (hkap : kap < 1)
    (B N cj K : ℕ) (kap0 lo hi : ℝ) (j : ℕ) (hj : j ∈ Finset.range 3)
    (bs : List Block) (hbs : bs ∈ blockWords (hbCap cj) (2*(j+1)))
    (Q : Finset ℕ) (rho : ℕ → ℂ) (hgate : Remaining lo hi bs)
    (hne : occurrenceAtom kap B N cj K kap0 j bs Q rho ≠ 0) :
    ∃ row : Row, row.order = j ∧ row.blocks = bs ∧
      originalChart (actualLicence kap B N) N kap0 [cj] [row.factors.prod] ≠ 0 ∧
      row.order ∈ Finset.range 3 ∧
      row.factors ∈ factorTuples (2*(row.order+1)) row.factors.prod ∧
      assignedWeight (beforeHBCutoff K [cj]) (hbCutoff cj)
        (roles row.order) row.blocks row.factors ≠ 0 ∧
      remainingTypeIValue lo hi (sourceTest (actualLicence kap B N) N kap0 Q rho) [row] ≠ 0 := by
  obtain ⟨fs, _, hfs, hchart, hassigned, hremaining⟩ :=
    nonzero_selected_occurrence_has_source_tuple kap hkap B N cj K kap0 lo hi j bs
      hbs Q rho hgate hne
  exact ⟨{order := j, blocks := bs, factors := fs}, rfl, rfl,
    hchart, hj, hfs, hassigned, hremaining⟩

/-- Split dead selected atoms before any Fourier insertion. The live
branch supplies the real tuple; no amplitude-zero statement occurs. -/
theorem selected_occurrence_eq_zero_or_has_source_tuple (kap : ℝ) (hkap : kap < 1)
    (B N cj K : ℕ) (kap0 lo hi : ℝ) (j : ℕ) (bs : List Block)
    (hbs : bs ∈ blockWords (hbCap cj) (2*(j+1))) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    (if Remaining lo hi bs then occurrenceAtom kap B N cj K kap0 j bs Q rho else 0) = 0 ∨
      (Remaining lo hi bs ∧
        ∃ fs, ActualSourceTuple kap B N cj K kap0 lo hi j bs Q rho fs) := by
  by_cases hgate : Remaining lo hi bs
  · by_cases hz : occurrenceAtom kap B N cj K kap0 j bs Q rho = 0
    · exact Or.inl (by simp only [if_pos hgate, hz])
    · exact Or.inr ⟨hgate,
        nonzero_selected_occurrence_has_source_tuple kap hkap B N cj K kap0 lo hi j bs
          hbs Q rho hgate hz⟩
  · exact Or.inl (by simp only [if_neg hgate])

end
end ImbalancedChen.P1OriginalSingletonRemainingRectangles
