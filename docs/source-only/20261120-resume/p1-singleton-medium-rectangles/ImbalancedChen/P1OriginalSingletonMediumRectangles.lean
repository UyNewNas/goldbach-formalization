import ImbalancedChen.P1OriginalSingletonOneLongRectangle
import ImbalancedChen.P1OriginalSingletonMiddleTensor

/-!
SOURCE CANDIDATE / NOT COMPILED.

The actual final singleton medium branch is the finite sum of its original
ordered HB rectangles. Reuse the already proved arbitrary-K/Q/rho row
dictionary; no row dictionary, OneLong estimate or source61 scale window
is reproved. This identity does not supply signed M, whole-box licences,
role normalization, Fourier restoration or an asymptotic Atlas estimate.
-/
namespace ImbalancedChen.P1OriginalSingletonMediumRectangles
noncomputable section
open Classical
open scoped BigOperators
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (products free)
open P5Z.LiteralHeathBrownOccurrenceWords P5Z.ActualRoughHeathBrownWords
open P5Z.HBRightClosedDyadicRoles P5Z.ActualHBDyadicOccurrenceFamily
open P5Z.ActualHBDyadicProductWindow P5Z.ActualHBMediumBranchPartition
open P5Z.PerGroupIntegerHBAtlasPushforward P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.LicensedOriginalIntegerProfile P5Z.OriginalPrimeAtlasReserveBranches
open P5Z.OriginalPrimeAllGroupHBDiscrepancy
open P5Z.AllGroupHBLogNormalization P5Z.ExistingIndependentFamilyLogNormalization
open P5Z.ActualLowerNormalizedAtlasOccurrence (scalarProfile normalized_singleton_profile)
open P5ActualUpperPairHBLogTransport
open P5CanonicalTentNarrowSingletonTransfer (actualLicence)
open Part3.OriginalProperPowerActualChart
open P1OriginalSingletonOneLongRectangle (sourceTest occurrenceAtom actual_row_reindex)

def normalizedMediumAtlas (kap : ℝ) (B N K cap : ℕ) (kap0 lo hi : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) : ℂ :=
  ∑ ps ∈ integerWords cap 1,
    numeratorAtlas P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js ps
      (fun rows =>
        (listExtension (normalizedLicence (actualLicence kap B N)) (originalProducts rows) : ℂ) *
          mediumValue lo hi (fun rows =>
            (P5Z.ActualEtaPsiOccurrenceBudget.eta
              (((originalProducts rows).prod : ℝ) / (N : ℝ)^(1-kap0)) : ℂ) *
              P5Z.IndependentPrimeSourceWordDictionary.wordKernel Q rho N (originalProducts rows)) rows)

/-- Normalize the actual singleton logarithm without moving the original
first-medium selector through the count/mean kernel. -/
theorem actual_log_normalization (kap : ℝ) (B N K cap : ℕ) (kap0 lo hi : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) :
    mediumAtlas (actualLicence kap B N) K cap N kap0 lo hi Q rho js =
      normalizedMediumAtlas kap B N K cap kap0 lo hi Q rho js := by
  unfold mediumAtlas normalizedMediumAtlas
  apply Finset.sum_congr rfl
  intro ps hps
  change atlasEval _ _ js ps (mediumValue lo hi (sourceTest (actualLicence kap B N) N kap0 Q rho)) = _
  have move : mediumValue lo hi (sourceTest (actualLicence kap B N) N kap0 Q rho) =
      (fun rows => (listExtension (actualLicence kap B N) (originalProducts rows) : ℂ) *
        mediumValue lo hi (fun rows =>
          (P5Z.ActualEtaPsiOccurrenceBudget.eta
            (((originalProducts rows).prod : ℝ) / (N : ℝ)^(1-kap0)) : ℂ) *
            P5Z.IndependentPrimeSourceWordDictionary.wordKernel Q rho N (originalProducts rows)) rows) := by
    funext rows
    by_cases h : firstMedium lo hi (rows.flatMap Row.blocks) = none <;>
      simp [mediumValue, sourceTest, h, mul_assoc]
  rw [move]
  exact atlas_normalized_licence (actualLicence kap B N) _ _ js ps _

def occurrenceChart (kap : ℝ) (B N cj K : ℕ) (kap0 lo hi : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range 3, P5Z.SmoothChartHBDyadicPartition.scalar j *
    ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
      if firstMedium lo hi bs = none then 0
      else occurrenceAtom kap B N cj K kap0 j bs Q rho

/-- The original cap 2*N is removed only inside the reused actual row
dictionary, using the support of this very normalized singleton profile.
All positions, unit slots, HB scalars and complete products are retained. -/
theorem source_to_actual_rectangles (kap : ℝ) (hk : kap < 1)
    (B N cj K : ℕ) (kap0 lo hi : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    mediumAtlas (actualLicence kap B N) K (2*N) N kap0 lo hi Q rho [cj] =
      occurrenceChart kap B N cj K kap0 lo hi Q rho := by
  rw [actual_log_normalization]
  unfold normalizedMediumAtlas integerWords
  rw [words_sum_cons]
  simp only [words, Finset.sum_singleton]
  have hpwise (p : ℕ) :
      numeratorAtlas P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K [cj]) [cj] [p]
        (fun rows =>
          (listExtension (normalizedLicence (actualLicence kap B N)) (originalProducts rows) : ℂ) *
            mediumValue lo hi (fun rows =>
              (P5Z.ActualEtaPsiOccurrenceBudget.eta
                (((originalProducts rows).prod : ℝ) / (N : ℝ)^(1-kap0)) : ℂ) *
                P5Z.IndependentPrimeSourceWordDictionary.wordKernel Q rho N (originalProducts rows)) rows) =
        ∑ j ∈ Finset.range 3, P5Z.SmoothChartHBDyadicPartition.scalar j *
          ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
            if firstMedium lo hi bs = none then 0 else
              ∑ fs ∈ factorTuples (2*(j+1)) p,
                assignedWeight (beforeHBCutoff K [cj]) (hbCutoff cj) (roles j) bs fs *
                  ((scalarProfile kap B N cj kap0 fs.prod : ℂ) *
                    P5Z.IndependentPrimeSourceWordDictionary.wordKernel Q rho N [fs.prod]) := by
    simp only [numeratorAtlas, originalProducts, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, mediumValue,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro bs hbs
    by_cases hgate : firstMedium lo hi bs = none
    · simp [hgate]
    · simp only [if_neg hgate, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro fs hfs
      have hprod := (factorTuples_spec (2*(j+1)) p fs hfs).2.1
      rw [←hprod, ←normalized_singleton_profile kap B N cj kap0 fs.prod]
      ring
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
  by_cases hgate : firstMedium lo hi bs = none
  · simp [hgate]
  · simp only [if_neg hgate]
    exact actual_row_reindex kap hk B N cj K kap0 j bs hbs Q rho

/-- Sum over the actual singleton chart bank, with no replacement chart
or modulus family and no change of physical residue N. -/
theorem original_medium_to_actual_rectangles (kap : ℝ) (hk : kap < 1)
    (B N K : ℕ) (kap0 zeta : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    (∑ js ∈ chartBank (2*N) 1,
      mediumAtlas (actualLicence kap B N) K (2*N) N kap0
        (originalMediumLow zeta js) (originalMediumHigh zeta js) Q rho js) =
      ∑ js ∈ chartBank (2*N) 1,
        occurrenceChart kap B N (js.getD 0 0) K kap0
          (originalMediumLow zeta js) (originalMediumHigh zeta js) Q rho := by
  apply Finset.sum_congr rfl
  intro js hjs
  have hlen : js.length = 1 := (words_spec _ _ _ hjs).1
  have hs : js = [js.getD 0 0] := by
    cases js with
    | nil => simp at hlen
    | cons cj tail =>
      have ht : tail = [] := List.length_eq_zero.mp (by simpa using hlen)
      subst tail
      rfl
  rw [hs]
  exact source_to_actual_rectangles kap hk B N _ K kap0 _ _ Q rho

/-- Specialization to precisely the final compiler's free coefficient.
This is only the medium summand of singletonAtlas, with all other signed
reserves and the existing OneLong conclusions left in their own scope. -/
theorem final_free_medium_to_actual_rectangles (P : Params)
    (kap : ℝ) (hk : kap < 1) (K : ℕ) (kap0 zeta : ℝ) :
    (∑ js ∈ chartBank (2*P.N) 1,
      mediumAtlas (actualLicence kap 6 P.N) K (2*P.N) P.N kap0
        (originalMediumLow zeta js) (originalMediumHigh zeta js)
        (products P) (fun q => (free P q : ℂ)) js) =
      ∑ js ∈ chartBank (2*P.N) 1,
        occurrenceChart kap 6 P.N (js.getD 0 0) K kap0
          (originalMediumLow zeta js) (originalMediumHigh zeta js)
          (products P) (fun q => (free P q : ℂ)) :=
  original_medium_to_actual_rectangles kap hk 6 P.N K kap0 zeta
    (products P) (fun q => (free P q : ℂ))

/-- The existing complete Atlas handle retains the original signs of
trim, no-medium, proper-power and rough-prime reserves. Only its medium
summand is rewritten by the finite identity above; none is estimated. -/
theorem final_singletonAtlas_eq_occurrences (P : Params)
    (kap : ℝ) (hk : kap < 1) (K : ℕ) (kap0 zeta : ℝ) :
    P1OriginalSingletonMiddleTensor.singletonAtlas P kap K kap0 zeta =
      trimReserve (actualLicence kap 6 P.N) (2*P.N) P.N kap0
        (products P) (fun q => (free P q : ℂ)) +
      ∑ js ∈ chartBank (2*P.N) 1,
        (occurrenceChart kap 6 P.N (js.getD 0 0) K kap0
          (originalMediumLow zeta js) (originalMediumHigh zeta js)
          (products P) (fun q => (free P q : ℂ)) +
        noMediumAtlas (actualLicence kap 6 P.N) K (2*P.N) P.N kap0
          (originalMediumLow zeta js) (originalMediumHigh zeta js)
          (products P) (fun q => (free P q : ℂ)) js -
        properPowerReserve (actualLicence kap 6 P.N) K (2*P.N) P.N kap0
          (products P) (fun q => (free P q : ℂ)) js +
        roughPrimeReserve (actualLicence kap 6 P.N) K (2*P.N) P.N kap0
          (products P) (fun q => (free P q : ℂ)) js) := by
  unfold P1OriginalSingletonMiddleTensor.singletonAtlas
  congr 1
  apply Finset.sum_congr rfl
  intro js hjs
  have hlen : js.length = 1 := (words_spec _ _ _ hjs).1
  have hs : js = [js.getD 0 0] := by
    cases js with
    | nil => simp at hlen
    | cons cj tail =>
      have ht : tail = [] := List.length_eq_zero.mp (by simpa using hlen)
      subst tail
      rfl
  rw [hs, source_to_actual_rectangles kap hk]

end
end ImbalancedChen.P1OriginalSingletonMediumRectangles
