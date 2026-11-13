import ImbalancedChen.P1OriginalSingletonOneLongCoefficients
import ImbalancedChen.P5ActualLowerNormalizedAtlasOccurrence
import ImbalancedChen.P5ActualHBMediumRoleSupports

/-! The actual no-medium singleton sub-sum, with literal ordered HB rows.
The original cap is removed only by the existing actual profile support.
Neither a source equality nor a bounded smooth-profile class is an input. -/
namespace ImbalancedChen.P1OriginalSingletonOneLongRectangle
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
open P5Z.AllGroupHBLogNormalization P5Z.ExistingIndependentFamilyLogNormalization
open P5Z.ActualLowerNormalizedAtlasOccurrence P5Z.OrderedFactorTupleRectangleReindex
open P5Z.ActualHBPostModulusLogCutoff
open P5ActualUpperPairHBLogTransport
open P5CanonicalTentNarrowSingletonTransfer (actualLicence)
open Part3.OriginalProperPowerActualChart

def OneLong (lo hi : ℝ) (bs : List Block) : Prop :=
  firstMedium lo hi bs=none ∧ (longBlocks hi bs).length=1

def oneLongValue (lo hi : ℝ) (F : List Row→ℂ) (rows : List Row) : ℂ :=
  if OneLong lo hi (rows.flatMap Row.blocks) then F rows else 0

def remainingTypeIValue (lo hi : ℝ) (F : List Row→ℂ) (rows : List Row) : ℂ :=
  if (longBlocks hi (rows.flatMap Row.blocks)).length=1 then 0 else typeIValue lo hi F rows

theorem exact_typeI_partition (lo hi : ℝ) (F : List Row→ℂ) (rows : List Row) :
    typeIValue lo hi F rows=oneLongValue lo hi F rows+remainingTypeIValue lo hi F rows := by
  by_cases hn : firstMedium lo hi (rows.flatMap Row.blocks)=none <;>
    by_cases hl : (longBlocks hi (rows.flatMap Row.blocks)).length=1 <;>
    simp [typeIValue,oneLongValue,remainingTypeIValue,OneLong,hn,hl]

def sourceTest {k : ℕ} {W : (Fin k→ℕ)→ℝ} (L : Licence k W)
    (T : ℕ) (kap : ℝ) (Q : Finset ℕ) (rho : ℕ→ℂ) (rows : List Row) : ℂ :=
  (listExtension L (originalProducts rows) : ℂ)*
    (P5Z.ActualEtaPsiOccurrenceBudget.eta
      (((originalProducts rows).prod : ℝ)/(T : ℝ)^(1-kap)) : ℂ)*
    P5Z.IndependentPrimeSourceWordDictionary.wordKernel Q rho T (originalProducts rows)

def oneLongAtlas {k : ℕ} {W : (Fin k→ℕ)→ℝ} (L : Licence k W)
    (K cap T : ℕ) (kap lo hi : ℝ) (Q : Finset ℕ) (rho : ℕ→ℂ) (js : List ℕ) : ℂ :=
  ∑ ps∈integerWords cap k,
    atlasEval P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js ps
      (oneLongValue lo hi (sourceTest L T kap Q rho))

def remainingTypeIAtlas {k : ℕ} {W : (Fin k→ℕ)→ℝ} (L : Licence k W)
    (K cap T : ℕ) (kap lo hi : ℝ) (Q : Finset ℕ) (rho : ℕ→ℂ) (js : List ℕ) : ℂ :=
  ∑ ps∈integerWords cap k,
    atlasEval P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js ps
      (remainingTypeIValue lo hi (sourceTest L T kap Q rho))

theorem noMedium_exact_partition {k : ℕ} {W : (Fin k→ℕ)→ℝ} (L : Licence k W)
    (K cap T : ℕ) (kap lo hi : ℝ) (Q : Finset ℕ) (rho : ℕ→ℂ) (js : List ℕ) :
    noMediumAtlas L K cap T kap lo hi Q rho js=
      oneLongAtlas L K cap T kap lo hi Q rho js+
        remainingTypeIAtlas L K cap T kap lo hi Q rho js := by
  unfold noMediumAtlas oneLongAtlas remainingTypeIAtlas
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ps hps
  change atlasEval _ _ js ps (typeIValue lo hi (sourceTest L T kap Q rho))=_
  have eqF : typeIValue lo hi (sourceTest L T kap Q rho)=
      (fun rows=>oneLongValue lo hi (sourceTest L T kap Q rho) rows+
        remainingTypeIValue lo hi (sourceTest L T kap Q rho) rows) :=
    funext (exact_typeI_partition lo hi (sourceTest L T kap Q rho))
  rw [eqF]
  exact atlasEval_add _ _ js ps _ _

/-- Both channels use precisely the same original singleton test. Their
different genuine modulus coefficients stay in the same kernel position. -/
def physicalChannel (P : Params) (kap : ℝ) (K : ℕ) (zeta : ℝ) : ℂ :=
  ∑ js∈chartBank (2*P.N) 1,
    oneLongAtlas (actualLicence kap 6 P.N) K (2*P.N) P.N kap
      (originalMediumLow zeta js) (originalMediumHigh zeta js) P.S (fun q=>(P.rho q : ℂ)) js

def freeChannel (P : Params) (kap : ℝ) (K : ℕ) (zeta : ℝ) : ℂ :=
  ∑ js∈chartBank (2*P.N) 1,
    oneLongAtlas (actualLicence kap 6 P.N) K (2*P.N) P.N kap
      (originalMediumLow zeta js) (originalMediumHigh zeta js) (products P)
      (fun q=>(free P q : ℂ)) js

def normalizedOneLongAtlas (kap : ℝ) (B N K cap : ℕ) (kap0 lo hi : ℝ)
    (Q : Finset ℕ) (rho : ℕ→ℂ) (js : List ℕ) : ℂ :=
  ∑ ps∈integerWords cap 1,
    numeratorAtlas P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js ps
      (fun rows=>
        (listExtension (normalizedLicence (actualLicence kap B N)) (originalProducts rows) : ℂ)*
          oneLongValue lo hi (fun rows=>
            (P5Z.ActualEtaPsiOccurrenceBudget.eta
              (((originalProducts rows).prod : ℝ)/(N : ℝ)^(1-kap0)) : ℂ)*
              P5Z.IndependentPrimeSourceWordDictionary.wordKernel Q rho N (originalProducts rows)) rows)

theorem actual_log_normalization (kap : ℝ) (B N K cap : ℕ) (kap0 lo hi : ℝ)
    (Q : Finset ℕ) (rho : ℕ→ℂ) (js : List ℕ) :
    oneLongAtlas (actualLicence kap B N) K cap N kap0 lo hi Q rho js=
      normalizedOneLongAtlas kap B N K cap kap0 lo hi Q rho js := by
  unfold oneLongAtlas normalizedOneLongAtlas
  apply Finset.sum_congr rfl
  intro ps hps
  have move : oneLongValue lo hi (sourceTest (actualLicence kap B N) N kap0 Q rho)=
      (fun rows=> (listExtension (actualLicence kap B N) (originalProducts rows) : ℂ)*
        oneLongValue lo hi (fun rows=>
          (P5Z.ActualEtaPsiOccurrenceBudget.eta
            (((originalProducts rows).prod : ℝ)/(N : ℝ)^(1-kap0)) : ℂ)*
            P5Z.IndependentPrimeSourceWordDictionary.wordKernel Q rho N (originalProducts rows)) rows) := by
    funext rows
    by_cases h : OneLong lo hi (rows.flatMap Row.blocks) <;>
      simp [oneLongValue,sourceTest,h,mul_assoc]
  rw [move]
  exact atlas_normalized_licence (actualLicence kap B N) _ _ js ps _

def occurrenceAtom (kap : ℝ) (B N cj K : ℕ) (kap0 : ℝ) (j : ℕ)
    (bs : List Block) (Q : Finset ℕ) (rho : ℕ→ℂ) : ℂ :=
  PrimeProducts.MellinInsertion20261028.exactDiscrepancy
    (rectangle (blockVector (2*(j+1)) bs)) Q rho completeProduct N
    (fun n=>hbSlots (beforeHBCutoff K [cj]) (fun _=>hbCutoff cj) (rowRoles j) n*
      (integerProfile kap B N cj kap0 n : ℂ))

/-- Reuse the exact ordered rectangle theorem, generalizing only the
old lower caller's fixed K=1 and modulus coefficient interface. -/
theorem actual_row_reindex (kap : ℝ) (hk : kap<1) (B N cj K : ℕ)
    (kap0 : ℝ) (j : ℕ) (bs : List Block)
    (hbs : bs∈blockWords (hbCap cj) (2*(j+1))) (Q : Finset ℕ) (rho : ℕ→ℂ) :
    (∑ p∈Finset.Icc 1 (2*N),∑ fs∈factorTuples (2*(j+1)) p,
      assignedWeight (beforeHBCutoff K [cj]) (hbCutoff cj) (roles j) bs fs*
        ((scalarProfile kap B N cj kap0 fs.prod : ℂ)*
          P5Z.IndependentPrimeSourceWordDictionary.wordKernel Q rho N [fs.prod]))=
      occurrenceAtom kap B N cj K kap0 j bs Q rho := by
  rw [sum_factorTuples_rectangle (2*N) (beforeHBCutoff K [cj]) (hbCutoff cj)
    (roles j) bs (blockWords_spec _ _ _ hbs).1]
  · unfold occurrenceAtom PrimeProducts.MellinInsertion20261028.exactDiscrepancy
      PrimeProducts.MellinInsertion20261028.functional
    apply Finset.sum_congr rfl
    intro n hn
    rw [row_weight]
    simp only [List.prod_ofFn,integerProfile,completeProduct,
      P5Z.IndependentPrimeSourceWordDictionary.wordKernel,List.prod_cons,List.prod_nil,mul_one]
    ring
  · intro n hn hout
    have hz : scalarProfile kap B N cj kap0 (List.ofFn n).prod=0 := by
      by_contra hp
      have hc := scalarProfile_support kap hk B N cj kap0 hp
      exact (not_le_of_gt hout) (by simpa only [List.prod_ofFn,completeProduct] using hc)
    simp only [hz,Complex.ofReal_zero,zero_mul]

/-- This is the exact local long-role fact already proved for the
literal source. No arbitrary bounded long sequence enters either channel. -/
theorem actual_long_role (z y hi : ℝ) (hz : 0≤z) (hy : y≤hi)
    (j n : ℕ) (bs : List Block) (ha : blockCoefficient z y j n bs≠0)
    (rb : Role×Block) (hrb : rb∈(roles j).zip bs) (hl : hi<(lower rb.2 : ℝ)) :
    rb.1=.one ∨ rb.1=.logarithm :=
  P5Z.ActualHBMediumRoleSupports.actual_long_role_is_unweighted hz hy ha rb hrb hl

def occurrenceChart (kap : ℝ) (B N cj K : ℕ) (kap0 lo hi : ℝ)
    (Q : Finset ℕ) (rho : ℕ→ℂ) : ℂ :=
  ∑ j∈Finset.range 3,P5Z.SmoothChartHBDyadicPartition.scalar j*
    ∑ bs∈blockWords (hbCap cj) (2*(j+1)),
      if OneLong lo hi bs then occurrenceAtom kap B N cj K kap0 j bs Q rho else 0

/-- This finite terminal is the actual selected branch of the original
singleton atlas. All original HB restoring scalars, complete-product
geometry, group log, ordered positions and the same count/mean kernel
are preserved. It asserts an identity, not the unpaid asymptotic estimate. -/
theorem source_to_actual_rectangles (kap : ℝ) (hk : kap<1)
    (B N cj K : ℕ) (kap0 lo hi : ℝ) (Q : Finset ℕ) (rho : ℕ→ℂ) :
    oneLongAtlas (actualLicence kap B N) K (2*N) N kap0 lo hi Q rho [cj]=
      occurrenceChart kap B N cj K kap0 lo hi Q rho := by
  rw [actual_log_normalization]
  unfold normalizedOneLongAtlas integerWords
  rw [words_sum_cons]
  simp only [words,Finset.sum_singleton]
  have hpwise (p : ℕ) :
      numeratorAtlas P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K [cj]) [cj] [p]
        (fun rows=>
          (listExtension (normalizedLicence (actualLicence kap B N)) (originalProducts rows) : ℂ)*
            oneLongValue lo hi (fun rows=>
              (P5Z.ActualEtaPsiOccurrenceBudget.eta
                (((originalProducts rows).prod : ℝ)/(N : ℝ)^(1-kap0)) : ℂ)*
                P5Z.IndependentPrimeSourceWordDictionary.wordKernel Q rho N (originalProducts rows)) rows)=
        ∑ j∈Finset.range 3,P5Z.SmoothChartHBDyadicPartition.scalar j*
          ∑ bs∈blockWords (hbCap cj) (2*(j+1)),
            if OneLong lo hi bs then
              ∑ fs∈factorTuples (2*(j+1)) p,
                assignedWeight (beforeHBCutoff K [cj]) (hbCutoff cj) (roles j) bs fs*
                  ((scalarProfile kap B N cj kap0 fs.prod : ℂ)*
                    P5Z.IndependentPrimeSourceWordDictionary.wordKernel Q rho N [fs.prod])
            else 0 := by
    simp only [numeratorAtlas,originalProducts,List.map_cons,List.map_nil,List.prod_cons,
      List.prod_nil,mul_one,oneLongValue,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro bs hbs
    by_cases hgate : OneLong lo hi bs
    · simp only [if_pos hgate,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro fs hfs
      have hprod := (factorTuples_spec (2*(j+1)) p fs hfs).2.1
      rw [←hprod,←normalized_singleton_profile kap B N cj kap0 fs.prod]
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
  by_cases hgate : OneLong lo hi bs
  · simp only [if_pos hgate]
    exact actual_row_reindex kap hk B N cj K kap0 j bs hbs Q rho
  · simp [hgate]

end
end ImbalancedChen.P1OriginalSingletonOneLongRectangle
