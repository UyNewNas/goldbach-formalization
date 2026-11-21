import ImbalancedChen.P4BOriginalTwoLongSourceRow
import ImbalancedChen.P5AllGroupOrderedRectangleReindex

/-! SOURCE ONLY / UNCOMPILED. Normalize the ORIGINAL noMediumAtlas
itself. The block-only typeI selector commutes with multiplication by
the raw group weight, so the proved arbitrary-Row normalization applies
before source reindexing. Zero/unit group logarithms keep totalized division. -/
namespace ImbalancedChen.P4BOriginalNoMediumAtlasNormalization
noncomputable section
open Classical
open scoped BigOperators
open P5Z.PerGroupIntegerHBAtlasPushforward (Row typeIValue atlasEval originalProducts)
open P5Z.AllGroupOrderedRectangleReindex (CapSupported fullEval numerator_source_eq_full_rectangles)
open P5ActualUpperPairHBLogTransport (numeratorAtlas)
open P5Z.LicensedOriginalIntegerProfile (listExtension)
open P5Z.OriginalPrimeAtlasReserveBranches (noMediumAtlas)
open P5Z.IndependentPrimeSourceWordDictionary (wordKernel)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P4BArbitraryWidthUpperPairHBNormalization (normalizedLicence all_group_normalization)
open P4BUpperPairOrderedRowModes (upperTest upperTest_capSupported)
open P4BOriginalFiniteSignedTrim (pairLicence)
open P4BArbitraryWidthUpperPairProfile (profile)
open Part3.OriginalProperPowerActualChart (integerWords)
open P4BOuterRampRoughness (baseline)

theorem typeIValue_mul (lo hi : ℝ) (W F : List Row→ℂ) :
    typeIValue lo hi (fun rows => W rows*F rows)=
      fun rows => W rows*typeIValue lo hi F rows := by
  funext rows
  unfold typeIValue
  split_ifs <;> simp

theorem typeI_all_group_normalization {b kap s : ℝ}
    (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96) (N : ℕ)
    (chi : ℝ→ℝ) (Z lo hi : ℝ) (js ns : List ℕ) (F : List Row→ℂ) :
    atlasEval chi Z js ns (typeIValue lo hi (fun rows =>
      (listExtension (pairLicence hb hs hg N) (originalProducts rows):ℂ)*F rows))=
    numeratorAtlas chi Z js ns (typeIValue lo hi (fun rows =>
      (listExtension (normalizedLicence hb (by norm_num : (0:ℝ)<1)
        (by norm_num : (0:ℝ)<19/96) hs (by simpa only [one_mul] using hg) N)
        (originalProducts rows):ℂ)*F rows)) := by
  simp only [typeIValue_mul]
  exact all_group_normalization hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
    hs (by simpa only [one_mul] using hg) N chi Z js ns (typeIValue lo hi F)

theorem typeI_capSupported (cap : ℕ) (lo hi : ℝ) (F : List Row→ℂ)
    (hF : CapSupported cap F) : CapSupported cap (typeIValue lo hi F) := by
  intro rows r hr hlarge
  unfold typeIValue
  split_ifs
  · exact hF rows r hr hlarge
  · rfl

/-- Both original group products have the temporary enumeration cap N.
Actual smooth support removes it; the same source test retains typeI,
the complete-product trim and the signed arithmetic kernel. -/
theorem noMediumAtlas_eq_fullEval {b kap s : ℝ}
    (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96)
    (N K : ℕ) (kap0 lo hi : ℝ) (S : Finset ℕ) (rho : ℕ→ℂ) (js : List ℕ)
    (hlen : js.length=2)
    (hcap : ∀ p : Fin 2→ℝ,profile b kap s N p≠0 → ∀ i,p i<(N:ℝ)) :
    noMediumAtlas (pairLicence hb hs hg N) K N N kap0 lo hi S rho js=
      fullEval P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js
        (typeIValue lo hi (upperTest hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
          hs (by simpa only [one_mul] using hg) N kap0 S rho)) := by
  let F := upperTest hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
    hs (by simpa only [one_mul] using hg) N kap0 S rho
  have hF : CapSupported N F := upperTest_capSupported hb (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<19/96) hs (by simpa only [one_mul] using hg) N hcap kap0 S rho
  unfold noMediumAtlas
  calc
    _=∑ ps∈integerWords N 2,numeratorAtlas P5Z.ActualEtaPsiOccurrenceBudget.chi
        (beforeHBCutoff K js) js ps (typeIValue lo hi F) := by
      apply Finset.sum_congr rfl
      intro ps hps
      simpa only [F,upperTest,mul_assoc] using typeI_all_group_normalization hb hs hg N
        P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) lo hi js ps
        (fun rows => (P5Z.ActualEtaPsiOccurrenceBudget.eta
          (((originalProducts rows).prod:ℝ)/(N:ℝ)^(1-kap0)):ℂ)*
          wordKernel S rho N (originalProducts rows))
    _=_ := by
      simpa only [hlen] using numerator_source_eq_full_rectangles N
        P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js
        (typeIValue lo hi F) (typeI_capSupported N lo hi F hF)

end
end ImbalancedChen.P4BOriginalNoMediumAtlasNormalization
