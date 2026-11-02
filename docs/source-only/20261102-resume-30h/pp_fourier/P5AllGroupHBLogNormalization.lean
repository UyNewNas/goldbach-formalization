import ImbalancedChen.P5ActualUpperPairHBLogTransport
import ImbalancedChen.P5ExistingIndependentFamilyLogNormalization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The frozen H transfer_lambda supplier owns the generic ALL-group
arithmetic denominator migration. Here it is connected to G's genuine
smooth Licence normalizer, for each original group and every integer
word, then to the original prime discrepancy. The same HB restoring
scalars +3, -3, +1 and the original physical rho remain in their positions.
There is no abstract Family-cover premise or retained-mode estimate.
-/
namespace ImbalancedChen.P5Z.AllGroupHBLogNormalization
noncomputable section
open Classical
open scoped BigOperators
open PerGroupIntegerHBAtlasPushforward ExactOriginalSmoothDyadicPartition
open LicensedOriginalIntegerProfile OriginalPrimeAllGroupHBDiscrepancy
open ActualIndependentGroupLogNormalization ExistingIndependentFamilyLogNormalization
open ImbalancedChen.P5ActualUpperPairHBLogTransport
open ImbalancedChen.Part3.OriginalProperPowerActualChart
open ImbalancedChen.PrimeProducts

/-- The geometric normalizer agrees on ALL integer words, including
composite and unit group products. No division by an individual HB
factor's logarithm is introduced. -/
theorem normalized_listExtension {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (ns : List ℕ) :
    listExtension (normalizedLicence L) ns = listExtension L ns / wordLog ns := by
  by_cases hlen : ns.length = k
  · have htest :
        listExtension (normalizedLicence L) (List.ofFn (wordVector k ns)) =
          listExtension L (List.ofFn (wordVector k ns)) /
            wordLog (List.ofFn (wordVector k ns)) := by
      simp only [listExtension_ofFn, wordLog_ofFn, integerExtension]
      exact normalize_nat L.ambient (wordVector k ns)
    simpa only [ofFn_wordVector hlen] using htest
  · simp only [listExtension, dif_neg hlen, zero_div]

/-- The actual shared arithmetic row operator consumes the genuine
smooth normalized licence. F may retain ANY row-dependent branch test;
only the existing original-group logarithms move into the ambient. -/
theorem atlas_normalized_licence {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi : ℝ → ℝ) (z : ℝ)
    (cjs ns : List ℕ) (F : List Row → ℂ) :
    atlasEval chi z cjs ns (fun rows =>
      (listExtension L (originalProducts rows) : ℂ) * F rows) =
      numeratorAtlas chi z cjs ns (fun rows =>
        (listExtension (normalizedLicence L) (originalProducts rows) : ℂ) * F rows) := by
  rw [actual_atlas_denominators]
  symm
  calc
    _ = numeratorAtlas chi z cjs ns (fun rows =>
        ((listExtension L (originalProducts rows) : ℂ) * F rows) / (wordLog ns : ℂ)) := by
      apply numeratorAtlas_congr_on_originalProducts
      intro rows hrows
      simp only [normalized_listExtension, Complex.ofReal_div, hrows]
      ring
    _ = _ := numeratorAtlas_div_const chi z cjs ns _ _

/-- The normalized integer ambient is used on precisely the old ALL-group
carrier. The literal HB restoring scalars stay inside numeratorAtlas. -/
def normalizedAllGroupAtlas {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (K cap T : ℕ) (κ₀ : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) : ℂ :=
  ∑ ps ∈ integerWords cap k,
    numeratorAtlas ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js ps
      (fun rows => (listExtension (normalizedLicence L) (originalProducts rows) : ℂ) *
        ((ActualEtaPsiOccurrenceBudget.eta
          (((originalProducts rows).prod : ℝ) / (T : ℝ) ^ (1 - κ₀)) : ℂ) *
          IndependentPrimeSourceWordDictionary.wordKernel Q rho T (originalProducts rows)))

theorem allGroupAtlas_eq_normalized {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (K cap T : ℕ) (κ₀ : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) :
    allGroupAtlas L K cap T κ₀ Q rho js =
      normalizedAllGroupAtlas L K cap T κ₀ Q rho js := by
  unfold allGroupAtlas normalizedAllGroupAtlas
  apply Finset.sum_congr rfl
  intro ps hps
  simpa only [mul_assoc] using atlas_normalized_licence L
    ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js ps
    (fun rows => (ActualEtaPsiOccurrenceBudget.eta
      (((originalProducts rows).prod : ℝ) / (T : ℝ) ^ (1 - κ₀)) : ℂ) *
        IndependentPrimeSourceWordDictionary.wordKernel Q rho T (originalProducts rows))

/-- The source Wprime is unchanged. Only the HB smooth factor is
normalized; the original prime test is NOT divided by prime logarithms.
All same-Q/rho trim/proper-power/rough-prime reserves remain explicit. -/
theorem original_prime_normalized_allGroup {k : ℕ}
    {Wprime : (Fin k → ℕ) → ℝ} (L : Licence k Wprime)
    (K cap T : ℕ) (κ₀ : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (Part3.primeProductSignedError k cap T Q rho
      (fun u => Wprime (fun i => (u i).val)) : ℂ) =
      trimReserve L cap T κ₀ Q (fun q => (rho q : ℂ)) +
        ∑ js ∈ chartBank cap k,
          (normalizedAllGroupAtlas L K cap T κ₀ Q (fun q => (rho q : ℂ)) js -
            properPowerReserve L K cap T κ₀ Q (fun q => (rho q : ℂ)) js +
              roughPrimeReserve L K cap T κ₀ Q (fun q => (rho q : ℂ)) js) := by
  rw [original_prime_allGroup_discrepancy L K cap T κ₀ Q rho]
  simp_rw [allGroupAtlas_eq_normalized]

end
end ImbalancedChen.P5Z.AllGroupHBLogNormalization
