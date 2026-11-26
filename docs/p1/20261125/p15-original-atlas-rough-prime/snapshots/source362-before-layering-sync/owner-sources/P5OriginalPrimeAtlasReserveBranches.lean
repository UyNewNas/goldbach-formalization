import ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The explicit source corrections retain their REAL carriers. The trim has
no exact-product=T term once the original scale threshold holds. Rough
prime deletion is supported on an actual prime below the chart cutoff.
The actual all-group atlas is split into its original medium and no-medium
row branches before estimates, keeping the same count/mean functional.
No local arithmetic-mode conclusion is supplied as a new premise.
-/
namespace ImbalancedChen.P5Z.OriginalPrimeAtlasReserveBranches
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.PrimeProducts
open IndependentPrimeSourceWordDictionary OriginalPrimeAllGroupHBDiscrepancy
open LicensedOriginalIntegerProfile AdmissibleAllRankIntegerGeometricFamily
open ExactOriginalSmoothDyadicPartition ActualLabelledPrimeSmoothCharts
open PerGroupIntegerHBAtlasPushforward OriginalPrimeChartHBWitnesses
open ImbalancedChen.Part3.AllKLambdaChartCorrection
open ImbalancedChen.Part3.AllKFamilyLambdaCorrectionBound

theorem trim_factor_small {T : ℕ} (hT : 0 < T) (κ₀ : ℝ) (ps : List ℕ)
    (hactive : 1 - (ActualEtaPsiOccurrenceBudget.eta
      ((ps.prod : ℝ) / (T : ℝ) ^ (1 - κ₀)) : ℂ) ≠ 0) :
    (ps.prod : ℝ) < 2 * (T : ℝ) ^ (1 - κ₀) := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hden := Real.rpow_pos_of_pos hTR (1 - κ₀)
  by_contra hnot
  have harg : 2 ≤ (ps.prod : ℝ) / (T : ℝ) ^ (1 - κ₀) :=
    (le_div_iff₀ hden).mpr (le_of_not_gt hnot)
  exact hactive (by rw [ActualEtaPsiOccurrenceBudget.eta_one harg]; simp)

/-- This excludes equality BEFORE applying any positive-distance divisor
bound. The exact-product correction is not silently charged by tau(0). -/
theorem trim_exact_product_zero {T : ℕ} (hT : 0 < T) (κ₀ : ℝ)
    (hscale : (2 : ℝ) ≤ (T : ℝ) ^ κ₀) (ps : List ℕ) (hprod : ps.prod = T) :
    1 - (ActualEtaPsiOccurrenceBudget.eta
      ((ps.prod : ℝ) / (T : ℝ) ^ (1 - κ₀)) : ℂ) = 0 := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have heq : (T : ℝ) / (T : ℝ) ^ (1 - κ₀) = (T : ℝ) ^ κ₀ := by
    calc
      _ = (T : ℝ) ^ (1 - (1 - κ₀)) := by rw [Real.rpow_sub hTR, Real.rpow_one]
      _ = _ := by congr 1; ring
  rw [hprod, heq, ActualEtaPsiOccurrenceBudget.eta_one hscale]
  simp

theorem roughWord_one_on_prime_word {ps : List ℕ} (z : ℝ)
    (hprime : primeOnly ps) (hrough : ∀ p ∈ ps, z < (p : ℝ)) : roughWord z ps = 1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp := hprime p (by simp)
    have hz := hrough p (by simp)
    have htailP : primeOnly ps := fun q hq => hprime q (List.mem_cons_of_mem p hq)
    have htailZ : ∀ q ∈ ps, z < (q : ℝ) := fun q hq => hrough q (List.mem_cons_of_mem p hq)
    rw [roughWord, prime_rough_one hp hz, ih htailP htailZ, mul_one]

theorem rough_prime_defect_witness {ps : List ℕ} (z : ℝ)
    (hprime : primeOnly ps) (hdefect : 1 - roughWord z ps ≠ 0) :
    ∃ p ∈ ps, (p : ℝ) ≤ z := by
  by_contra hnot
  have hrough : ∀ p ∈ ps, z < (p : ℝ) := by
    intro p hp
    by_contra h
    exact hnot ⟨p, hp, le_of_not_gt h⟩
  exact hdefect (by rw [roughWord_one_on_prime_word z hprime hrough]; simp)

/-- A real original source-band inequality, rather than a desired rough
reserve estimate, annihilates this explicit prime correction. -/
theorem family_rough_reserve_zero {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar + 1)) (K cap : ℕ) (κ₀ : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ)
    (hband : beforeHBCutoff K js < A.lower * (T : ℝ) ^ A.aStar) :
    roughPrimeReserve (licence A T k) K cap T κ₀ Q rho js = 0 := by
  unfold roughPrimeReserve
  apply Finset.sum_eq_zero
  intro ps hps
  by_cases hchart : originalChart (licence A T k) T κ₀ js ps = 0
  · simp [hchart]
  · have hlen := (primeTuples_spec cap k.val hps).1
    have hprime : primeOnly ps := fun p hp => ((primeTuples_spec cap k.val hps).2 p hp).1
    have hW : bankWeight A T k ps ≠ 0 := by
      intro hz
      apply hchart
      change (listExtension (licence A T k) ps : ℂ) = 0 at hz
      simp only [originalChart, chartTerm, trimmedWeight, hz, mul_zero]
    have hs := bankWeight_support A T k hlen hW
    have hrough : ∀ p ∈ ps, beforeHBCutoff K js < (p : ℝ) :=
      fun p hp => hband.trans_le (hs.1 p hp)
    rw [roughWord_one_on_prime_word _ hprime hrough]
    simp

def mediumAtlas {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ} (L : Licence k Wprime)
    (K cap T : ℕ) (κ₀ lo hi : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) : ℂ :=
  ∑ ps ∈ ImbalancedChen.Part3.OriginalProperPowerActualChart.integerWords cap k,
    atlasEval ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js ps
      (mediumValue lo hi (fun rows =>
        (listExtension L (originalProducts rows) : ℂ) *
          (ActualEtaPsiOccurrenceBudget.eta
            (((originalProducts rows).prod : ℝ) / (T : ℝ) ^ (1 - κ₀)) : ℂ) *
          wordKernel Q rho T (originalProducts rows)))

def noMediumAtlas {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ} (L : Licence k Wprime)
    (K cap T : ℕ) (κ₀ lo hi : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) : ℂ :=
  ∑ ps ∈ ImbalancedChen.Part3.OriginalProperPowerActualChart.integerWords cap k,
    atlasEval ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js ps
      (typeIValue lo hi (fun rows =>
        (listExtension L (originalProducts rows) : ℂ) *
          (ActualEtaPsiOccurrenceBudget.eta
            (((originalProducts rows).prod : ℝ) / (T : ℝ) ^ (1 - κ₀)) : ℂ) *
          wordKernel Q rho T (originalProducts rows)))

/-- The original row test of the actual ALL-group atlas is split, not
an arbitrary separated-mode surrogate. Both branches retain all actual
group products and the SAME signed q kernel and exact coprime mean. -/
theorem allGroup_actual_branch_split {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (K cap T : ℕ) (κ₀ lo hi : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) :
    allGroupAtlas L K cap T κ₀ Q rho js =
      mediumAtlas L K cap T κ₀ lo hi Q rho js +
        noMediumAtlas L K cap T κ₀ lo hi Q rho js := by
  unfold allGroupAtlas mediumAtlas noMediumAtlas
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ps hps
  exact atlas_exact_branch_partition ActualEtaPsiOccurrenceBudget.chi
    (beforeHBCutoff K js) lo hi js ps _

def originalMediumLow (ζ : ℝ) (js : List ℕ) : ℝ := (scales js).prod ^ (3 * ζ)

def originalMediumHigh (ζ : ℝ) (js : List ℕ) : ℝ :=
  (scales js).prod ^ (1 / 3 + ζ / 4 : ℝ)

/-- The exact ORIGINAL source now reaches the actual original-window
medium/no-medium row carriers. There is no spectral or Brun conclusion
hidden in this identity; those internal estimates still have to apply to
these very carriers and to the unchanged signed physical rho. -/
theorem original_prime_discrepancy_mode_carriers {k : ℕ}
    {Wprime : (Fin k → ℕ) → ℝ} (L : Licence k Wprime)
    (K cap T : ℕ) (κ₀ ζ : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (Part3.primeProductSignedError k cap T Q rho
      (fun u => Wprime (fun i => (u i).val)) : ℂ) =
      trimReserve L cap T κ₀ Q (fun q => (rho q : ℂ)) +
        ∑ js ∈ chartBank cap k,
          (mediumAtlas L K cap T κ₀ (originalMediumLow ζ js) (originalMediumHigh ζ js)
              Q (fun q => (rho q : ℂ)) js +
            noMediumAtlas L K cap T κ₀ (originalMediumLow ζ js) (originalMediumHigh ζ js)
              Q (fun q => (rho q : ℂ)) js -
            properPowerReserve L K cap T κ₀ Q (fun q => (rho q : ℂ)) js +
            roughPrimeReserve L K cap T κ₀ Q (fun q => (rho q : ℂ)) js) := by
  rw [original_prime_allGroup_discrepancy L K cap T κ₀ Q rho]
  congr 1
  apply Finset.sum_congr rfl
  intro js hjs
  rw [allGroup_actual_branch_split L K cap T κ₀ (originalMediumLow ζ js)
    (originalMediumHigh ζ js)]

end
end ImbalancedChen.P5Z.OriginalPrimeAtlasReserveBranches
