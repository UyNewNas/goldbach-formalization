import ImbalancedChen.P5ActualUpperPairHBLogTransport
import ImbalancedChen.P4BActualSmoothPhysicalPPA3

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The independently present production rank-two upper caller is connected
to its actual ALL-group HB expansion.  Its signed coefficient is literally
attachedUpperCoefficient, also in the exact coprime mean and every reserve.
Only the existing recursive HB denominators are absorbed into the G smooth
normalizer.  The original prime weight and physical product-fibre weight
are RAW, and the complete-product trim/proper-power/rough reserves remain.
-/
namespace ImbalancedChen.P5ActualUpperPairOriginalHBSource
noncomputable section
open Classical
open scoped BigOperators
open P5ActualIndependentUpperPairProfile P5ActualUpperPairHBLogTransport
open P5Z.PerGroupIntegerHBAtlasPushforward P5Z.LicensedOriginalIntegerProfile
open P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.OriginalPrimeAllGroupHBDiscrepancy P5Z.OriginalPrimeAtlasReserveBranches
open P5Z.IndependentPrimeSourceWordDictionary
open Part3.AllKLambdaChartCorrection Part3.OriginalProperPowerActualChart

/-- The SAME original HB block/factor banks with the actual log-normalized
pair numerator.  This is not a proposed Family cover or a new prime caller. -/
def normalizedAllGroupAtlas (D : Parameters) (b : Band D) (N K : ℕ)
    (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) : ℂ :=
  ∑ ps ∈ integerWords N 2,
    numeratorAtlas P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js ps
      (fun rows =>
        (listExtension (P5Z.ActualIndependentUpperPairLogFields.licence D b N)
          (originalProducts rows) : ℂ) *
        (P5Z.ActualEtaPsiOccurrenceBudget.eta
          (((originalProducts rows).prod : ℝ) / (N : ℝ) ^ (1 - kappa0)) : ℂ) *
        wordKernel Q rho N (originalProducts rows))

theorem actual_rawAtlas_eq_normalized (D : Parameters) (b : Band D) (N K : ℕ)
    (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) :
    allGroupAtlas (P5ActualIndependentUpperPairProfile.licence D b N)
      K N N kappa0 Q rho js = normalizedAllGroupAtlas D b N K kappa0 Q rho js := by
  unfold allGroupAtlas normalizedAllGroupAtlas
  apply Finset.sum_congr rfl
  intro ps hps
  simpa only [mul_assoc] using actual_all_group_normalization D b N
    P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js ps
    (fun rows =>
      (P5Z.ActualEtaPsiOccurrenceBudget.eta
        (((originalProducts rows).prod : ℝ) / (N : ℝ) ^ (1 - kappa0)) : ℂ) *
        wordKernel Q rho N (originalProducts rows))

/-- The source identification is proved on the ORIGINAL labelled prime
carrier.  No equality with a candidate source/atlas is an assumption. -/
theorem original_upper_pair_eq_licensed_source (D : Parameters) (b : Band D)
    {N : ℕ} (hN : 2 ≤ N) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 2 N N Q rho
      (P4B.smoothPhysicalPairOuterRamp b.val N (manuscriptHalfProductCutoff D.kappa N)
        (selected D).width) =
      Part3.primeProductSignedError 2 N N Q rho
        (fun u => P5ActualIndependentUpperPairProfile.integerWeight D b N
          (fun i => (u i).val)) := by
  unfold Part3.primeProductSignedError
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  rw [actual_original_caller D b hN u hu]
  rfl

/-- Explicit restoring expression, including every original chart and
the actual trim/proper-power/rough-prime source corrections. -/
def restoredAtlas (D : Parameters) (b : Band D) (N K : ℕ) (kappa0 : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) : ℂ :=
  trimReserve (P5ActualIndependentUpperPairProfile.licence D b N)
    N N kappa0 Q (fun q => (rho q : ℂ)) +
    ∑ js ∈ chartBank N 2,
      (normalizedAllGroupAtlas D b N K kappa0 Q (fun q => (rho q : ℂ)) js -
        properPowerReserve (P5ActualIndependentUpperPairProfile.licence D b N)
          K N N kappa0 Q (fun q => (rho q : ℂ)) js +
        roughPrimeReserve (P5ActualIndependentUpperPairProfile.licence D b N)
          K N N kappa0 Q (fun q => (rho q : ℂ)) js)

/-- Actual prime-projector/restoring identity.  The original raw prime
test is retained on the left; both original reciprocal group logs have
been incorporated in the right-hand smooth numerator. -/
theorem original_upper_pair_normalized_HB (D : Parameters) (b : Band D)
    {N : ℕ} (hN : 2 ≤ N) (K : ℕ) (kappa0 : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (Part3.primeProductSignedError 2 N N Q rho
      (P4B.smoothPhysicalPairOuterRamp b.val N (manuscriptHalfProductCutoff D.kappa N)
        (selected D).width) : ℂ) = restoredAtlas D b N K kappa0 Q rho := by
  rw [original_upper_pair_eq_licensed_source D b hN Q rho]
  rw [original_prime_allGroup_discrepancy
    (P5ActualIndependentUpperPairProfile.licence D b N) K N N kappa0 Q rho]
  unfold restoredAtlas
  congr 1
  apply Finset.sum_congr rfl
  intro js hjs
  rw [actual_rawAtlas_eq_normalized]

/-- Specialization to the exact original upper coefficient, with no
amplitude, density, cap-plan, distribution or source-equality premise. -/
theorem attached_upper_pair_normalized_HB (D : Parameters) (b : Band D)
    {N : ℕ} (hN : 2 ≤ N) (K : ℕ) (kappa0 nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    (Part3.primeProductSignedError 2 N N
      (attachedUpperModuli nu r epsilon retain cap N)
      (attachedUpperCoefficient nu r epsilon retain cap N)
      (P4B.smoothPhysicalPairOuterRamp b.val N (manuscriptHalfProductCutoff D.kappa N)
        (selected D).width) : ℂ) =
      restoredAtlas D b N K kappa0
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) :=
  original_upper_pair_normalized_HB D b hN K kappa0 _ _

/-- Consumer in the genuine physical integer product fibre.  Its original
noninjective labelled multiplicities and exact coprime mass are preserved;
products above N have not been truncated away. -/
theorem attached_upper_physical_fibre_normalized_HB (D : Parameters) (b : Band D)
    {N : ℕ} (hN : 2 ≤ N) (K : ℕ) (kappa0 nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    ((∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N q *
        finitePrimitiveDiscrepancy (P4BLabelledOuterPushforward.productCarrier N)
          (P4BLabelledOuterPushforward.productWeight N
            (P4B.smoothPhysicalPairOuterRamp b.val N
              (manuscriptHalfProductCutoff D.kappa N) (selected D).width)) N q) : ℂ) =
      restoredAtlas D b N K kappa0
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) := by
  rw [P4BLabelledOuterPushforward.signed_productWeight_eq_primeProductSignedError]
  exact attached_upper_pair_normalized_HB D b hN K kappa0 nu r epsilon retain cap

/-- The actual remaining trim has a real small complete-product carrier.
At the genuine original scale threshold its exact-product=N part vanishes
BEFORE a positive-distance divisor bound can be used.  No trim estimate
is asserted or hidden in the premises. -/
theorem actual_active_trim_support (D : Parameters) (b : Band D)
    {N : ℕ} (hN : 2 ≤ N) (kappa0 : ℝ)
    (hscale : (2 : ℝ) ≤ (N : ℝ) ^ kappa0)
    (Q : Finset ℕ) (rho : ℕ → ℂ) {ps : List ℕ}
    (hps : ps ∈ P5Z.ActualLabelledPrimeSmoothCharts.primeTuples N 2)
    (hactive :
      (1 - (P5Z.ActualEtaPsiOccurrenceBudget.eta
        ((ps.prod : ℝ) / (N : ℝ) ^ (1 - kappa0)) : ℂ)) *
        (listExtension (P5ActualIndependentUpperPairProfile.licence D b N) ps : ℂ) *
          wordKernel Q rho N ps ≠ 0) :
    (N : ℝ) ^ (1 - D.kappaZero) < (ps.prod : ℝ) ∧
      (ps.prod : ℝ) < 2 * (N : ℝ) ^ (1 - kappa0) ∧ ps.prod ≠ N := by
  have hpair := (mul_ne_zero_iff.mp hactive).1
  have htrim := (mul_ne_zero_iff.mp hpair).1
  have hWc := (mul_ne_zero_iff.mp hpair).2
  have hW : listExtension (P5ActualIndependentUpperPairProfile.licence D b N) ps ≠ 0 := by
    intro hzero
    exact hWc (by rw [hzero]; simp)
  have hlen := (P5Z.ActualLabelledPrimeSmoothCharts.primeTuples_spec N 2 hps).1
  have hprofile : P5ActualIndependentUpperPairProfile.profile D b N
      (fun i => (wordVector 2 ps i : ℝ)) ≠ 0 := by
    change integerExtension (P5ActualIndependentUpperPairProfile.licence D b N)
      (wordVector 2 ps) ≠ 0
    rw [← listExtension_ofFn, ofFn_wordVector hlen]
    exact hW
  have hs := profile_nonzero_data D b hprofile
  have hprod : (ps.prod : ℝ) =
      (wordVector 2 ps 0 : ℝ) * (wordVector 2 ps 1 : ℝ) := by
    rw [← ofFn_wordVector hlen, List.prod_ofFn, Nat.cast_prod, Fin.prod_univ_two]
  refine ⟨?_, trim_factor_small (by omega) kappa0 ps htrim, ?_⟩
  · rw [hprod]
    exact hs.2.2.2.1
  · intro heq
    exact htrim (trim_exact_product_zero (by omega) kappa0 hscale ps heq)

end
end ImbalancedChen.P5ActualUpperPairOriginalHBSource
