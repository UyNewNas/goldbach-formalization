import ImbalancedChen.P1Full87RealManuscriptGate
import ImbalancedChen.P1Full87LowPhysicalDelta
import ImbalancedChen.P4AOriginalFiniteAll22FineDensity
import ImbalancedChen.P4BCutoffRounding

/-! The sharp half-product receiver on the coefficient chosen by the finite
upper policy.  The common scale is set before the Fine compiler chooses its
precision and aligned grid.  The signed change of the two earlier full87
policies is evaluated at the same parameters on its own support. -/

namespace ImbalancedChen.P1Full87FineSharpReceiver

noncomputable section
open scoped Classical BigOperators
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFull87CompiledCounting (moduli compiled_modulus_dvd)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AOriginalFiniteAll22FineDensity (modulusFamily coefficientFamily)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P1Full87TrueDPolicyDelta (trueDDeltaRho)
open P4AAll22OriginalKLedger20261024zSourceOnly (compilerReserve)

/-- Same Fine witness for the density, strict support and sharp signed count.
Both coprime corrections vanish.  At the unit modulus the final coefficient
and the earlier signed change have different, determined values. -/
theorem exists_fine_sharp_receiver (eMax : ℝ) (heMax : 0 < eMax) :
    ∃ m0 : ℕ, ∀ m ≥ m0, ∃ r0 : ℕ, ∀ r ≥ r0, ∃ n0 : ℕ, ∀ n ≥ n0,
    ∃ E : ℝ, 0 < E ∧ E ≤ eMax ∧ ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < E →
    ∀ a : ℝ, 0 < a → a ≤ 1 / 800 → ∀ qMin mMin : ℕ,
    ∃ q : ℕ, qMin ≤ q ∧ 0 < q ∧ 256 ∣ q ∧ mMin ≤ refinedMesh q ∧
    ∀ etaPP : ℝ, 0 < etaPP → etaPP ≤ P4AOriginalFiniteFallbackCommonGroups.gap m (data e q a) →
    ∀ betaMax extra : ℝ, 0 < betaMax → 0 < extra →
    ∀ fineTolerance : ℝ → ℝ, (∀ b : ℝ, 0 < b → 0 < fineTolerance b) →
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < betaMax ∧
      epsilon ^ 2 < thirdPrefixRho ∧ epsilon ^ 2 < a ∧ epsilon < 1 / 1000 ∧
      epsilon < etaPP / 32 ∧ epsilon < extra / 32 ∧
    ∃ k : ℕ,
      let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
      tau ≤ fineTolerance epsilon ∧
      tau * ((P4AHeldTaggedCompilerSupport.J0 (epsilon ^ 2) : ℝ) + 1) ≤ etaPP ∧
      tau * ((P4AHeldTaggedCompilerSupport.J0 (epsilon ^ 2) : ℝ) + 1) ≤ extra ∧
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, Even N →
      let w := (N : ℝ) ^ (epsilon ^ 2)
      let z := (N : ℝ) ^ thirdPrefixRho
      let L := (N : ℝ) ^ epsilon
      let Q := moduli N w
      let rho := P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a (epsilon ^ 2) N tau L
      let f := F (bank m) (width r) n (data e q a) (epsilon ^ 2) N
      let R := P4AOriginalFull87CompleteSixthDispatch.policy e q a (N : ℝ)
      let S := P4AOriginalFull87LicensedSixthPolicy.policy (width r) n e q a (N : ℝ)
      let Qdelta := actualSmallRoughModuli (S false) N N w z ∪
        actualSmallRoughModuli (R false) N N w z
      let deltaRho := trueDDeltaRho (R false) (S false) N N w z L
      P4AOriginalFiniteFallbackAllHighAtoms.HighAtoms
        m n N (width r) (epsilon ^ 2) tau epsilon etaPP (data e q a) ∧
      ((N : ℝ) / Real.log (N : ℝ)) *
        P4AFiniteCapTaggedConstructor.compilerExpense f (fun _ => []) N N w z tau L <
          compilerReserve * singularNormalization N ∧
      physicalDensitySum Q rho ≤ currentK * (singularSeries N / Real.log (N : ℝ)) ∧
      (∀ d : ℕ, rho d ≠ 0 → (d : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ)) ∧
      rho 1 = 1 ∧ deltaRho 1 = 0 ∧
      ∀ b kappa0 : ℝ, (1 / 2 : ℝ) ≤ b → b < 1 → kappa0 ≤ (1 / 4 : ℝ) →
        let T := manuscriptHalfProductCutoff kappa0 N
        realPhysicalCoprimeCorrection b N T Q rho = 0 ∧
        realPhysicalCoprimeCorrection b N T Qdelta deltaRho = 0 ∧
        (RealB b N : ℝ) ≤ ((realHalfProductSource b N T).card : ℝ) * physicalDensitySum Q rho +
          realPhysicalDistributionError b N T Q rho + (Nat.ceil z : ℝ) + (T + 1) := by
  classical
  obtain ⟨m0, hm0⟩ := P4AOriginalFiniteAll22FineDensity.exists_fine_same_rho_hdensity eMax heMax
  refine ⟨m0, ?_⟩
  intro m hm
  obtain ⟨r0, hr0⟩ := hm0 m hm
  refine ⟨r0, ?_⟩
  intro r hr
  obtain ⟨n0, hn0⟩ := hr0 r hr
  refine ⟨n0, ?_⟩
  intro n hn
  obtain ⟨E, hE, hEmax, heAll⟩ := hn0 n hn
  refine ⟨E, hE, hEmax, ?_⟩
  intro e he heE a ha haSmall qMin mMin
  obtain ⟨q, hqMin, hq, hqDiv, hmesh, hchoose⟩ := heAll e he heE a ha haSmall qMin mMin
  refine ⟨q, hqMin, hq, hqDiv, hmesh, ?_⟩
  intro etaPP hPP hgap betaMax extra hMax hExtra fineTolerance hTol
  have hfine := hchoose etaPP hPP hgap 1 thirdPrefixRho betaMax extra zero_lt_one
    (by norm_num [thirdPrefixRho]) (by simp [thirdPrefixRho]) hMax hExtra fineTolerance hTol
  simp only [one_mul] at hfine
  obtain ⟨epsilon, heps, heps8, hepsMax, hsq, haSq, hsmall, hepPP, hepExtra,
    k, hwidth, hbudget, hextraBudget, _, N0, hN0, hselected⟩ := hfine
  refine ⟨epsilon, heps, heps8, hepsMax, hsq, haSq, hsmall, hepPP, hepExtra,
    k, hwidth, hbudget, hextraBudget, N0, hN0, ?_⟩
  intro N hN hEven
  obtain ⟨hAtoms, hExpense, _, hDensity, hRange, _⟩ := hselected N hN hEven
  let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
  let w := (N : ℝ) ^ (epsilon ^ 2)
  let z := (N : ℝ) ^ thirdPrefixRho
  let L := (N : ℝ) ^ epsilon
  let Q := moduli N w
  let rho := P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a (epsilon ^ 2) N tau L
  have hN2 := hN0.trans hN
  have hN1 : 1 ≤ N := by omega
  have hbase : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hw : 1 < w := Real.one_lt_rpow hbase (sq_pos_of_pos heps)
  have hL : 1 < L := Real.one_lt_rpow hbase heps
  have hepsOne : epsilon ≤ 1 := heps8.le.trans (by norm_num)
  have hwL : w ≤ L := by
    apply Real.rpow_le_rpow_of_exponent_le hbase.le
    simpa only [pow_two, one_mul] using mul_le_mul_of_nonneg_right hepsOne heps.le
  have hwz : w ≤ z := Real.rpow_le_rpow_of_exponent_le hbase.le hsq.le
  have hzN : z ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase.le
      (show thirdPrefixRho ≤ 1 by norm_num [thirdPrefixRho])
  have hmajor : ∀ x : ℕ,
      (if x.Coprime (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho x :=
    P4AOriginalFiniteFallbackCount.upper_majorant (bank m) r n e q a (epsilon ^ 2) N tau L
      hL hwL hwz hzN
  have hunitLower : 1 ≤ physicalDivisorSum Q rho 1 := by simpa using hmajor 1
  have hunit : rho 1 = 1 := by
    have hbound : |rho 1| ≤ 1 := P4AUpperTaggedBetaAttachment.rho_abs_le_one
      (F (bank m) (width r) n (data e q a) (epsilon ^ 2) N) (fun _ => []) N N w z tau L 1
    refine le_antisymm ((le_abs_self _).trans hbound) ?_
    by_cases hmem : (1 : ℕ) ∈ Q
    · simpa [physicalDivisorSum, Nat.dvd_one, Finset.sum_ite_eq', hmem] using hunitLower
    · have habsurd : (1 : ℝ) ≤ 0 := by
        simpa [physicalDivisorSum, Nat.dvd_one, Finset.sum_ite_eq', hmem] using hunitLower
      exact (not_le_of_gt zero_lt_one habsurd).elim
  have hwFive : (1 : ℝ) < w ^ 5 := by
    simpa only [pow_zero] using pow_lt_pow_right₀ hw (show (0 : ℕ) < 5 by omega)
  refine ⟨hAtoms, hExpense, ?_, ?_, hunit, ?_, ?_⟩
  · simpa only [modulusFamily, coefficientFamily, one_mul] using hDensity
  · simpa only [coefficientFamily, one_mul] using hRange
  · exact P1Full87LowPhysicalDelta.actual_full87_true_d_delta_zero_below_fifth
      (width r) n e q a N N 1 w z L hw.le (by simpa using hwFive)
  · intro b kappa0 hb hbOne hkappa
    have hbPos : 0 < b := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hb
    obtain ⟨hT, hgate⟩ :=
      P1Full87RealManuscriptGate.manuscript_real_endpoint_gate_of_weak_exponent hbPos
        (P1Full87RealManuscriptGate.original_nineteen_over_ninety_six_has_source_margin hb hkappa).le
        N hN1
    have hbuffer := P4BCutoffRounding.ceil_le_floor_add_one_of_le
      (Real.rpow_nonneg hT.le _) hgate
    have hzero : realPhysicalCoprimeCorrection b N (manuscriptHalfProductCutoff kappa0 N) Q rho = 0 :=
      P4BCutoffRounding.physicalCoprimeCorrection_eq_zero_of_buffer Q rho hbPos hT hbuffer
        (fun _ hd _ => compiled_modulus_dvd N w hwz hd)
    refine ⟨hzero, ?_, ?_⟩
    · exact P1Full87RealManuscriptGate.actual_full87_manuscript_coprime_correction_zero
        (width r) n e q a b kappa0 epsilon N N hN1 hb hkappa heps.le heps8.le
    · have hcount := RealB_cast_le_same_rho_main_add_errors N (Nat.ceil z) Q rho hbOne hT.le hmajor
      rw [hzero, add_zero] at hcount
      exact hcount

end
end ImbalancedChen.P1Full87FineSharpReceiver
