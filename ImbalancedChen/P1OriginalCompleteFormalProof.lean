import ImbalancedChen.P1OriginalFinalPolicyRawBound
import ImbalancedChen.P1OriginalFinalPolicyStructure
import ImbalancedChen.P1OriginalFinalPolicyAncestorReads
import ImbalancedChen.P4AOriginalFiniteFallbackPPSchedule
import ImbalancedChen.P4AOriginalFiniteAll22CofinalCoefficient
import ImbalancedChen.P4AHistoricalPhysicalSavingsReserve

/-!
RECONSTRUCTED SOURCE CANDIDATE / NOT YET COMPILED OR KERNEL ACCEPTED.

This new thin endpoint uses the single q selected by the reconstructed raw theorem.
The ordinary PP parameter schedule is called once, at that q, to choose beta
and the aligned k. The raw and compiler thresholds are then joined. No second
coefficient or independent cofinal mesh is selected.

The original density reserve is fixed at one half, as in the existing
`P4AOriginalFiniteAll22FineDensity` construction. The budget identity, actual
presieve correction, raw/physical identity, integer majorant and ancestor
programs are existing suppliers. This file does not establish the signed
distribution estimate: the actual same-rho distribution error remains in the
finite counting conclusion. No Fine schedule or Fine high-atom module is used.
-/

set_option autoImplicit false

namespace ImbalancedChen.P1OriginalCompleteFormalProof

noncomputable section
open scoped Classical
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AOriginalFiniteAll22RawLedger (finalPolicy)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P5OriginalCommonPositivePresieve (normalize)
open P4AAll22OriginalKLedger20261024zSourceOnly
  (quotedAll22Raw densityReserve compilerReserve exactSlack
    densityReserve_pos compilerReserve_pos exactSlack_pos)
open P4AOriginalFiniteAll22CofinalCoefficient (upper)
open P4AUpperTaggedParityCompiler («universe»)
open P4AOrderedThirdRectangleRate (index position)
open P4AOrderedThirdRankReads (admit)
open P4AOriginalFiniteFallbackPrograms (code)
open P4AFull87ActualAffineDeletion (coords)

/-- A common cofinal policy, one physical coefficient, and one beta/k choice.
The raw upper bound, compiler payment, K-density, integer majorant, nonzero
support and actual rough-ancestor programs all concern this literal policy
and rho. Every finite parameter precedes the sufficiently large even target.
The distribution error is retained, not assumed bounded. -/
theorem exists_cofinal_same_policy_same_coefficient
    (eMax : ℝ) (heMax : 0 < eMax) :
    ∃ h : ℝ, 0 < h ∧
    ∃ m0 : ℕ, ∀ m ≥ m0,
    ∃ r0 : ℕ, ∀ r ≥ r0,
    ∃ n0 : ℕ, ∀ n ≥ n0,
    ∃ E : ℝ, 0 < E ∧ E ≤ eMax ∧
    ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < E →
    ∀ a : ℝ, 0 < a → a ≤ 1 / 800 →
    ∀ qMin mMin : ℕ,
    ∃ q : ℕ, qMin ≤ q ∧ 0 < q ∧ 256 ∣ q ∧ mMin ≤ refinedMesh q ∧
    ∀ budget nu v betaMax : ℝ,
      0 < budget → 0 < nu → 0 < v → nu * v = 19 / 96 → 0 < betaMax →
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 / 8 ∧ beta < betaMax ∧ beta ^ 2 < v ∧
      nu * beta ^ 2 < a ∧ nu * beta ^ 2 ≤ h ∧
      nu * beta < 1 / 1000 ∧ nu * beta < budget / 32 ∧
    ∃ k : ℕ,
      alignedWidth (jointIndex (bank m) (data e q a).m) k *
        ((P4AHeldTaggedCompilerSupport.J0 (nu * beta ^ 2) : ℝ) + 1) ≤ budget ∧
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, Even N →
      let omega := nu * beta ^ 2
      let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
      let w := (N : ℝ) ^ omega
      let z := cutoff N
      let L := (N : ℝ) ^ (nu * beta)
      let Q := moduli N w
      let rho := P4AOriginalFiniteFallbackPolicy.rho
        (bank m) r n e q a omega N tau L
      let f := F (bank m) (width r) n (data e q a) omega N
      (∀ p : List ℕ, finalPolicy m r n e q a omega N true p = true) ∧
      rho = P4AUpperTaggedBetaAttachment.rho
        (finalPolicy m r n e q a omega N false) (fun _ => []) N N w z tau L ∧
      normalize N (rawRoot (finalPolicy m r n e q a omega N) N) <
        quotedAll22Raw + densityReserve / 2 ∧
      ((N : ℝ) / Real.log (N : ℝ)) *
        P4AFiniteCapTaggedConstructor.compilerExpense f (fun _ => []) N N w z tau L <
        compilerReserve * singularNormalization N ∧
      physicalDensitySum Q rho < upper m r n e q a omega (densityReserve / 2) N ∧
      physicalDensitySum Q rho < currentK * (singularSeries N / Real.log (N : ℝ)) ∧
      (∀ x : ℤ,
        (if x.natAbs.Coprime (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0) ≤
          physicalDivisorSum Q rho x.natAbs ∧
        0 ≤ physicalDivisorSum Q rho x.natAbs) ∧
      (∀ d : ℕ, |rho d| ≤ 1) ∧
      (∀ d : ℕ, rho d ≠ 0 →
        d ∈ Q ∧ Squarefree d ∧ d.Coprime N ∧ (d : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ)) ∧
      (∀ d : ℕ, d ∈ Q →
        ∃ s x : ℕ, s ∈ actualSmallRosserSupport N N w ∧
          x ∈ «universe» N N w z ∧ d = s * x ∧
          ∀ j : ℕ, j ≤ x.primeFactorsList.length → polarityAfter true j = false →
            index (position j) + 1 ≤ j ∧
              finalPolicy m r n e q a omega N false (rosserAncestor j x.primeFactorsList) =
                admit N ((code (bank m) (width r) n (data e q a) (position j)).eval
                  (coords N _ x.primeFactorsList.reverse))
                  (rosserAncestor j x.primeFactorsList)) ∧
      ∀ b T : ℝ, 0 < b → b < 1 → 0 < T → (Nat.ceil z : ℝ) ≤ T ^ (b / (1 + b)) →
        (RealB b N : ℝ) ≤ ((realHalfProductSource b N T).card : ℝ) *
            upper m r n e q a omega (densityReserve / 2) N +
          realPhysicalDistributionError b N T Q rho + (Nat.ceil z : ℝ) + (T + 1) := by
  obtain ⟨h, hh, m0, hM⟩ :=
    P1OriginalFinalPolicyRawBound.exists_cofinal_final_raw_upper
      (densityReserve / 2) eMax (half_pos densityReserve_pos) heMax
  refine ⟨h, hh, m0, ?_⟩
  intro m hm
  obtain ⟨r0, hR⟩ := hM m hm
  refine ⟨r0, ?_⟩
  intro r hr
  obtain ⟨n0, hC⟩ := hR r hr
  refine ⟨n0, ?_⟩
  intro n hn
  obtain ⟨E, hE, hEmax, hCE⟩ := hC n hn
  refine ⟨E, hE, hEmax, ?_⟩
  intro e he heE a ha haSmall qMin mMin
  obtain ⟨q, hq, hqpos, hqdiv, hmesh, hQ⟩ :=
    hCE e he heE a ha haSmall qMin mMin
  refine ⟨q, hq, hqpos, hqdiv, hmesh, ?_⟩
  intro budget nu v betaMax hbudget hnu hv hcut hmax
  have heRat : 0 < e := by exact_mod_cast he
  obtain ⟨beta, hbeta, hb8, hbCeil, hbSq, hwa, hlog, hbetaBudget,
      k, hmeshBudget, NC, hNC, hCN⟩ :=
    P4AOriginalFiniteFallbackPPSchedule.joined
      (bank m) (P4AOriginalFiniteFallbackCanonical.bounded m)
      r n e heRat.le q a ha budget hbudget nu v compilerReserve
      (min betaMax (h / nu)) hnu hv hcut compilerReserve_pos
      (lt_min hmax (div_pos hh hnu))
  have hbMax : beta < betaMax := hbCeil.trans_le (min_le_left _ _)
  have hbOne : beta < 1 := by linarith only [hb8]
  have hbSqSelf : beta ^ 2 ≤ beta := by nlinarith only [hbeta.le, hbOne.le]
  let omega := nu * beta ^ 2
  let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
  have homega : 0 < omega := mul_pos hnu (sq_pos_of_pos hbeta)
  have homegaR : omega < thirdPrefixRho := by
    have H := mul_lt_mul_of_pos_left hbSq hnu
    rw [hcut] at H
    exact H
  have homegaBeta : omega ≤ nu * beta :=
    mul_le_mul_of_nonneg_left hbSqSelf hnu.le
  have homegaH : omega ≤ h := by
    have H := (lt_div_iff₀ hnu).mp (hbCeil.trans_le (min_le_right _ _))
    exact homegaBeta.trans (by linarith only [H])
  obtain ⟨NR, hNR, hRN⟩ := hQ omega homega homegaR hwa.le homegaH
  refine ⟨beta, hbeta, hb8, hbMax, hbSq, hwa, homegaH, hlog, hbetaBudget,
    k, hmeshBudget, max NC NR, hNC.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hNC' : NC ≤ N := (le_max_left _ _).trans hN
  have hNR' : NR ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNC.trans hNC'
  have hN1 : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN1
  have hRaw := hRN N hNR' hEven
  obtain ⟨hExpense, hDensity, hSupport, hCount⟩ := hCN N hNC' hEven
  dsimp only at hExpense hDensity hSupport hCount ⊢
  have hRawScale : rawRoot (finalPolicy m r n e q a omega N) N ≤
      (quotedAll22Raw + densityReserve / 2) *
        (singularSeries N / Real.log (N : ℝ)) :=
    (density_le_manuscriptScale_iff_normalized hN2 _ _).mpr hRaw.le
  have hCoefficient : quotedAll22Raw + densityReserve / 2 + compilerReserve =
      currentK - densityReserve - exactSlack + densityReserve / 2 := by
    linarith only [P4AAll22OriginalKLedger20261024zSourceOnly.exact_original_budget_identity]
  rw [P4AOriginalFiniteAll22PhysicalLedger.reserve_raw_is_actual_final] at hDensity
  have hUpper : physicalDensitySum (moduli N ((N : ℝ) ^ omega))
      (P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau
        ((N : ℝ) ^ (nu * beta))) <
      upper m r n e q a omega (densityReserve / 2) N := by
    have hScale : rawRoot (finalPolicy m r n e q a omega N) N +
        compilerReserve * (singularSeries N / Real.log (N : ℝ)) ≤
        (currentK - densityReserve - exactSlack + densityReserve / 2) *
          (singularSeries N / Real.log (N : ℝ)) := by
      calc
        _ ≤ (quotedAll22Raw + densityReserve / 2) *
            (singularSeries N / Real.log (N : ℝ)) +
            compilerReserve * (singularSeries N / Real.log (N : ℝ)) :=
          add_le_add_right hRawScale _
        _ = _ := by rw [← add_mul, hCoefficient]
    unfold upper
    linarith only [hDensity, hScale]
  have hL : 1 < (N : ℝ) ^ (nu * beta) :=
    Real.one_lt_rpow hNr (mul_pos hnu hbeta)
  have hwL : (N : ℝ) ^ omega ≤ (N : ℝ) ^ (nu * beta) :=
    Real.rpow_le_rpow_of_exponent_le hNr.le homegaBeta
  have hwz : (N : ℝ) ^ omega ≤ cutoff N :=
    Real.rpow_le_rpow_of_exponent_le hNr.le homegaR.le
  have hz : cutoff N ≤ (N : ℝ) := by
    simpa only [cutoff, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNr.le
        (show (19 / 96 : ℝ) ≤ 1 by norm_num)
  have hCorrection := p4aActualPresieveCorrection_nonneg
    (F (bank m) (width r) n (data e q a) omega N)
    N N ((N : ℝ) ^ omega) (cutoff N) hwz
  have hCoefficientK : currentK - densityReserve - exactSlack + densityReserve / 2 < currentK := by
    linarith only [densityReserve_pos, exactSlack_pos]
  have hScaleK := mul_lt_mul_of_pos_right hCoefficientK (densityScale_pos hN2)
  have hUpperK : upper m r n e q a omega (densityReserve / 2) N <
      currentK * (singularSeries N / Real.log (N : ℝ)) := by
    unfold upper
    linarith only [hCorrection, hScaleK]
  refine ⟨P1OriginalFinalPolicyStructure.final_policy_even m r n e q a omega N,
    P1OriginalFinalPolicyStructure.final_coefficient_is_same_policy
      m r n e q a omega N tau ((N : ℝ) ^ (nu * beta)),
    hRaw, hExpense, hUpper, hUpper.trans hUpperK, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨P1OriginalFinalPolicyStructure.final_integer_sieve_majorant
        m r n e q a omega N tau ((N : ℝ) ^ (nu * beta)) hL hwL hwz hz x,
      P1OriginalFinalPolicyStructure.final_integer_divisorSum_nonneg
        m r n e q a omega N tau ((N : ℝ) ^ (nu * beta)) hL hwL hwz hz x⟩
  · exact P1OriginalFinalPolicyStructure.final_coefficient_abs_le_one
      m r n e q a omega N tau ((N : ℝ) ^ (nu * beta))
  · intro d hd
    have hdQ := P1OriginalFinalPolicyStructure.final_nonzero_mem_moduli
      m r n e q a omega N tau ((N : ℝ) ^ (nu * beta)) hd
    exact ⟨hdQ, P1OriginalFinalPolicyStructure.final_modulus_squarefree N omega hdQ,
      P1OriginalFinalPolicyStructure.final_modulus_coprime_target N omega hdQ, hSupport d hd⟩
  · intro d hd
    exact P1OriginalFinalPolicyAncestorReads.physical_modulus_ancestor_reads
      m r n e q a omega N hN1 homega.le d hd
  · intro b T hb hb1 hT hgate
    have hFinite := hCount b T hb hb1 hT hgate
    have hMass := mul_le_mul_of_nonneg_left hUpper.le
      (Nat.cast_nonneg (realHalfProductSource b N T).card)
    exact hFinite.trans
      (add_le_add_right (add_le_add_right (add_le_add_right hMass _) _) _)

end
end ImbalancedChen.P1OriginalCompleteFormalProof
