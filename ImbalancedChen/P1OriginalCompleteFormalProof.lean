import ImbalancedChen.P1OriginalFinalPolicyRawBound
import ImbalancedChen.P1OriginalFinalPolicyStructure
import ImbalancedChen.P1OriginalFinalPolicyAncestorReads
import ImbalancedChen.P4AOriginalFiniteFallbackCandidate

/-!
Static public assembly of the selected original causal-policy outputs.
UNCOMPILED: no compiler, kernel or publication acceptance is asserted.

The canonical fallback bank index m_bank and the original prime-log mesh
index (data e q a).m = refinedMesh q are distinct.  The latter is selected
after e, using the raw theorem's cofinal mMin binder, on the same q.
All22 is reused; no mean, tail, desired saving or Ready premise is added.
The tagged physical coefficient remains distinct from the raw coefficient.
-/
namespace ImbalancedChen.P1OriginalCompleteFormalProof

noncomputable section
open Filter Topology
open scoped Classical
open P4AOriginalFiniteAll22RawLedger (finalPolicy)
open P4AOriginalFiniteFallbackPolicy (F rho)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P4AOriginalFull87CompiledCounting (moduli)
open P5OriginalCommonPositivePresieve (normalize)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P4AAll22OriginalKLedger20261024zSourceOnly (quotedAll22Raw)
open P4AUpperTaggedParityCompiler (universe)
open P4AOrderedThirdRectangleRate (index position)
open P4AOriginalFiniteFallbackPrograms (code)
open P4AOrderedThirdRankReads (admit)
open P4AFull87ActualAffineDeletion (coords)
open HistoricalThirdCoarse.P1ActualTuple (history)

/-- First-stop is recovered from a valid actual selected prefix, rather
than inferred from an isolated later acceptance. -/
theorem firstStop_of_valid_prefix (m_bank r n : ℕ) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (N p : ℕ) (ps : List ℕ)
    (hvalid : FirstExitValidSelection (finalPolicy m_bank r n e q a omega N)
      [] true (p :: ps)) :
    HistoricalThirdCoarse.firstStop (e : ℝ) (data e q a).m (N : ℝ) [p] := by
  have hfirst : finalPolicy m_bank r n e q a omega N false [p] = true := hvalid.1
  exact P1OriginalFinalPolicyStructure.finalPolicy_firstStop
    m_bank r n e q a omega N [p] (by simp) hfirst

/-- The original candidate observation supplies its actual prime box,
ordering and first stop.  Only its literal physical cutoff is observed
separately; no desired geometric licence is a premise. -/
theorem actual_candidate_owner (e : ℚ) (he : 0 ≤ (e : ℝ)) (q : ℕ)
    (a omega : ℝ) (N : ℕ) (hN : 1 < N) (p : Fin 3 → ℕ)
    (hp : p ∈ P4ACatalogFiveCoarseWeightedPayment.candidateTuples (data e q a) N)
    (hcut : (N : ℝ) ^ omega ≤ (p 2 : ℝ)) :
    ∃! j : P4AOriginalOrderedThirdTable.Cell (data e q a).m,
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) (data e q a).m j ∧
      j ∈ P4AOriginalOrderedThirdTable.retained (e : ℝ) (data e q a).m ∧
      P4AOriginalOrderedThirdTable.rawExponent (e : ℝ) (data e q a).m omega N
          (history p) = P4AOriginalOrderedThirdTable.capValue (e : ℝ) (data e q a).m j ∧
      P4AOriginalOrderedThirdTable.capValue (e : ℝ) (data e q a).m j ≤
        VariableEnvelope.cap - 2 * (e : ℝ) := by
  obtain ⟨hanti, hbox, _hfirstCube, hstop⟩ :=
    P4AOriginalFiniteFallbackCandidate.geometry (data e q a) hN hp
  exact P4AOriginalOrderedThirdActualCoefficient.actual_triple
    he hN p hbox hanti hcut hstop

/-- Extract nonempty fixed parameters from the full cofinal raw theorem.
The mesh lower bound is chosen after the actual positive rational e. -/
private theorem exists_fixed_raw_parameters
    (eta eMax : ℝ) (heta : 0 < eta) (heMax : 0 < eMax) :
    ∃ m_bank r n : ℕ, ∃ e : ℚ, 0 < (e : ℝ) ∧ (e : ℝ) ≤ eMax ∧
      (e : ℝ) ≤ 1 / 384 ∧
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 800 ∧
    ∃ q : ℕ, 0 < q ∧ 256 ∣ q ∧
      logPrimeMeshStep 0 (19 / 96) (data e q a).m ≤ (e : ℝ) / 2 ∧
    ∃ omega : ℝ, 0 < omega ∧ omega < thirdPrefixRho ∧ omega ≤ a ∧
      omega ≤ 1 / 32000 ∧
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      normalize N (rawRoot (finalPolicy m_bank r n e q a omega N) N) <
        quotedAll22Raw + eta := by
  have hcap : 0 < min eMax (1 / 384 : ℝ) := lt_min heMax (by norm_num)
  obtain ⟨h, hh, m0, hM⟩ :=
    P1OriginalFinalPolicyRawBound.exists_cofinal_final_raw_upper
      eta (min eMax (1 / 384)) heta hcap
  obtain ⟨r0, hR⟩ := hM m0 (le_refl m0)
  obtain ⟨n0, hC⟩ := hR r0 (le_refl r0)
  obtain ⟨E, hE, hEcap, hQ⟩ := hC n0 (le_refl n0)
  obtain ⟨e, he, heE⟩ := exists_rat_btwn hE
  have heMax' : (e : ℝ) ≤ eMax :=
    (heE.trans_le (hEcap.trans (min_le_left _ _))).le
  have heSmall : (e : ℝ) ≤ 1 / 384 :=
    (heE.trans_le (hEcap.trans (min_le_right _ _))).le
  let a : ℝ := 1 / 800
  have ha : 0 < a := by norm_num [a]
  have haSmall : a ≤ 1 / 800 := le_refl _
  obtain ⟨M, hMesh⟩ := eventually_atTop.mp
    ((tendsto_logPrimeMeshStep 0 (19 / 96)).eventually (gt_mem_nhds (half_pos he)))
  obtain ⟨q, _hqMin, hqpos, hqdiv, hqmesh, hOmega⟩ :=
    hQ e he heE a ha haSmall 0 M
  have hstep : logPrimeMeshStep 0 (19 / 96) (data e q a).m ≤ (e : ℝ) / 2 :=
    (hMesh (refinedMesh q) hqmesh).le
  let small : ℝ := min a (min h (min thirdPrefixRho (1 / 32000)))
  have hrho : 0 < thirdPrefixRho := by norm_num [thirdPrefixRho]
  have hsmall : 0 < small := lt_min ha (lt_min hh (lt_min hrho (by norm_num)))
  have hsa : small ≤ a := min_le_left a (min h (min thirdPrefixRho (1 / 32000)))
  have hsh : small ≤ h :=
    (min_le_right a (min h (min thirdPrefixRho (1 / 32000)))).trans
      (min_le_left h (min thirdPrefixRho (1 / 32000)))
  have hsrho : small ≤ thirdPrefixRho :=
    ((min_le_right a (min h (min thirdPrefixRho (1 / 32000)))).trans
      (min_le_right h (min thirdPrefixRho (1 / 32000)))).trans
        (min_le_left thirdPrefixRho (1 / 32000))
  have hscap : small ≤ (1 / 32000 : ℝ) :=
    ((min_le_right a (min h (min thirdPrefixRho (1 / 32000)))).trans
      (min_le_right h (min thirdPrefixRho (1 / 32000)))).trans
        (min_le_right thirdPrefixRho (1 / 32000))
  let omega : ℝ := small / 2
  have homega : 0 < omega := half_pos hsmall
  have hws : omega < small := by dsimp only [omega]; linarith only [hsmall]
  have hwrho : omega < thirdPrefixRho := hws.trans_le hsrho
  have hwa : omega ≤ a := hws.le.trans hsa
  have hwh : omega ≤ h := hws.le.trans hsh
  have hwcap : omega ≤ (1 / 32000 : ℝ) := hws.le.trans hscap
  obtain ⟨N0, hN0, hRaw⟩ := hOmega omega homega hwrho hwa hwh
  exact ⟨m0, r0, n0, e, he, heMax', heSmall, a, ha, haSmall,
    q, hqpos, hqdiv, hstep, omega, homega, hwrho, hwa, hwcap, N0, hN0, hRaw⟩

/-- A genuinely fixed original-policy family: all finite choices precede
N. The complete All22 raw bound, original selected-prefix rules, actual
ancestor reads and one physical rough-indicator majorant share these
choices. The physical choice ell=16*omega corresponds to the manuscript
beta=1/16 and nu=256*omega. Compiled density errors and signed PP
remain separate. -/
theorem exists_complete_original_policy
    (eta eMax : ℝ) (heta : 0 < eta) (heMax : 0 < eMax) :
    ∃ m_bank r n : ℕ, ∃ e : ℚ, 0 < (e : ℝ) ∧ (e : ℝ) ≤ eMax ∧
      (e : ℝ) ≤ 1 / 384 ∧
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 800 ∧
    ∃ q : ℕ, 0 < q ∧ 256 ∣ q ∧
      logPrimeMeshStep 0 (19 / 96) (data e q a).m ≤ (e : ℝ) / 2 ∧
    ∃ omega ell tau : ℝ, 0 < omega ∧ omega < thirdPrefixRho ∧ omega ≤ a ∧
      0 < ell ∧ ell = 16 * omega ∧ omega ≤ ell ∧ ell < 1 / 1000 ∧ 0 < tau ∧
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      let D := data e q a
      let P := finalPolicy m_bank r n e q a omega N
      let f := F (bank m_bank) (width r) n D omega N
      let R := rho (bank m_bank) r n e q a omega N tau ((N : ℝ) ^ ell)
      normalize N (rawRoot P N) < quotedAll22Raw + eta ∧
      (∀ pre : List ℕ, P true pre = true) ∧
      (∀ (positive : Bool) (pre : List ℕ), pre.length ≤ 2 →
        P positive pre = HistoricalThirdCoarse.initialPolicy (e : ℝ) D.m
          (N : ℝ) positive pre) ∧
      (∀ (p : ℕ) (ps : List ℕ), FirstExitValidSelection P [] true (p :: ps) →
        HistoricalThirdCoarse.firstStop (e : ℝ) D.m (N : ℝ) [p]) ∧
      (∀ (w z : ℝ) (d : ℕ), fixedRoughCoefficient f N N w z d =
        (firstExitRetainedCoefficient P (roughPrimeUniverse N N w z) d : ℝ)) ∧
      (∀ x : ℤ, actualSmallRoughIndicator N (cutoff N) x ≤
          physicalDivisorSum (moduli N ((N : ℝ) ^ omega)) R x.natAbs ∧
        0 ≤ physicalDivisorSum (moduli N ((N : ℝ) ^ omega)) R x.natAbs) ∧
      (∀ d : ℕ, |R d| ≤ 1 ∧
        (R d ≠ 0 → Squarefree d ∧ d.Coprime N ∧
          (d : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ))) ∧
      (∀ p : Fin 3 → ℕ,
        p ∈ P4ACatalogFiveCoarseWeightedPayment.candidateTuples D N →
        (p 0 : ℝ) ^ 3 < (N : ℝ) ^
          P4AOriginalOrderedThirdTable.rawExponent (e : ℝ) D.m omega N (history p)) ∧
      (∀ x k : ℕ, x ∈ universe N N ((N : ℝ) ^ omega) (cutoff N) →
        k ≤ x.primeFactorsList.length → polarityAfter true k = false →
        index (position k) + 1 ≤ k ∧
          f (rosserAncestor k x.primeFactorsList) =
            admit N ((code (bank m_bank) (width r) n D (position k)).eval
              (coords N (index (position k) + 1) x.primeFactorsList.reverse))
              (rosserAncestor k x.primeFactorsList)) := by
  obtain ⟨m_bank, r, n, e, he, heMax', heSmall, a, ha, haSmall,
      q, hqpos, hqdiv, hstep, omega, homega, homegaR, hwa, hwcap, N0, hN0, hRaw⟩ :=
    exists_fixed_raw_parameters eta eMax heta heMax
  let ell : ℝ := 16 * omega
  have hell : 0 < ell := by dsimp only [ell]; positivity
  have hwell : omega ≤ ell := by dsimp only [ell]; linarith only [homega]
  have hellSmall : ell < 1 / 1000 := by dsimp only [ell]; linarith only [hwcap]
  have heRat : (0 : ℚ) ≤ e := by exact_mod_cast he.le
  obtain ⟨tau0, htau0, hSupport⟩ :=
    P1OriginalFinalPolicyStructure.exists_final_rho_support_width
      m_bank r n e heRat q a omega ell homega hellSmall
  let tau : ℝ := tau0 / 2
  have htau : 0 < tau := half_pos htau0
  have htauSmall : tau ≤ tau0 := by dsimp only [tau]; linarith only [htau0]
  obtain ⟨_hbudget, hActive⟩ := hSupport tau htau htauSmall
  refine ⟨m_bank, r, n, e, he, heMax', heSmall, a, ha, haSmall,
    q, hqpos, hqdiv, hstep, omega, ell, tau, homega, homegaR, hwa,
    hell, rfl, hwell, hellSmall, htau, N0, hN0, ?_⟩
  intro N hN hEven
  have hNtwo : 2 ≤ N := hN0.trans hN
  have hNone : 1 < N := by omega
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 1 < (N : ℝ) ^ ell :=
    Real.one_lt_rpow (by exact_mod_cast hNone : (1 : ℝ) < N) hell
  have hwL : (N : ℝ) ^ omega ≤ (N : ℝ) ^ ell :=
    Real.rpow_le_rpow_of_exponent_le hNreal hwell
  have hwz : (N : ℝ) ^ omega ≤ cutoff N :=
    Real.rpow_le_rpow_of_exponent_le hNreal (show omega ≤ (19 / 96 : ℝ) from homegaR.le)
  have hzN : cutoff N ≤ (N : ℝ) := by
    simpa only [cutoff, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNreal (show (19 / 96 : ℝ) ≤ 1 by norm_num)
  refine ⟨hRaw N hN hEven, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact P1OriginalFinalPolicyStructure.finalPolicy_even m_bank r n e q a omega N
  · intro positive pre hlen
    exact P1OriginalFinalPolicyStructure.finalPolicy_through_two
      m_bank r n e q a omega N positive pre hlen
  · intro p ps hvalid
    exact firstStop_of_valid_prefix m_bank r n e q a omega N p ps hvalid
  · intro w z d
    exact P1OriginalFinalPolicyStructure.final_raw_coefficient_identity
      m_bank r n e q a omega N w z d
  · intro x
    exact ⟨P1OriginalFinalPolicyStructure.final_rho_majorant
      m_bank r n e q a omega N tau ((N : ℝ) ^ ell) hL hwL hwz hzN x,
      P1OriginalFinalPolicyStructure.final_rho_divisorSum_nonneg
        m_bank r n e q a omega N tau ((N : ℝ) ^ ell) hL hwL hwz hzN x⟩
  · intro d
    refine ⟨P1OriginalFinalPolicyStructure.final_rho_abs_le_one
      m_bank r n e q a omega N tau ((N : ℝ) ^ ell) d, ?_⟩
    intro hd
    obtain ⟨hsq, hcop⟩ := P1OriginalFinalPolicyStructure.final_rho_support_arithmetic
      m_bank r n e q a omega N tau ((N : ℝ) ^ ell) d hd
    exact ⟨hsq, hcop, hActive N hNtwo d hd⟩
  · intro p hp
    exact P4AOriginalFiniteFallbackCandidate.first_cube
      (d := data e q a) hNone he heSmall hstep omega hp
  · intro x k hx hk ho
    exact P1OriginalFinalPolicyAncestorReads.final_rough_ancestor_read
      m_bank r n e q a omega N hNone homega.le x k hx hk ho

end
end ImbalancedChen.P1OriginalCompleteFormalProof
