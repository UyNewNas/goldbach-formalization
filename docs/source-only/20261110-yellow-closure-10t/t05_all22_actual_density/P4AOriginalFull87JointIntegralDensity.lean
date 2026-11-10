import ImbalancedChen.P4AOriginalFull87JointPhysicalBudget
import ImbalancedChen.P4AOriginalFull87ArchivedIntegralRows

/-! The ordinary comparison to the complete original 87 source integrals
is made before projecting or attaching the compiler. The original archive
and all 87 cells use one e,q,a. The actual final density and count use the
same licensed coefficient. -/

namespace ImbalancedChen.P4AOriginalFull87JointIntegralDensity

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P4AOriginalFull87RawChronology
open P4AOriginalFull87CompiledCounting (moduli coefficient)
open P4AOriginalFull87JointPhysicalBudget (parameters upper cutoff_le_target exists_joint_physical_budget)
open P4AOriginalFull87SlotTwoFive (sourceBound)
open P4AFull87CompilerChangedPartition (Parameters pendingMass)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)
open P4AOriginalFull87ArchivedIntegralRows
  (Paid paidCell paidCell_injective archived paid_cell_le_integral paid_archive_sum paidNumerical)
open P5OriginalCommonPositivePresieve (normalize normalize_add normalize_sub)
open P5OriginalCommonRefinedConstructor (old3)
open P5OriginalCommonFourthSourceLedger (originalFourthIntegral)
open P4AAll22OriginalKLedger20261024zSourceOnly (compilerReserve finalFourGains)
open OriginalThirdFiniteReserveSourceOnly (originalDensityReserve)

def beforeEighth (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) : ℝ :=
  let d := archiveData e q a
  normalize N (rawRoot (old3 d (N : ℝ)) N) + normalize N (thirdIncrement e q a N) -
    originalFourthIntegral d - currentUpperEighteenGains 1 - currentUpperEighteenGains 4 +
    normalize N (fifthAdjustment n e q a N + sixthIncrement n e q a N)

def sourceIntegralUpper (P : Parameters) (eta B omega tau : ℝ)
    (history : ℕ → List Bool) (N : ℕ) : ℝ :=
  (beforeEighth P.n P.e P.q P.om N - (∑ c : Cell, cellIntegral c) + eta +
      compilerReserve / 2 + B / omega * pendingMass P N N history omega (19 / 96) tau) *
    (singularSeries N / Real.log (N : ℝ)) -
    p4aActualPresieveCorrection (P.keep N) N N ((N : ℝ) ^ omega) (cutoff N)

/-- The disjoint complement of the 14 ascending, 15 descending and 13
third-minorant cells whose actual archived floors are used below. -/
def otherCells : Finset Cell := Finset.univ \ Finset.univ.image paidCell

/-- The exact slots 16, 17 and 19 use the selected replacement value on
their own 42 cells. The other original cells retain their full integrals. -/
theorem archive_floor_and_other_cells_le_full_integral :
    (currentUpperEighteenGains 15 + currentUpperEighteenGains 16 + finalFourGains 0) +
        (∑ c ∈ otherCells, cellIntegral c) ≤ ∑ c : Cell, cellIntegral c := by
  classical
  let A : Finset Cell := Finset.univ.image paidCell
  have hpaid := Finset.sum_le_sum (s := Finset.univ) (fun i _ => paid_cell_le_integral i)
  have hnum : (∑ i : Paid, (archived (paidCell i) : ℝ)) = (paidNumerical : ℝ) := by
    exact_mod_cast paid_archive_sum
  have hslots : (paidNumerical : ℝ) =
      currentUpperEighteenGains 15 + currentUpperEighteenGains 16 + finalFourGains 0 := by
    norm_num [paidNumerical, currentUpperEighteenGains, finalFourGains]
  have himage : (∑ c ∈ A, cellIntegral c) = ∑ i : Paid, cellIntegral (paidCell i) :=
    Finset.sum_image (fun i _ j _ hij => paidCell_injective hij)
  have hsplit : (∑ c ∈ otherCells, cellIntegral c) + (∑ c ∈ A, cellIntegral c) =
      ∑ c : Cell, cellIntegral c := Finset.sum_sdiff (Finset.subset_univ A)
  rw [hnum, hslots, ← himage] at hpaid
  linarith only [hpaid, hsplit]

def sourceArchiveUpper (P : Parameters) (eta B omega tau : ℝ)
    (history : ℕ → List Bool) (N : ℕ) : ℝ :=
  (beforeEighth P.n P.e P.q P.om N -
      (currentUpperEighteenGains 15 + currentUpperEighteenGains 16 + finalFourGains 0) -
      (∑ c ∈ otherCells, cellIntegral c) + eta +
      compilerReserve / 2 + B / omega * pendingMass P N N history omega (19 / 96) tau) *
    (singularSeries N / Real.log (N : ℝ)) -
    p4aActualPresieveCorrection (P.keep N) N N ((N : ℝ) ^ omega) (cutoff N)

theorem sourceIntegralUpper_le_sourceArchiveUpper (P : Parameters) (eta B omega tau : ℝ)
    (history : ℕ → List Bool) (N : ℕ) (hN : 2 ≤ N) :
    sourceIntegralUpper P eta B omega tau history N ≤
      sourceArchiveUpper P eta B omega tau history N := by
  unfold sourceIntegralUpper sourceArchiveUpper
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_right _ (densityScale_pos hN).le
  linarith only [archive_floor_and_other_cells_le_full_integral]

private theorem replace_eighth (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) (hN : 2 ≤ N)
    (eta B omega tau : ℝ) (history : ℕ → List Bool)
    (h : (∑ c : Cell, cellIntegral c) - eta / 2 <
      normalize N (rawRoot (P4AOriginalFull87LicensedSixthPolicy.sixthPolicy n e q a (N : ℝ)) N -
        rawRoot (licensed (width r) n e q a (N : ℝ)) N)) :
    let P := parameters (width r) n e q a
    upper P (eta / 2) B omega tau history N ≤ sourceIntegralUpper P eta B omega tau history N := by
  have hd := congrArg (normalize N) (licensed_raw_sub_sixth (width r) n e q a N)
  rw [normalize_sub] at h hd
  have heighth : normalize N (eighthIncrement (width r) n e q a N) <
      -(∑ c : Cell, cellIntegral c) + eta / 2 := by linarith only [h, hd]
  have hsource : sourceBound (width r) n e q a N + eta / 2 <
      beforeEighth n e q a N - (∑ c : Cell, cellIntegral c) + eta := by
    unfold sourceBound beforeEighth
    simp only [normalize_add]
    linarith only [heighth]
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_right _ (densityScale_pos hN).le
  exact add_le_add_right (add_le_add_right hsource.le _) _

/-- The original 87-cell ordinary gain and the archive/mean payment
each use eta/2. The beta and finite-cap compiler account remains the
separate original u_c. All historical, coarse and fine choices precede
the targets. The explicit endpoint still includes the other unpaid
terms of the original upper construction. -/
theorem exists_physical_density_and_count_with_full87_integral :
    ∃ B : ℝ, 0 < B ∧ ∀ eta eMax : ℝ, 0 < eta → 0 < eMax →
    ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    ∃ a0 : ℝ, 0 < a0 ∧ a0 ≤ 1 / 800 ∧ a0 < (19 / 96 : ℝ) ∧
      ∀ a : ℝ, 0 < a → a ≤ a0 →
      ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ eMax ∧ e0 ≤ 3 / 51200 ∧
      ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < e0 →
      ∀ qMin mMin : ℕ, ∃ q0 : ℕ, 0 < q0 ∧ qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
        let d := archiveData e q a
        let P := parameters (width r) n e q a
        mMin ≤ d.m ∧
        (P4ASameRhoCompact.originalOrdinaryRoot + actualExtendedThirdFiniteFunctional (e : ℝ) d.m ≤
          (∑ i, currentUpperEighteenPositive i) + originalDensityReserve / 4) ∧
        ∀ nu betaMax : ℝ, 0 < nu → 0 < betaMax →
        ∃ beta : ℝ, 0 < beta ∧ beta < 1 / 8 ∧ beta < betaMax ∧
          nu * beta ^ 2 < (19 / 96 : ℝ) ∧ nu * beta < 1 / 1000 ∧
        ∃ tau0 : ℝ, 0 < tau0 ∧ ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
          let omega := nu * beta ^ 2
          (∀ᶠ N : ℕ in atTop, Even N → ∀ history : ℕ → List Bool,
            let w := (N : ℝ) ^ omega
            let L := (N : ℝ) ^ (nu * beta)
            physicalDensitySum (moduli N w)
              (coefficient (width r) n e q a history N w tau L) <
                sourceIntegralUpper P eta B omega tau history N ∧
            sourceIntegralUpper P eta B omega tau history N ≤
                sourceArchiveUpper P eta B omega tau history N) ∧
          ∀ b kappa : ℝ, 0 < b → b < 1 →
            (19 / 96 : ℝ) < (1 - kappa) * (b / (1 + b)) →
            ∀ᶠ N : ℕ in atTop, Even N → ∀ history : ℕ → List Bool,
              let w := (N : ℝ) ^ omega
              let L := (N : ℝ) ^ (nu * beta)
              let T := manuscriptHalfProductCutoff kappa N
              (RealB b N : ℝ) ≤ ((realHalfProductSource b N T).card : ℝ) *
                sourceArchiveUpper P eta B omega tau history N +
                realPhysicalDistributionError b N T (moduli N w)
                  (coefficient (width r) n e q a history N w tau L) +
                (Nat.ceil (cutoff N) : ℝ) + (T + 1) := by
  obtain ⟨B, hB, hbudget⟩ := exists_joint_physical_budget
  refine ⟨B, hB, ?_⟩
  intro eta eMax heta heMax
  have hhalf := half_pos heta
  obtain ⟨r0, hr0⟩ :=
    P4AOriginalFull87ActualGain.exists_ordinary_source_gain (eta / 2) hhalf
  obtain ⟨a0, ha0, ha0max, ha0rho, hA⟩ := hbudget (eta / 2) eMax hhalf heMax
  refine ⟨r0, ?_⟩
  intro r hr
  obtain ⟨n0, hn0⟩ := hr0 r hr
  refine ⟨n0, ?_⟩
  intro n hn
  obtain ⟨eg, heg, hgainE⟩ := hn0 n hn
  refine ⟨a0, ha0, ha0max, ha0rho, ?_⟩
  intro a ha haa0
  obtain ⟨ep, hep, heMax', heBound, hE⟩ := hA a ha haa0
  refine ⟨min ep eg, lt_min hep heg, (min_le_left _ _).trans heMax',
    (min_le_left _ _).trans heBound, ?_⟩
  intro e he hee qMin mMin
  have heQ : 0 < e := by exact_mod_cast he
  obtain ⟨qg, _, hgainQ⟩ := hgainE e heQ (hee.trans_le (min_le_right _ _))
  obtain ⟨q0, hq0, hqEarlier, hQ⟩ :=
    hE e he (hee.trans_le (min_le_left _ _)) (max qMin qg) mMin
  refine ⟨q0, hq0, (le_max_left _ _).trans hqEarlier, ?_⟩
  intro q hq
  have hqg := ((le_max_right _ _).trans hqEarlier).trans hq
  obtain ⟨Ng, hNg, hGain⟩ := hgainQ q hqg a
    (haa0.trans (ha0max.trans (by norm_num : (1 / 800 : ℝ) ≤ 1 / 100)))
  obtain ⟨hm, hpos, hPhysical⟩ := hQ q hq
  refine ⟨hm, hpos, ?_⟩
  intro nu betaMax hnu hmax
  obtain ⟨beta, hb, hb8, hbm, hcut, hell, tau0, htau0, hGood⟩ :=
    hPhysical (width r) (width_pos r) n nu betaMax hnu hmax
  refine ⟨beta, hb, hb8, hbm, hcut, hell, tau0, htau0, ?_⟩
  intro tau htau ht
  let omega := nu * beta ^ 2
  let P := parameters (width r) n e q a
  obtain ⟨hD, hC⟩ := hGood tau htau ht
  have hsource : ∀ᶠ N : ℕ in atTop, Even N → ∀ history : ℕ → List Bool,
      upper P (eta / 2) B omega tau history N ≤ sourceIntegralUpper P eta B omega tau history N := by
    filter_upwards [eventually_ge_atTop Ng] with N hN
    intro hEven history
    have hN2 := hNg.trans hN
    have hNR : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hz : (N : ℝ) ^ VariableEnvelope.mu ≤ cutoff N :=
      Real.rpow_le_rpow_of_exponent_le hNR (by norm_num [VariableEnvelope.mu])
    exact replace_eighth r n e q a N hN2 eta B omega tau history
      (hGain N hN hEven N (cutoff N) hz (cutoff_le_target N hNR))
  constructor
  · filter_upwards [hD, hsource, eventually_ge_atTop (2 : ℕ)] with N hD' hS hN
    intro hEven history
    exact ⟨(hD' hEven history).trans_le (hS hEven history),
      sourceIntegralUpper_le_sourceArchiveUpper P eta B omega tau history N hN⟩
  · intro b kappa hbpos hb1 hgap
    filter_upwards [hC b kappa hbpos hb1 hgap, hsource, eventually_ge_atTop (2 : ℕ)]
      with N hC' hS hN
    intro hEven history
    have hm' := mul_le_mul_of_nonneg_left ((hS hEven history).trans
      (sourceIntegralUpper_le_sourceArchiveUpper P eta B omega tau history N hN))
      (Nat.cast_nonneg (realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card)
    exact (hC' hEven history).trans (add_le_add_right (add_le_add_right (add_le_add_right hm' _) _) _)

end
end ImbalancedChen.P4AOriginalFull87JointIntegralDensity
