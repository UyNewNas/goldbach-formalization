import ImbalancedChen.P1OriginalSingletonLogNormalization

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The two positions supplied by the original singleton remaining dictionary
are retained. At the same actual tuple, its normalized profile is nonzero.
An occurrence p is paired with the existing owner of the whole integer n/p,
not just the other long occurrence or the short product. The indexed erased
product identity retains units and repeated numerical values.

The existing physical-level theorem pays both selected complete local
scales. Its threshold is combined with the existing dictionary and profile
thresholds before all charts, tuples and historical coefficient parameters.
The original same-Q/rho fixed-mode count-minus-coprime-mean identity remains
in the conclusion. No aggregate or whole-rectangle activity is inferred.
-/

namespace ImbalancedChen.P1OriginalSingletonLongComplement
noncomputable section
open Classical Filter
open scoped BigOperators
open PrimeProducts
open P5Z.HBRightClosedDyadicRoles
  (Block Owns owner bank owner_owns owner_mem_bank actual_factor_bound)
open P5Z.LiteralHeathBrownOccurrenceWords (factorTuples factorTuples_spec)
open P5Z.ActualRoughHeathBrownWords (roles)
open P5Z.ActualHBDyadicOccurrenceFamily (assignedWeight)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ActualHBMediumBranchPartition (longBlocks)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.PerGroupIntegerHBAtlasPushforward (Row hbCutoff originalProducts typeIValue)
open P5Z.LicensedOriginalIntegerProfile (listExtension)
open P5Z.IndependentPrimeSourceWordDictionary (wordKernel)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (originalChart)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5CanonicalTentNarrowSingletonTransfer (actualLicence)
open P5Z.ActualEtaPsiOccurrenceBudget (eta)
open P5Z.OrderedFactorTupleRectangleReindex (blockVector)
open Part3.OriginalProperPowerActualChart (wordVector)
open P5Z.ActualLowerNormalizedAtlasOccurrence (rowRoles scalarProfile integerProfile)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle scales rectangle_owns)
open P5Z.ActualHBPostModulusLogCutoff (hbSlots completeProduct)
open P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode)
open P5Z.OriginalHBCompleteProductScale (localScale)
open Part3.TwoLongActualHBShortMass (ShortPositions shortSupport shortSequence)
open Part3.TwoLongRetainedRowReindex (roughFibreCore)
open P4BOriginalNoMediumPairRows (longPositions)
open P1OriginalHistoricalTwoLongP2 (historicalModuli)
open P1OriginalSingletonTwoLongDictionary (eventually_actual_remaining_tuple_dictionary)
open P1OriginalSingletonLogNormalization (eventually_actual_tuple_normalized_profile)
open P1OriginalSingletonPhysicalLevel (eventually_actual_singleton_local_level)

/-- The whole-complement owner is supplied by the genuine ordered factor
tuple. No divisibility, quotient positivity or complement block is assumed. -/
theorem actual_factor_whole_complement {r n : ℕ} {fs : List ℕ}
    (hfs : fs ∈ factorTuples r n) {p : ℕ} (hp : p ∈ fs) :
    0 < p ∧ p ∣ n ∧ 0 < n / p ∧ p * (n / p) = n ∧
      Owns (owner (n / p)) (n / p) ∧ owner (n / p) ∈ bank n := by
  obtain ⟨hp0, hpn⟩ := actual_factor_bound hfs hp
  have hspec := factorTuples_spec r n fs hfs
  have hdvd : p ∣ n := by
    simpa only [hspec.2.1] using List.dvd_prod hp
  have hc0 : 0 < n / p := Nat.div_pos hpn hp0
  exact ⟨hp0, hdvd, hc0, Nat.mul_div_cancel' hdvd,
    owner_owns hc0, owner_mem_bank hc0 (Nat.div_le_self n p)⟩

/-- The original remaining selector chooses two distinct occurrences once.
Each is joined to its entire indexed complement and the same historical
modulus carrier. The exact same-rho finite dictionary is retained for all
Fourier modes, with the original single-mother roles and coprime mean.

The threshold precedes kap, B, K, the chart, actual row, old/fresh coefficient
data and rho. All support and local-level inequalities are conclusions of
the existing suppliers at this one actual tuple. -/
theorem eventually_actual_remaining_two_long_complements
    {kappa kap0 zeta : ℝ} (hkappa : 0 < kappa)
    (hsmall : kappa ≤ zeta / 10000) (hzeta : zeta ≤ 1 / 20000)
    (htrim : kap0 < kappa / (4 * (1 + kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (B K cj : ℕ) (row : Row) (levelB : ℝ)
        (old fresh : List ℕ → Bool) (cap : ℕ) (w z : ℝ) (rho : ℕ → ℂ),
      originalChart (actualLicence kap B N) N kap0 [cj] [row.factors.prod] ≠ 0 →
      row.order ∈ Finset.range 3 →
      row.factors ∈ factorTuples (2*(row.order+1)) row.factors.prod →
      assignedWeight (beforeHBCutoff K [cj]) (hbCutoff cj)
        (roles row.order) row.blocks row.factors ≠ 0 →
      (if (longBlocks (originalMediumHigh zeta [cj])
          ([row].flatMap Row.blocks)).length = 1 then (0 : ℂ)
        else typeIValue (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj])
          (fun rows => (listExtension (actualLicence kap B N) (originalProducts rows) : ℂ) *
            (eta (((originalProducts rows).prod : ℝ) / (N : ℝ)^(1-kap0)) : ℂ) *
            wordKernel (historicalModuli levelB old fresh N cap w z) rho N
              (originalProducts rows)) [row]) ≠ 0 →
      let r := 2*(row.order+1)
      let bs := blockVector r row.blocks
      let ns := wordVector r row.factors
      List.ofFn bs = row.blocks ∧
      List.ofFn ns = row.factors ∧
      ns ∈ rectangle bs ∧
      completeProduct ns = row.factors.prod ∧
      hbSlots (beforeHBCutoff K [cj]) (fun _ => hbCutoff cj) (rowRoles row.order) ns =
        assignedWeight (beforeHBCutoff K [cj]) (hbCutoff cj)
          (roles row.order) row.blocks row.factors ∧
      scalarProfile kap B N cj kap0 row.factors.prod ≠ 0 ∧
      ∃ i k : Fin r, i ≠ k ∧
        longPositions (originalMediumHigh zeta [cj]) bs = {i,k} ∧
        (rowRoles row.order i = .one ∨ rowRoles row.order i = .logarithm) ∧
        (rowRoles row.order k = .one ∨ rowRoles row.order k = .logarithm) ∧
        Fintype.card (ShortPositions i k) + 2 = r ∧
        Fintype.card (ShortPositions i k) ≤ 4 ∧
        (∀ a : ShortPositions i k,
          (lower (bs a.val) : ℝ) < originalMediumLow zeta [cj]) ∧
        (∀ a ∈ ({i,k} : Finset (Fin r)),
          ns a ∈ row.factors ∧ Owns (bs a) (ns a) ∧
          0 < ns a ∧ ns a ∣ row.factors.prod ∧ 0 < row.factors.prod / ns a ∧
          (∏ b ∈ Finset.univ.erase a, ns b) = row.factors.prod / ns a ∧
          ns a * (row.factors.prod / ns a) = row.factors.prod ∧
          Owns (owner (row.factors.prod / ns a)) (row.factors.prod / ns a) ∧
          owner (row.factors.prod / ns a) ∈ bank row.factors.prod ∧
          (let x := localScale (bs a) (owner (row.factors.prod / ns a))
           1 < x ∧ (1 / 2 : ℝ) * x ≤ N ∧ (N : ℝ) ≤ x ^ (1 + kappa) ∧
             ∀ q ∈ historicalModuli levelB old fresh N cap w z,
               (q : ℝ) < x ^ (1199 / 2000 : ℝ) ∧
                 q ≤ ⌊x ^ (1199 / 2000 : ℝ)⌋₊)) ∧
        ∀ xi : Fin r → ℝ,
          MellinInsertion20261028.exactDiscrepancy (rectangle bs)
            (historicalModuli levelB old fresh N cap w z) rho completeProduct N
            (fun ns => hbSlots (beforeHBCutoff K [cj]) (fun _ => hbCutoff cj)
              (rowRoles row.order) ns * occurrenceMode (scales bs) ns xi) =
            ∑ m ∈ shortSupport (fun a : ShortPositions i k => bs a.val),
              shortSequence (fun a : ShortPositions i k => bs a.val)
                (beforeHBCutoff K [cj]) (fun _ => hbCutoff cj)
                (fun a => xi a.val) (fun a => rowRoles row.order a.val) m *
              ∑ q ∈ historicalModuli levelB old fresh N cap w z,
                rho q * roughFibreCore bs (beforeHBCutoff K [cj])
                  (fun _ => hbCutoff cj) xi (rowRoles row.order) i k m N q := by
  have hzeta0 : 0 < zeta := by linarith only [hkappa, hsmall]
  have hden : 0 < 4 * (1 + kappa) := by positivity
  have hratio : kappa / (4 * (1 + kappa)) < 1 := by
    apply (div_lt_iff₀ hden).2
    linarith only [hkappa]
  have hkap0 : kap0 < 1 := htrim.trans hratio
  have h400 : zeta ≤ 1 / 400 := hzeta.trans (by norm_num)
  filter_upwards
    [eventually_actual_remaining_tuple_dictionary hkap0 hzeta0 hzeta,
      eventually_actual_tuple_normalized_profile hkap0 hzeta0 hzeta,
      eventually_actual_singleton_local_level hkappa hsmall h400 htrim]
    with N hdict hnorm hlevel
  intro kap hkap B K cj row levelB old fresh cap w z rho hactive hj hfs hassigned hremaining
  let r := 2*(row.order+1)
  let bs := blockVector r row.blocks
  let ns := wordVector r row.factors
  let Q := historicalModuli levelB old fresh N cap w z
  obtain ⟨hbs, hns, hrect, hproduct, hweight, i, k, hik, hpair,
    hrolei, hrolek, hcard, hfour, hshort, hmode⟩ :=
    hdict kap B K cj row Q rho hactive hj hfs hassigned hremaining
  obtain ⟨_, _, _, hprofile, _, _, _⟩ :=
    hnorm kap hkap B K cj row.order row.factors.prod row.blocks row.factors
      Q rho hactive hfs hassigned
  have hscalar : scalarProfile kap B N cj kap0 row.factors.prod ≠ 0 := by
    simpa only [integerProfile, hproduct] using hprofile
  refine ⟨hbs, hns, hrect, hproduct, hweight, hscalar, i, k, hik, hpair,
    hrolei, hrolek, hcard, hfour, hshort, ?_, hmode⟩
  intro a _ha
  have hmem : ns a ∈ row.factors := by
    have hm : ns a ∈ List.ofFn ns := List.mem_ofFn.mpr ⟨a, rfl⟩
    simpa only [hns] using hm
  have hown : Owns (bs a) (ns a) := rectangle_owns bs hrect a
  obtain ⟨hp0, hdvd, hc0, hcancel, hc, hbank⟩ :=
    actual_factor_whole_complement hfs hmem
  have hmul : ns a * (∏ b ∈ Finset.univ.erase a, ns b) = row.factors.prod := by
    calc
      _ = completeProduct ns := Finset.mul_prod_erase Finset.univ ns (Finset.mem_univ a)
      _ = _ := hproduct
  have herase : (∏ b ∈ Finset.univ.erase a, ns b) = row.factors.prod / ns a := by
    calc
      _ = (ns a * (∏ b ∈ Finset.univ.erase a, ns b)) / ns a :=
        (Nat.mul_div_cancel_left _ hp0).symm
      _ = _ := congrArg (fun t : ℕ => t / ns a) hmul
  obtain ⟨hx, hxN, hNx, hQ⟩ :=
    hlevel kap hkap B cj row.order row.factors.prod row.factors hfs hscalar
      (ns a) (bs a) (owner (row.factors.prod / ns a)) hmem hown hc
  refine ⟨hmem, hown, hp0, hdvd, hc0, herase, hcancel, hc, hbank, hx, hxN, hNx, ?_⟩
  intro q hq
  exact hQ levelB old fresh cap w z q hq

end
end ImbalancedChen.P1OriginalSingletonLongComplement
