import ImbalancedChen.P1OriginalSingletonRemainingTypeIGeometry
import ImbalancedChen.P1OriginalSingletonTwoLongFiniteGeometry
import ImbalancedChen.P5ActualLowerNormalizedAtlasOccurrence
import ImbalancedChen.P1OriginalSingletonSameRhoFibres

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The original singleton remaining selector and a genuine nonzero ordered
HB tuple supply two distinct long positions. The carrier is the original
integer rectangle, including unit blocks and repeated occurrence values.
The final identity uses the same arbitrary Q and signed rho in both the
congruence count and its exact coprime mean. It is a fixed-mode finite
identity; Fourier reconstruction and the remaining estimates are separate.

No implication from a nonzero assigned tuple to a nonzero aggregate
blockCoefficient is used. The generic finite-geometry and same-rho
suppliers retain their original proof bytes; group_has_long becomes public.
-/
namespace ImbalancedChen.P1OriginalSingletonTwoLongDictionary
noncomputable section
open Classical Filter
open scoped BigOperators
open PrimeProducts
open P5Z.HBRightClosedDyadicRoles (Block Owns)
open P5Z.LiteralHeathBrownOccurrenceWords (factorTuples factorTuples_spec)
open P5Z.ActualRoughHeathBrownWords (Role roles roughTupleWeight)
open P5Z.ActualHBDyadicOccurrenceFamily (assignedWeight)
open P5Z.ActualHBDyadicProductWindow
  (lower assigned_nonzero_owns assigned_eq_rough_of_owns owns_product_window)
open P5Z.ActualHBMediumBranchPartition
  (Medium firstMedium firstMedium_none longBlocks rawProduct atMostTwoLong noMedium_short_or_long)
open P5Z.ActualHBMediumRoleSupports (assigned_mobius_lower_caps)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.PerGroupIntegerHBAtlasPushforward (Row hbCutoff originalProducts typeIValue)
open P5Z.LicensedOriginalIntegerProfile (listExtension)
open P5Z.IndependentPrimeSourceWordDictionary (wordKernel)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (originalChart)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5CanonicalTentNarrowSingletonTransfer (actualLicence)
open P5Z.ActualEtaPsiOccurrenceBudget (eta)
open P5Z.OrderedFactorTupleRectangleReindex
  (blockVector ofFn_blockVector owns_word_iff)
open Part3.OriginalProperPowerActualChart (wordVector ofFn_wordVector)
open P5Z.ActualLowerNormalizedAtlasOccurrence (rowRoles ofFn_rowRoles row_weight)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle scales rectangle_bounds)
open P5Z.ActualHBPostModulusLogCutoff (hbSlots completeProduct)
open P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode)
open Part3.TwoLongActualHBShortMass (ShortPositions shortSupport shortSequence)
open Part3.TwoLongRetainedRowReindex (roughFibreCore)
open P4BOriginalNoMediumPairRows
  (group_has_long longPositions long_card_eq_length short_card)
open P4BOriginalTwoLongActualDictionary (same_rho_mode_eq_fibres)
open P1OriginalSingletonRemainingTypeIGeometry
  (eventually_original_singleton_numeric_reserves singleton_remaining_predicate_iff)

/-- Actual ordered factor tuples, rather than products alone, are sent
to the rectangle. Both list roundtrips and the complete signed HB weight
are retained. This lemma needs no nonzero aggregate coefficient. -/
theorem actual_tuple_to_rectangle (z y : ℝ) (j n : ℕ)
    (bs : List Block) (fs : List ℕ)
    (hfs : fs ∈ factorTuples (2*(j+1)) n)
    (hassigned : assignedWeight z y (roles j) bs fs ≠ 0) :
    bs.length = 2*(j+1) ∧
      List.ofFn (blockVector (2*(j+1)) bs) = bs ∧
      List.ofFn (wordVector (2*(j+1)) fs) = fs ∧
      wordVector (2*(j+1)) fs ∈ rectangle (blockVector (2*(j+1)) bs) ∧
      completeProduct (wordVector (2*(j+1)) fs) = n ∧
      hbSlots z (fun _ => y) (rowRoles j) (wordVector (2*(j+1)) fs) =
        assignedWeight z y (roles j) bs fs := by
  have hspec := factorTuples_spec (2*(j+1)) n fs hfs
  have howns := assigned_nonzero_owns (roles j) bs fs hassigned
  have hlen : bs.length = 2*(j+1) := howns.length_eq.trans hspec.1
  have hrect : wordVector (2*(j+1)) fs ∈
      P5Z.OrderedFactorTupleRectangleReindex.rectangle (blockVector (2*(j+1)) bs) :=
    (P5Z.OrderedFactorTupleRectangleReindex.mem_rectangle _ _).mpr
      ((owns_word_iff hlen hspec.1).mp howns)
  have hproduct : completeProduct (wordVector (2*(j+1)) fs) = n := by
    calc
      _ = (List.ofFn (wordVector (2*(j+1)) fs)).prod := by
        simp only [completeProduct, List.prod_ofFn]
      _ = fs.prod := congrArg List.prod (ofFn_wordVector hspec.1)
      _ = n := hspec.2.1
  refine ⟨hlen, ofFn_blockVector hlen, ofFn_wordVector hspec.1,
    hrect, hproduct, ?_⟩
  calc
    _ = roughTupleWeight z y (roles j) fs := by
      rw [← row_weight z y j, ofFn_wordVector hspec.1]
    _ = _ := (assigned_eq_rough_of_owns howns (roles j)).symm

private theorem role_position_mem (j : ℕ) (bs : List Block)
    (hlen : bs.length = 2*(j+1)) (a : Fin (2*(j+1))) :
    (rowRoles j a, blockVector (2*(j+1)) bs a) ∈ (roles j).zip bs := by
  have hmem : (rowRoles j a, blockVector (2*(j+1)) bs a) ∈
      (List.ofFn (rowRoles j)).zip (List.ofFn (blockVector (2*(j+1)) bs)) := by
    apply List.mem_iff_getElem.mpr
    refine ⟨a.val, ?_, ?_⟩
    · simpa only [List.length_zip, List.length_ofFn, min_self] using a.isLt
    · simp only [List.getElem_zip, List.getElem_ofFn]
  simpa only [ofFn_rowRoles, ofFn_blockVector hlen] using hmem

/-- The real cutoff excludes the Mobius role at a long position of the
actual nonzero tuple. No arbitrary long sequence is introduced. -/
theorem actual_tuple_long_role {z y hi : ℝ} (hy : y ≤ hi)
    (j : ℕ) (bs : List Block) (fs : List ℕ)
    (hlen : bs.length = 2*(j+1))
    (hassigned : assignedWeight z y (roles j) bs fs ≠ 0)
    (a : Fin (2*(j+1)))
    (hlong : hi < (lower (blockVector (2*(j+1)) bs a) : ℝ)) :
    rowRoles j a = .one ∨ rowRoles j a = .logarithm := by
  have hnot : rowRoles j a ≠ .mobius := by
    intro hm
    have hcap := assigned_mobius_lower_caps (roles j) bs fs hassigned
      (rowRoles j a, blockVector (2*(j+1)) bs a) (role_position_mem j bs hlen a) hm
    exact (not_lt_of_ge (hcap.trans hy)) hlong
  cases hrole : rowRoles j a with
  | mobius => exact False.elim (hnot hrole)
  | one => exact Or.inl rfl
  | logarithm => exact Or.inr rfl

/-- From the literal nonzero remaining source row to the same-Q/rho
two-long dictionary. The eventual physical-N threshold precedes every
profile parameter, HB order, chart, row, modulus carrier and coefficient.
The source test in the premise is the unchanged body of the historical
sourceTest, and the selector is the unchanged remainingTypeIValue body.

The two positions are chosen before xi. Their short complement has at
most four occurrences, still including units and repeated numerical values.
The full rectangle and the original one-mother rowRoles are unchanged. -/
theorem eventually_actual_remaining_tuple_dictionary
    {kap0 zeta : ℝ} (hkap0 : kap0 < 1)
    (hzeta : 0 < zeta) (hsmall : zeta ≤ 1 / 20000) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ) (B K cj : ℕ) (row : Row)
      (Q : Finset ℕ) (rho : ℕ → ℂ),
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
            wordKernel Q rho N (originalProducts rows)) [row]) ≠ 0 →
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
      ∃ i k : Fin r, i ≠ k ∧
        longPositions (originalMediumHigh zeta [cj]) bs = {i,k} ∧
        (rowRoles row.order i = .one ∨ rowRoles row.order i = .logarithm) ∧
        (rowRoles row.order k = .one ∨ rowRoles row.order k = .logarithm) ∧
        Fintype.card (ShortPositions i k) + 2 = r ∧
        Fintype.card (ShortPositions i k) ≤ 4 ∧
        (∀ a : ShortPositions i k,
          (lower (bs a.val) : ℝ) < originalMediumLow zeta [cj]) ∧
        ∀ xi : Fin r → ℝ,
          MellinInsertion20261028.exactDiscrepancy (rectangle bs) Q rho completeProduct N
            (fun ns => hbSlots (beforeHBCutoff K [cj]) (fun _ => hbCutoff cj)
              (rowRoles row.order) ns * occurrenceMode (scales bs) ns xi) =
            ∑ m ∈ shortSupport (fun a : ShortPositions i k => bs a.val),
              shortSequence (fun a : ShortPositions i k => bs a.val)
                (beforeHBCutoff K [cj]) (fun _ => hbCutoff cj)
                (fun a => xi a.val) (fun a => rowRoles row.order a.val) m *
              ∑ q ∈ Q, rho q * roughFibreCore bs (beforeHBCutoff K [cj])
                (fun _ => hbCutoff cj) xi (rowRoles row.order) i k m N q := by
  filter_upwards [eventually_original_singleton_numeric_reserves hkap0 hzeta hsmall]
    with N hnumeric
  intro kap B K cj row Q rho hactive hj hfs hassigned hremaining
  let r := 2*(row.order+1)
  let bs := blockVector r row.blocks
  let ns := wordVector r row.factors
  let lo := originalMediumLow zeta [cj]
  let hi := originalMediumHigh zeta [cj]
  let F : List Row → ℂ := fun rows =>
    (listExtension (actualLicence kap B N) (originalProducts rows) : ℂ) *
      (eta (((originalProducts rows).prod : ℝ) / (N : ℝ)^(1-kap0)) : ℂ) *
      wordKernel Q rho N (originalProducts rows)
  obtain ⟨hnotOne, hbranch, _⟩ :=
    (singleton_remaining_predicate_iff lo hi F row).mp hremaining
  obtain ⟨hlo, hhi, hlarge, hcomplete, hcut⟩ :=
    hnumeric kap B cj row.factors.prod hactive
  obtain ⟨hlen, hbs, hns, hrect, hproduct, hweight⟩ :=
    actual_tuple_to_rectangle (beforeHBCutoff K [cj]) (hbCutoff cj)
      row.order row.factors.prod row.blocks row.factors hfs hassigned
  have hr : r ≤ 6 := by
    have hj' := Finset.mem_range.mp hj
    dsimp only [r]
    omega
  have hmem (a : Fin r) : bs a ∈ row.blocks := by
    have hm : bs a ∈ List.ofFn bs := List.mem_ofFn.mpr ⟨a,rfl⟩
    simpa only [hbs] using hm
  have hnone (a : Fin r) : ¬ Medium lo hi (bs a) :=
    firstMedium_none.mp hbranch _ (hmem a)
  have hex : ∃ a : Fin r, hi < (lower (bs a) : ℝ) :=
    group_has_long hr hlo bs ns
      (fun a => (rectangle_bounds bs hrect a).2.2) hnone
      (by simpa only [hproduct] using hlarge)
  have hpositive : 0 < (longPositions hi bs).card := by
    obtain ⟨a,ha⟩ := hex
    exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
  have hraw : rawProduct row.blocks ≤ (row.factors.prod : ℝ) := by
    have hp := (owns_product_window
      (assigned_nonzero_owns (roles row.order) row.blocks row.factors hassigned)).1
    unfold rawProduct
    exact_mod_cast hp
  have htwo : (longPositions hi bs).card ≤ 2 := by
    rw [long_card_eq_length, hbs]
    exact atMostTwoLong hhi (hraw.trans_lt hcomplete)
  have hcard : (longPositions hi bs).card = 2 := by
    have hne : (longPositions hi bs).card ≠ 1 := by
      simpa only [long_card_eq_length, hbs] using hnotOne
    omega
  obtain ⟨i,k,hik,hpair⟩ := Finset.card_eq_two.mp hcard
  have hilong : hi < (lower (bs i) : ℝ) := by
    have hm : i ∈ longPositions hi bs := by rw [hpair]; simp
    exact (Finset.mem_filter.mp hm).2
  have hklong : hi < (lower (bs k) : ℝ) := by
    have hm : k ∈ longPositions hi bs := by rw [hpair]; simp
    exact (Finset.mem_filter.mp hm).2
  have hrole (a : Fin r) (ha : hi < (lower (bs a) : ℝ)) :
      rowRoles row.order a = .one ∨ rowRoles row.order a = .logarithm :=
    actual_tuple_long_role hcut row.order row.blocks row.factors hlen hassigned a ha
  have hshort (a : ShortPositions i k) : (lower (bs a.val) : ℝ) < lo := by
    have hnlong : ¬ hi < (lower (bs a.val) : ℝ) := by
      intro ha
      have hm : a.val ∈ longPositions hi bs :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
      rw [hpair] at hm
      have hor : a.val = i ∨ a.val = k := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
      exact hor.elim a.property.1 a.property.2
    exact (noMedium_short_or_long hbranch (hmem a.val)).resolve_right hnlong
  have hshortCard := short_card i k hik
  have hfour : Fintype.card (ShortPositions i k) ≤ 4 := by omega
  refine ⟨hbs, hns, hrect, hproduct, hweight, i, k, hik, hpair,
    hrole i hilong, hrole k hklong, hshortCard, hfour, hshort, ?_⟩
  intro xi
  exact same_rho_mode_eq_fibres bs (beforeHBCutoff K [cj])
    (fun _ => hbCutoff cj) xi (rowRoles row.order) i k hik N Q rho

end
end ImbalancedChen.P1OriginalSingletonTwoLongDictionary
