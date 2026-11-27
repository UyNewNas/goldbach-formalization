import ImbalancedChen.P3OriginalU5CommonPhysicalRoot
import ImbalancedChen.P3OriginalU5RoundedModulusCap

/-! Level and rank of retained rough histories at the physical cell seed
on the full original marked pair support. -/

namespace ImbalancedChen.P3OriginalU5PhysicalRawRank

noncomputable section
open scoped Classical List
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver P2OriginalPairRootRoughProducer
open P2OriginalSelectedPairNativeData (original_root_seed_bounded)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalLowerCompactStartCapConstructor (topCap)
open P2OriginalSelectedIntegerPrefixSquares (coordinate_list_power)
open P2ActualPairPlanRawSupport (PlanCeiling accepted_run_sum_le)
open P2LowerCanonicalRetainedTrace (actual_chosen_eq_canonical)
open P3OriginalU5CommonPhysicalRoot (rowOwner rowOwner_seed_bounds physicalSeed policy)
open P3OriginalU5RoundedModulusCap (rawRank)
open P5OriginalU5CausalFinite (cutoff coordinates coordinates_mem_triangle pairSupport smallCutoff attachmentNu)
open P5OriginalU5PlateauPrimeBV (fullModulus markedProduct)

/-- The physical seed and every fresh cap have the common ceiling.
The original pair coordinates carry the first odd bypass at every mesh. -/
theorem accepted_physical_word_le_topCap
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (buffer : ℚ)
    (hb : 0 ≤ buffer) (m : ℕ) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) (enum : ℕ) (w : ℝ) {chosen : List ℕ}
    (hsub : chosen <+ roughPrimeUniverse N enum w (cutoff N))
    (haccept :
      let seed := physicalSeed R buffer (rowOwner R m hN ht)
      (run (pairPlan R bank (2 * buffer) seed) (R.epsilon : ℝ) (ceiling : ℝ)
        (pairRoot N t seed) (chosen.map (coordinate N))).accepted = true) :
    (fullModulus t chosen.prod : ℝ) ≤ (N : ℝ) ^ topCap := by
  let seed := physicalSeed R buffer (rowOwner R m hN ht)
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hseed : seed ≤ topCap :=
    (rowOwner_seed_bounds R m buffer hN ht).1.trans (original_root_seed_bounded false buffer hb N t)
  have hplan : PlanCeiling (pairPlan R bank (2 * buffer) seed) topCap := by
    intro rank code incoming hi
    exact pairPlan_fresh_cap_bound R bank (2 * buffer) seed rank code incoming hi
  obtain ⟨_, horder, hlarge⟩ :=
    Part5OriginalUpsilon5CausalDictionary.mem_triangle.mp (coordinates_mem_triangle hN ht)
  change coordinate N t.1 < coordinate N t.2 at horder
  change coordinate N t.2 < 19 / 125 at hlarge
  have hrootTop : (pairRoot N t seed).word.sum + 2 * (417 / 5000 : ℝ) ≤ topCap := by
    simp only [pairRoot, List.sum_cons, List.sum_nil, add_zero, topCap]
    linarith only [horder, hlarge]
  have hprime : ∀ q ∈ chosen, q.Prime :=
    fun q hq => mem_roughPrimeUniverse_prime (hsub.subset hq)
  have hnonneg : ∀ x ∈ chosen.map (coordinate N), 0 ≤ x := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    change 0 ≤ Real.log (q : ℝ) / Real.log (N : ℝ)
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast (hprime q hq).one_lt.le))
      (Real.log_pos hNr).le
  have hupper : ∀ x ∈ chosen.map (coordinate N), x ≤ (417 / 5000 : ℝ) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    apply (Real.rpow_le_rpow_left_iff hNr).mp
    rw [coordinate_power hNr (hprime q hq).pos]
    exact (mem_roughPrimeUniverse_upper (hsub.subset hq)).le
  have hsort : (chosen.map (coordinate N)).Pairwise (· ≥ ·) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hi' : i < chosen.length := by simpa only [List.length_map] using hi
    have hj' : j < chosen.length := by simpa only [List.length_map] using hj
    have hqsort := (roughPrimeUniverse_pairwise_gt N enum w (cutoff N)).sublist hsub
    have hge := ((List.pairwise_iff_getElem.mp hqsort) i j hi' hj' hij).le
    have hm : coordinate N chosen[j] ≤ coordinate N chosen[i] := by
      apply (Real.rpow_le_rpow_left_iff hNr).mp
      rw [coordinate_power hNr (hprime chosen[j] (List.getElem_mem hj')).pos,
        coordinate_power hNr (hprime chosen[i] (List.getElem_mem hi')).pos]
      exact_mod_cast hge
    simpa only [List.getElem_map] using hm
  have hfinal := accepted_run_sum_le
    (pairPlan R bank (2 * buffer) seed) topCap hplan
    (R.epsilon : ℝ) (ceiling : ℝ) (chosen.map (coordinate N))
    (pairRoot N t seed) (417 / 5000 : ℝ)
    (by simp [pairRoot]) hseed (by linarith [hrootTop])
    (fun _ => hrootTop) (fun _ => hupper) hsort hnonneg haccept
  have hsum : (pairRoot N t seed).word.sum +
      (chosen.map (coordinate N)).sum ≤ topCap := by
    simpa only [run_word, List.sum_append] using hfinal
  obtain ⟨hc, _hA, _horder, _hH⟩ := Finset.mem_filter.mp ht
  obtain ⟨ht1, ht2⟩ := Finset.mem_product.mp hc
  have h1pos := (mem_chenAdditivePrimeCarrier.mp ht1).2.1.pos
  have h2pos := (mem_chenAdditivePrimeCarrier.mp ht2).2.1.pos
  have hpower := coordinate_list_power hNr (t.2 :: t.1 :: chosen) (by
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · exact h2pos
    · exact h1pos
    · exact (hprime q hq).pos)
  have hpower' :
      (N : ℝ) ^ ((pairRoot N t seed).word.sum +
        (chosen.map (coordinate N)).sum) = (fullModulus t chosen.prod : ℝ) := by
    simpa [pairRoot, fullModulus, markedProduct, List.map_cons, List.sum_cons,
      List.prod_cons, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc]
      using hpower
  rw [← hpower']
  exact Real.rpow_le_rpow_of_exponent_le hNr.le hsum

/-- One bound works for the raw support of every physical owner and every
ordered external pair, including the empty retained rough history. -/
theorem physical_raw_level_and_rank
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (buffer : ℚ)
    (hb : 0 ≤ buffer) (m : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (enum : ℕ) {r : ℕ}
    (hr : r ∈ P2LowerFiniteCellRounding.rawSupport
      (policy R bank buffer m N t) N enum (smallCutoff N epsilon) (cutoff N)) :
    (fullModulus t r : ℝ) ≤ (N : ℝ) ^ topCap ∧
      r.primeFactorsList.length ≤ rawRank epsilon := by
  let seed := physicalSeed R buffer (rowOwner R m hN ht)
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans hNr
  have homega : 0 < attachmentNu * epsilon ^ 2 := by
    dsimp [attachmentNu]
    positivity
  have hpolicy : policy R bank buffer m N t =
      pairPolicy (pairPlan R bank (2 * buffer) seed) (R.epsilon : ℝ) (ceiling : ℝ) seed N t := by
    simp only [policy, dif_pos (coordinates_mem_triangle hN ht)]
    rfl
  have hraw : r ∈ P2LowerFiniteCellRounding.rawSupport
      (pairPolicy (pairPlan R bank (2 * buffer) seed) (R.epsilon : ℝ) (ceiling : ℝ) seed N t)
      N enum (smallCutoff N epsilon) (cutoff N) := by
    exact hpolicy ▸ hr
  obtain ⟨chosen, hsub, haccept, hprod⟩ :=
    (pair_policy_support_iff (pairPlan R bank (2 * buffer) seed)
      (R.epsilon : ℝ) (ceiling : ℝ) seed N enum t (smallCutoff N epsilon) (cutoff N) r).mp hraw
  have hphysical : (fullModulus t r : ℝ) ≤ (N : ℝ) ^ topCap := by
    simpa only [hprod] using accepted_physical_word_le_topCap
      R bank buffer hb m hN ht enum (smallCutoff N epsilon) hsub haccept
  refine ⟨hphysical, ?_⟩
  obtain ⟨hcarrier, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨ht1, ht2⟩ := Finset.mem_product.mp hcarrier
  have hp1 := (mem_chenAdditivePrimeCarrier.mp ht1).2.1
  have hp2 := (mem_chenAdditivePrimeCarrier.mp ht2).2.1
  have hmark : (1 : ℝ) ≤ (markedProduct t : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp1.ne_zero hp2.ne_zero))
  have hrbound : (r : ℝ) ≤ (N : ℝ) ^ topCap := by
    apply le_trans ?_ hphysical
    change (r : ℝ) ≤ ((markedProduct t * r : ℕ) : ℝ)
    rw [Nat.cast_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hmark (Nat.cast_nonneg r)
  have hlow := List.prod_map_le_prod_map₀
    (fun _ : ℕ => (N : ℝ) ^ (attachmentNu * epsilon ^ 2))
    (fun p : ℕ => (p : ℝ))
    (fun _ _ => Real.rpow_nonneg hNpos.le _)
    (fun p hp => mem_roughPrimeUniverse_lower (hsub.subset hp))
  have hpow : (N : ℝ) ^ ((attachmentNu * epsilon ^ 2) * (chosen.length : ℝ)) ≤
      (N : ℝ) ^ topCap := by
    rw [Real.rpow_mul hNpos.le, Real.rpow_natCast]
    apply le_trans ?_ hrbound
    simpa only [List.map_const', List.prod_replicate, actualNatList_cast_prod, hprod] using hlow
  have hlength : (chosen.length : ℝ) ≤ topCap / (attachmentNu * epsilon ^ 2) :=
    (le_div_iff₀ homega).mpr (by
      simpa only [mul_comm] using (Real.rpow_le_rpow_left_iff hNr).mp hpow)
  have hcanonical := actual_chosen_eq_canonical N enum
    (smallCutoff N epsilon) (cutoff N) chosen hsub hprod
  rw [hcanonical, List.length_reverse] at hlength
  exact_mod_cast hlength.trans (Nat.le_ceil (topCap / (attachmentNu * epsilon ^ 2)))

end
end ImbalancedChen.P3OriginalU5PhysicalRawRank
