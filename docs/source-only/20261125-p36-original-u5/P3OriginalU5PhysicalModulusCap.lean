import ImbalancedChen.P2ActualPairPlanRawSupport
import ImbalancedChen.P2OriginalPairBufferedRootProvenance
import ImbalancedChen.P5OriginalU5PlateauPrimeBV

/-!
# Physical modulus cap for the actual original U5 selected receiver

Candidate source. Elaboration and kernel verification are pending.

The receiver is exactly `selectedPolicy R bank buffer false N t`: its
stored pair seed is the original U5 level minus TWO buffers and its
checked continuation plan is `pairPlan R bank (2 * buffer) seed`.
The original pair selector supplies the first rough head reserve. The
existing accepted-run induction and the checked plan ceiling then bound
the complete external-pair/rough product at 153/256, at every rough rank.

For the SAME nonzero native rho, the existing signed small/rough
factorization supplies an active small factor s < L. Its literal small
Rosser level L = N^(attachmentNu * epsilon) is paid by the allocation
attachmentNu * epsilon <= buffer. Thus the COMPLETE physical modulus is
strictly below N^(153/256 + buffer), uniformly below N^(599/1000) when
buffer <= 1/1000. The integer pushforward corollary uses the pre-existing
original-fibre identity, and does not construct a replacement rho.

No arbitrary-policy support bound, selected-complement square licence,
global source-bank adoption, signed PP estimate, or final PP closure is
asserted here. The only upstream change required by this file is making
the existing `P2ActualPairPlanRawSupport.accepted_run_sum_le` public; its
proof is reused unchanged.
-/

namespace ImbalancedChen.P3OriginalU5PhysicalModulusCap

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver P2OriginalPairRootRoughProducer
open P2OriginalSelectedPairNativeData P2OriginalPairBufferedRootProvenance
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalLowerCompactStartCapConstructor (topCap)
open P2OriginalSelectedIntegerPrefixSquares (coordinate_list_power)
open P2ActualPairPlanRawSupport (PlanCeiling accepted_run_sum_le)
open P5OriginalU5CausalFinite
open P5OriginalU5PlateauPrimeBV
  (fullModulus markedProduct moduli integerRho rowInteger integerRho_at_original)

/-- The numerical margin is positive even after the entire allowed
small-factor buffer has been spent. -/
theorem physical_cap_margin :
    topCap + (1 / 1000 : ℝ) = (19157 / 32000 : ℝ) ∧
      (599 / 1000 : ℝ) - (topCap + 1 / 1000) = (11 / 32000 : ℝ) := by
  norm_num [topCap]

theorem buffered_cap_lt_theta (buffer : ℚ) (hb : buffer ≤ 1 / 1000) :
    topCap + (buffer : ℝ) < (599 / 1000 : ℝ) := by
  have hbR : (buffer : ℝ) ≤ 1 / 1000 := by exact_mod_cast hb
  norm_num [topCap] at *
  linarith

/-- An accepted ACTUAL U5 rough word has a bound on the complete marked
pair times that word. Its cap and root reserve are derived from the
literal selected receiver and original pair selector; neither is supplied
as a final-modulus hypothesis. -/
theorem selected_U5_accepted_word_le_topCap
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hbuffer : 0 ≤ buffer) (hb : buffer ≤ 1 / 1000)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (enum : ℕ) (w : ℝ) {chosen : List ℕ}
    (hsub : chosen <+ roughPrimeUniverse N enum w (cutoff N))
    (haccept :
      (run (pairPlan R bank (2 * buffer) (rootSeed false buffer N t))
        (R.epsilon : ℝ) (ceiling : ℝ)
        (pairRoot N t (rootSeed false buffer N t))
        (chosen.map (coordinate N))).accepted = true) :
    (fullModulus t chosen.prod : ℝ) ≤ (N : ℝ) ^ topCap := by
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hseed : rootSeed false buffer N t ≤ topCap :=
    original_root_seed_bounded false buffer hbuffer N t
  have hplan : PlanCeiling
      (pairPlan R bank (2 * buffer) (rootSeed false buffer N t)) topCap := by
    intro rank code incoming hi
    exact pairPlan_fresh_cap_bound R bank (2 * buffer)
      (rootSeed false buffer N t) rank code incoming hi
  have hcoordinates : coordinates N t = pairPoint N t := by
    funext i
    fin_cases i <;> rfl
  have hpoint : pairPoint N t ∈ Part5OriginalUpsilon5CausalDictionary.triangle := by
    rw [← hcoordinates]
    exact coordinates_mem_triangle hN ht
  have hsquares := fifth_buffered_root_squares hpoint buffer hb
  have hroot :
      (pairRoot N t (rootSeed false buffer N t)).word.sum +
        2 * (417 / 5000 : ℝ) < rootSeed false buffer N t := by
    simpa [pairRoot, pairPoint, rootSeed, rootLevel] using hsquares.2.2
  have hrootTop := hroot.le.trans hseed
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
    (pairPlan R bank (2 * buffer) (rootSeed false buffer N t)) topCap hplan
    (R.epsilon : ℝ) (ceiling : ℝ) (chosen.map (coordinate N))
    (pairRoot N t (rootSeed false buffer N t)) (417 / 5000 : ℝ)
    (by simp [pairRoot]) hseed (by linarith [hrootTop])
    (fun _ => hrootTop) (fun _ => hupper) hsort hnonneg haccept
  have hsum : (pairRoot N t (rootSeed false buffer N t)).word.sum +
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
      (N : ℝ) ^ ((pairRoot N t (rootSeed false buffer N t)).word.sum +
        (chosen.map (coordinate N)).sum) = (fullModulus t chosen.prod : ℝ) := by
    simpa [pairRoot, fullModulus, markedProduct, List.map_cons, List.sum_cons,
      List.prod_cons, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc]
      using hpower
  rw [← hpower']
  exact Real.rpow_le_rpow_of_exponent_le hNr.le hsum

/-- SAME nonzero native rho, SAME original pair labels, SAME small Rosser
level. Its signed active factorization pays the full physical modulus,
with no rank restriction and no replacement coefficient. -/
theorem native_U5_physical_modulus_lt_buffered
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hbuffer : 0 ≤ buffer) (hb : buffer ≤ 1 / 1000)
    (epsilon : ℝ) (halloc : attachmentNu * epsilon ≤ (buffer : ℝ))
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) {k : ℕ}
    (hk : rho N epsilon (selectedPolicy R bank buffer false N t) k ≠ 0) :
    (fullModulus t k : ℝ) < (N : ℝ) ^ (topCap + (buffer : ℝ)) := by
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨s, hs, r, hr, chosen, hsub, hprod, hkprod, haccept⟩ :=
    native_U5_nonzero_word R bank buffer epsilon N t hk
  have hrough : (fullModulus t r : ℝ) ≤ (N : ℝ) ^ topCap := by
    simpa only [hprod] using selected_U5_accepted_word_le_topCap
      R bank buffer hbuffer hb hN ht (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) hsub haccept
  have hpair : (s, r) ∈ P5CausalRhoFactorization.pairs
      (selectedPolicy R bank buffer false N t) N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N) := Finset.mem_product.mpr ⟨hs, hr⟩
  have hvalue := P5CausalRhoFactorization.rho_at_pair
    (selectedPolicy R bank buffer false N t) N (Nat.ceil (cutoff N))
    (smallCutoff N epsilon) (cutoff N) (smallLevel N epsilon) hpair
  have hactive : (s, r) ∈ P5CausalRhoFactorization.activePairs
      (selectedPolicy R bank buffer false N t) N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N) (smallLevel N epsilon) := by
    apply Finset.mem_filter.mpr
    refine ⟨hpair, ?_⟩
    rw [← hvalue, ← hkprod]
    exact hk
  have hsmall : (s : ℝ) < (N : ℝ) ^ (buffer : ℝ) :=
    (P5CausalRhoFactorization.active_small_factor_lt
      (selectedPolicy R bank buffer false N t) N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N) (smallLevel N epsilon) hactive).trans_le
      (fifth_native_small_level_budget hNr epsilon buffer halloc)
  calc
    (fullModulus t k : ℝ) = (s : ℝ) * (fullModulus t r : ℝ) := by
      rw [hkprod]
      simp only [fullModulus, markedProduct, Nat.cast_mul]
      ring
    _ ≤ (s : ℝ) * (N : ℝ) ^ topCap :=
      mul_le_mul_of_nonneg_left hrough (Nat.cast_nonneg s)
    _ < (N : ℝ) ^ (buffer : ℝ) * (N : ℝ) ^ topCap :=
      mul_lt_mul_of_pos_right hsmall
        (Real.rpow_pos_of_pos (zero_lt_one.trans hNr) topCap)
    _ = (N : ℝ) ^ (topCap + (buffer : ℝ)) := by
      rw [Real.rpow_add (zero_lt_one.trans hNr)]
      ring

/-- A single fixed legal exponent, with the original buffer and small
level allocation still explicit in the hypotheses. -/
theorem native_U5_physical_modulus_lt_theta
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hbuffer : 0 ≤ buffer) (hb : buffer ≤ 1 / 1000)
    (epsilon : ℝ) (halloc : attachmentNu * epsilon ≤ (buffer : ℝ))
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) {k : ℕ}
    (hk : rho N epsilon (selectedPolicy R bank buffer false N t) k ≠ 0) :
    (fullModulus t k : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  exact (native_U5_physical_modulus_lt_buffered
    R bank buffer hbuffer hb epsilon halloc hN ht hk).trans
    ((Real.rpow_lt_rpow_left_iff hNr).mpr (buffered_cap_lt_theta buffer hb))

/-- Every nonzero atom of the EXISTING pooled integer rho has the same
physical cap. Original fibre uniqueness and the integer-to-real identity
transfer nonvanishing to the literal native row coefficient. -/
theorem selected_integerRho_nonzero_modulus_lt_theta
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hbuffer : 0 ≤ buffer) (hb : buffer ≤ 1 / 1000)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (halloc : attachmentNu * epsilon ≤ (buffer : ℝ))
    {N : ℕ} (hN : 2 ≤ N) {q : ℕ}
    (hq : integerRho N epsilon (selectedPolicy R bank buffer false N) q ≠ 0) :
    (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  have hmem : q ∈ moduli N epsilon (selectedPolicy R bank buffer false N) := by
    by_contra hnot
    exact hq (P3ActualU6PhysicalRhoPushforward.tagged_physical_integer_rho_zero_off_support
      (pairSupport N) (fun t => support N epsilon (selectedPolicy R bank buffer false N t))
      fullModulus (rowInteger N epsilon (selectedPolicy R bank buffer false N)) q hnot)
  obtain ⟨t, ht, hqmem⟩ := Finset.mem_biUnion.mp hmem
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hqmem
  have hinteger : rowInteger N epsilon (selectedPolicy R bank buffer false N) t k ≠ 0 := by
    rw [← integerRho_at_original (selectedPolicy R bank buffer false N)
      (attachment_gates hN hepsilon hepsilon8).2.2 ht hk]
    exact hq
  have hrow : rho N epsilon (selectedPolicy R bank buffer false N t) k ≠ 0 := by
    intro hz
    apply hinteger
    have hzcast : (rowInteger N epsilon (selectedPolicy R bank buffer false N) t k : ℝ) = 0 := by
      change (P3ActualEvenLowerIntegerRho.actualEvenLowerIntegerRho _ _ _ _ _ _ _ : ℝ) = 0
      rw [P3ActualEvenLowerIntegerRho.actualEvenLowerIntegerRho_cast]
      exact hz
    exact_mod_cast hzcast
  exact native_U5_physical_modulus_lt_theta
    R bank buffer hbuffer hb epsilon halloc hN ht hrow

end
end ImbalancedChen.P3OriginalU5PhysicalModulusCap
