import ImbalancedChen.P2RoundedFibreCore
import ImbalancedChen.P3OriginalU5PhysicalModulusCap
import ImbalancedChen.P3OriginalU5RoundedCountInsertion

/-!
# Fixed-mesh physical support for the actual rounded U5 output

SOURCE ONLY / UNCOMPILED / NO FORMAL ACCEPTANCE.

The original U5 selector and its selected pair-root run supply the raw
full-prefix level. The actual positive rough cutoff supplies a rank bound.
The already existing same-fibre rounding theorem then chooses one positive
mesh before N, the bank, and the arithmetic pair. It includes the original
small beta level in the complete physical modulus.

No new rounding algorithm is introduced. In particular an outward negative
rounded word is handled by its old same-label raw witness, not by assuming
it belongs to the raw retained support. The coefficient is exactly the one
used by RoundedCountInsertion. This support envelope is not the auxiliary
factorization cover or a common-Q family/admission/PP theorem.
-/

namespace ImbalancedChen.P3OriginalU5RoundedModulusCap

noncomputable section
open scoped Classical List
open P2LowerCapPlanIntegerRetention (coordinate)
open P2OriginalPairSourceReceiver (PairRange pairPlan)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalPairRootRoughProducer (pair_policy_support_iff)
open P2OriginalSelectedPairNativeData (selectedPolicy rootSeed)
open P2OriginalLowerCompactStartCapConstructor (topCap)
open P2LowerCanonicalRetainedTrace (actual_chosen_eq_canonical)
open P3OriginalU5PhysicalModulusCap
open P3OriginalU5RoundedCountInsertion (roundedRho)
open P5OriginalU5CausalFinite (attachmentNu cutoff pairSupport smallCutoff smallLevel)
open P5OriginalU5PlateauPrimeBV (markedProduct fullModulus)

/-- Only rough slots are counted. The small beta divisor is kept separate. -/
abbrev rawRank (epsilon : ℝ) : ℕ :=
  Nat.ceil (topCap / (attachmentNu * epsilon ^ 2))

/-- Actual original U5 raw support supplies BOTH inputs of the old
rounding-level theorem. The sixth-pair selector is not substituted. -/
theorem selected_U5_raw_level_and_rank
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : 0 ≤ buffer) (hb' : buffer ≤ 1 / 1000)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (enum : ℕ) {r : ℕ}
    (hr : r ∈ P2LowerFiniteCellRounding.rawSupport
      (selectedPolicy R bank buffer false N t) N enum (smallCutoff N epsilon) (cutoff N)) :
    (fullModulus t r : ℝ) ≤ (N : ℝ) ^ topCap ∧
      r.primeFactorsList.length ≤ rawRank epsilon := by
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans hNr
  have homega : 0 < attachmentNu * epsilon ^ 2 := by
    dsimp [attachmentNu]
    positivity
  obtain ⟨chosen, hsub, haccept, hprod⟩ :=
    (pair_policy_support_iff
      (pairPlan R bank (2 * buffer) (rootSeed false buffer N t))
      (R.epsilon : ℝ) (P2OriginalPairSourceReceiver.ceiling : ℝ)
      (rootSeed false buffer N t) N enum t (smallCutoff N epsilon) (cutoff N) r).mp hr
  have hphysical : (fullModulus t r : ℝ) ≤ (N : ℝ) ^ topCap := by
    simpa only [hprod] using selected_U5_accepted_word_le_topCap
      R bank buffer hb hb' hN ht enum (smallCutoff N epsilon) hsub haccept
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

/-- One positive mesh precedes the scale, the finite bank and every original
pair. The same rounded rho as the count entrance has a strict complete
physical exponent below 599/1000, including its active small beta factor. -/
theorem exists_uniform_rounded_U5_modulus_cap
    (buffer : ℚ) (hb : 0 ≤ buffer) (hb' : buffer ≤ 1 / 1000)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (halloc : attachmentNu * epsilon ≤ (buffer : ℝ)) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ (R : PairRange) (mesh : ℕ) (bank : CandidateBank mesh),
      ∀ N : ℕ, 2 ≤ N → ∀ t ∈ pairSupport N, ∀ k : ℕ,
        roundedRho N epsilon tau (selectedPolicy R bank buffer false N t) k ≠ 0 →
          (fullModulus t k : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  have hgap : topCap + attachmentNu * epsilon < (599 / 1000 : ℝ) :=
    (add_le_add_left halloc topCap).trans_lt (buffered_cap_lt_theta buffer hb')
  let nu : ℝ := (topCap + attachmentNu * epsilon + 599 / 1000) / 2
  have hnu : topCap + attachmentNu * epsilon < nu := by dsimp [nu]; linarith
  have hnu' : nu < (599 / 1000 : ℝ) := by dsimp [nu]; linarith
  obtain ⟨tau, htau, hlevel⟩ :=
    P2RoundedCausalFibreLossAndLevel.exists_uniform_mesh_physical_level
      topCap (attachmentNu * epsilon) nu (rawRank epsilon) hnu
  refine ⟨tau, htau, ?_⟩
  intro R mesh bank N hN t ht k hk
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hbound := hlevel N hNr (selectedPolicy R bank buffer false N t)
    (Nat.ceil (cutoff N)) (markedProduct t) (smallCutoff N epsilon) (cutoff N)
    (fun r hr => selected_U5_raw_level_and_rank R bank buffer hb hb'
      epsilon hepsilon hN ht (Nat.ceil (cutoff N)) hr) k hk
  exact hbound.trans_lt ((Real.rpow_lt_rpow_left_iff hNr).mpr hnu')

end
end ImbalancedChen.P3OriginalU5RoundedModulusCap
