import ImbalancedChen.RealHalfProductMassSplit
import ImbalancedChen.P4BLabelledPairDictionary
import ImbalancedChen.P4BSupportedRampStripUnion
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FinCases

/-!
# P4B: actual lower-product wall-strip mass

SOURCE ONLY / YELLOW / UNCOMPILED.

The P4B labelled dictionary import names the intended module of its sibling
draft and must be staged before a later compiler check.  The ordinary strip
uses prime pairs in the original finite cap without an ordering restriction.
The exact upper wall puts every product at most T=2*N^(1-kappa), so a crude
two-orientations product count and the proved cutoff absorption already pay
the entire strip, uniformly in its width. No analytic premise is introduced.
-/

namespace ImbalancedChen.P4BLowerProductStripMass

noncomputable section
open Filter Topology
open ImbalancedChen.Part3
open ImbalancedChen.P4BLabelledPairDictionary

private theorem prime_product_mem_Icc {U : ℝ} {p : ℕ × ℕ}
    (hp : Nat.Prime p.1 ∧ Nat.Prime p.2) (hprod : (p.1 * p.2 : ℕ) ≤ U) :
    p.1 * p.2 ∈ Finset.Icc 1 (Nat.ceil U) := by
  have hpos : 0 < p.1 * p.2 := Nat.mul_pos hp.1.pos hp.2.pos
  have hceil : (p.1 * p.2 : ℕ) ≤ Nat.ceil U := by
    exact_mod_cast hprod.trans (Nat.le_ceil U)
  exact Finset.mem_Icc.mpr ⟨by omega, hceil⟩

/-- Ordered prime products are counted once, including squares. -/
theorem ordered_prime_pairs_card_le_ceil (S : Finset (ℕ × ℕ)) (U : ℝ)
    (hprime : ∀ p ∈ S, Nat.Prime p.1 ∧ Nat.Prime p.2)
    (horder : ∀ p ∈ S, p.1 ≤ p.2)
    (hprod : ∀ p ∈ S, (p.1 * p.2 : ℕ) ≤ U) : S.card ≤ Nat.ceil U := by
  classical
  have hcard : S.card ≤ (Finset.Icc 1 (Nat.ceil U)).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1 * p.2)
    · intro p hp
      exact prime_product_mem_Icc (hprime p hp) (hprod p hp)
    · intro p hp t ht heq
      obtain ⟨hp1, hp2⟩ := hprime p hp
      obtain ⟨ht1, ht2⟩ := hprime t ht
      obtain ⟨h1, h2⟩ := ordered_prime_factors_unique
        hp1 hp2 ht1 ht2 (horder p hp) (horder t ht) heq
      exact Prod.ext h1 h2
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hcard

/-- Any finite prime-pair set, with no ordering restriction, has at most
two pairs per possible positive product. The reverse part is sorted by
swapping its factors; no assertion of source symmetry is needed. -/
theorem prime_pairs_card_le_two_ceil (S : Finset (ℕ × ℕ)) (U : ℝ)
    (hprime : ∀ p ∈ S, Nat.Prime p.1 ∧ Nat.Prime p.2)
    (hprod : ∀ p ∈ S, (p.1 * p.2 : ℕ) ≤ U) : S.card ≤ 2 * Nat.ceil U := by
  classical
  let A := S.filter (fun p => p.1 ≤ p.2)
  let B := S.filter (fun p => ¬p.1 ≤ p.2)
  have hA : A.card ≤ Nat.ceil U := by
    apply ordered_prime_pairs_card_le_ceil A U
    · intro p hp
      exact hprime p (Finset.mem_filter.mp hp).1
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p hp
      exact hprod p (Finset.mem_filter.mp hp).1
  have hB : B.card ≤ Nat.ceil U := by
    have hcard : B.card ≤ (Finset.Icc 1 (Nat.ceil U)).card := by
      apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1 * p.2)
      · intro p hp
        exact prime_product_mem_Icc
          (hprime p (Finset.mem_filter.mp hp).1)
          (hprod p (Finset.mem_filter.mp hp).1)
      · intro p hp t ht heq
        obtain ⟨hp1, hp2⟩ := hprime p (Finset.mem_filter.mp hp).1
        obtain ⟨ht1, ht2⟩ := hprime t (Finset.mem_filter.mp ht).1
        have hporder : p.2 ≤ p.1 :=
          (lt_of_not_ge (Finset.mem_filter.mp hp).2).le
        have htorder : t.2 ≤ t.1 :=
          (lt_of_not_ge (Finset.mem_filter.mp ht).2).le
        have hswap : p.2 * p.1 = t.2 * t.1 := by
          simpa only [Nat.mul_comm] using heq
        obtain ⟨h2, h1⟩ := ordered_prime_factors_unique
          hp2 hp1 ht2 ht1 hporder htorder hswap
        exact Prod.ext h1 h2
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hcard
  have hsplit : A.card + B.card = S.card :=
    Finset.card_filter_add_card_filter_not S (fun p => p.1 ≤ p.2)
  omega

/-- Ordinary prime pairs on the literal finite coordinate cap; no order or
distinctness condition is imposed. -/
def ordinaryPrimePairs (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter
    (fun p => Nat.Prime p.1 ∧ Nat.Prime p.2)

@[simp] theorem mem_ordinaryPrimePairs {N : ℕ} {p : ℕ × ℕ} :
    p ∈ ordinaryPrimePairs N ↔
      p.1 ≤ N ∧ p.2 ≤ N ∧ Nat.Prime p.1 ∧ Nat.Prime p.2 := by
  classical
  simp only [ordinaryPrimePairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range, Nat.lt_succ_iff, and_assoc]

/-- Signed normalized distance below the lower-product wall. -/
def normalizedLowerWall (kappa : ℝ) (N m : ℕ) : ℝ :=
  (Real.log (m : ℝ) - Real.log (manuscriptHalfProductCutoff kappa N)) /
    Real.log (N : ℝ)

/-- The exact strict-lower, closed-upper logarithmic collar. -/
def lowerProductStrip (kappa delta : ℝ) (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (ordinaryPrimePairs N).filter fun p =>
    -delta < normalizedLowerWall kappa N (p.1 * p.2) ∧
      normalizedLowerWall kappa N (p.1 * p.2) ≤ 0

/-- The same collar on the actual rank-two labelled prime carrier. -/
def labelledLowerProductStrip (kappa delta : ℝ) (N : ℕ) :
    Finset (Fin 2 → Fin (N + 1)) := by
  classical
  exact (labelledPrimeTuples 2 N).filter fun t =>
    -delta < normalizedLowerWall kappa N (labelledProduct t) ∧
      normalizedLowerWall kappa N (labelledProduct t) ≤ 0

/-- With this strict lower-width convention, every nonpositive width gives
an empty collar. -/
theorem lowerProductStrip_eq_empty_of_nonpos {kappa delta : ℝ} {N : ℕ}
    (hdelta : delta ≤ 0) : lowerProductStrip kappa delta N = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro p hp
  have hwall := (Finset.mem_filter.mp hp).2
  linarith [hwall.1, hwall.2]

/-- Exact endpoint dictionary, valid for every real width delta.
Negative and zero widths therefore give the corresponding empty interval. -/
theorem normalizedLowerWall_iff_power_interval {kappa delta : ℝ} {N m : ℕ}
    (hN : 2 ≤ N) (hm : 0 < m) :
    (-delta < normalizedLowerWall kappa N m ∧
        normalizedLowerWall kappa N m ≤ 0) ↔
      manuscriptHalfProductCutoff kappa N * (N : ℝ) ^ (-delta) < (m : ℝ) ∧
        (m : ℝ) ≤ manuscriptHalfProductCutoff kappa N := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans hN1
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hT : 0 < manuscriptHalfProductCutoff kappa N := by
    unfold manuscriptHalfProductCutoff
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hNpos _)
  have hpow : 0 < (N : ℝ) ^ (-delta) := Real.rpow_pos_of_pos hNpos _
  have hlogLow :
      Real.log (manuscriptHalfProductCutoff kappa N * (N : ℝ) ^ (-delta)) =
        Real.log (manuscriptHalfProductCutoff kappa N) +
          (-delta) * Real.log (N : ℝ) := by
    rw [Real.log_mul hT.ne' hpow.ne', Real.log_rpow hNpos]
  unfold normalizedLowerWall
  constructor
  · rintro ⟨hlow, hhigh⟩
    have hlowMul := (lt_div_iff₀ hlog).mp hlow
    have hhighMul := (div_le_iff₀ hlog).mp hhigh
    have hlowLog :
        Real.log (manuscriptHalfProductCutoff kappa N * (N : ℝ) ^ (-delta)) <
          Real.log (m : ℝ) := by
      rw [hlogLow]
      linarith
    have hhighLog : Real.log (m : ℝ) ≤
        Real.log (manuscriptHalfProductCutoff kappa N) := by linarith
    exact ⟨(Real.log_lt_log_iff (mul_pos hT hpow) hmR).mp hlowLog,
      (Real.log_le_log_iff hmR hT).mp hhighLog⟩
  · rintro ⟨hlow, hhigh⟩
    have hlowLog := (Real.log_lt_log_iff (mul_pos hT hpow) hmR).mpr hlow
    have hhighLog := (Real.log_le_log_iff hmR hT).mpr hhigh
    rw [hlogLow] at hlowLog
    constructor
    · apply (lt_div_iff₀ hlog).mpr
      linarith
    · apply (div_le_iff₀ hlog).mpr
      linarith

/-- Every ordinary strip product is positive and at most the manuscript
cutoff. The lower-width condition does not enlarge this upper product cap. -/
theorem lowerProductStrip_product_bounds {kappa delta : ℝ} {N : ℕ}
    (hN : 2 ≤ N) {p : ℕ × ℕ} (hp : p ∈ lowerProductStrip kappa delta N) :
    0 < p.1 * p.2 ∧ (p.1 * p.2 : ℕ) ≤ manuscriptHalfProductCutoff kappa N := by
  classical
  rcases Finset.mem_filter.mp hp with ⟨hcarrier, hwall⟩
  rcases mem_ordinaryPrimePairs.mp hcarrier with ⟨_, _, hp1, hp2⟩
  have hpos : 0 < p.1 * p.2 := Nat.mul_pos hp1.pos hp2.pos
  exact ⟨hpos, ((normalizedLowerWall_iff_power_interval hN hpos).mp hwall).2⟩

/-- Generic two-orientation arithmetic product count specialized to the
literal lower-product strip. This bound is uniform in every real delta. -/
theorem lowerProductStrip_card_le_two_ceil {kappa delta : ℝ} {N : ℕ}
    (hN : 2 ≤ N) :
    (lowerProductStrip kappa delta N).card ≤
      2 * Nat.ceil (manuscriptHalfProductCutoff kappa N) := by
  classical
  apply prime_pairs_card_le_two_ceil (lowerProductStrip kappa delta N)
    (manuscriptHalfProductCutoff kappa N)
  · intro p hp
    have hcarrier := (Finset.mem_filter.mp hp).1
    exact ⟨(mem_ordinaryPrimePairs.mp hcarrier).2.2.1,
      (mem_ordinaryPrimePairs.mp hcarrier).2.2.2⟩
  · intro p hp
    exact (lowerProductStrip_product_bounds hN hp).2

/-- The actual labelled and ordinary collars have exactly the same count;
the tuple-pair dictionary preserves the literal product and all endpoints. -/
theorem labelledLowerProductStrip_card_eq (kappa delta : ℝ) (N : ℕ) :
    (labelledLowerProductStrip kappa delta N).card =
      (lowerProductStrip kappa delta N).card := by
  classical
  refine Finset.card_bij (fun t _ => tuplePair t) ?_ ?_ ?_
  · intro t ht
    rcases Finset.mem_filter.mp ht with ⟨hprime, hwall⟩
    have hp : ∀ i : Fin 2, Nat.Prime (t i).val :=
      (Finset.mem_filter.mp hprime).2
    apply Finset.mem_filter.mpr
    refine ⟨mem_ordinaryPrimePairs.mpr ⟨?_, ?_, hp 0, hp 1⟩, ?_⟩
    · exact Nat.lt_succ_iff.mp (t 0).isLt
    · exact Nat.lt_succ_iff.mp (t 1).isLt
    · simpa only [labelledProduct_eq_pairProduct] using hwall
  · intro t ht u hu heq
    exact tuplePair_injective N heq
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hcarrier, hwall⟩
    rcases mem_ordinaryPrimePairs.mp hcarrier with ⟨hpN, hqN, hpPrime, hqPrime⟩
    refine ⟨pairTuple N p hpN hqN, ?_, tuplePair_pairTuple N p hpN hqN⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro i
      fin_cases i
      · simpa [pairTuple] using hpPrime
      · simpa [pairTuple] using hqPrime
    · simpa only [labelledProduct_pairTuple] using hwall

/-- Standalone arithmetic supplier for the complete two-orientation ceiling
cost. It uses the already proved power-versus-log cutoff absorption. -/
theorem eventually_two_ceil_cutoff_le_massScale {kappa : ℝ}
    (hkappa : 0 < kappa) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      2 * (Nat.ceil (manuscriptHalfProductCutoff kappa N) : ℝ) ≤
        epsilon * ((N : ℝ) / Real.log (N : ℝ)) := by
  have h := eventually_manuscriptHalfProductCutoff_add_one_le_massScale
    hkappa (epsilon / 2) (half_pos hepsilon)
  filter_upwards [h] with N hbudget
  have hceil : (Nat.ceil (manuscriptHalfProductCutoff kappa N) : ℝ) ≤
      manuscriptHalfProductCutoff kappa N + 1 :=
    (Nat.ceil_lt_add_one (manuscriptHalfProductCutoff_nonneg kappa N)).le
  linarith

/-- One eventual threshold pays EVERY finite prime-pair set below the
manuscript product cutoff. Only its actual prime/product geometry is needed;
the source may be a lower collar, a closed ramp margin, or a positive outer
low-product part, and no coordinate cap or ordering is required. -/
theorem prime_pairs_below_cutoff_uniform_mass_reserve {kappa eta : ℝ}
    (hkappa : 0 < kappa) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ S : Finset (ℕ × ℕ),
      (∀ p ∈ S, Nat.Prime p.1 ∧ Nat.Prime p.2) →
      (∀ p ∈ S, (p.1 * p.2 : ℕ) ≤ manuscriptHalfProductCutoff kappa N) →
      (S.card : ℝ) ≤ eta * ((N : ℝ) / Real.log (N : ℝ)) := by
  have habsorb := eventually_two_ceil_cutoff_le_massScale hkappa eta heta
  have hbound : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧
      ∀ S : Finset (ℕ × ℕ),
        (∀ p ∈ S, Nat.Prime p.1 ∧ Nat.Prime p.2) →
        (∀ p ∈ S, (p.1 * p.2 : ℕ) ≤ manuscriptHalfProductCutoff kappa N) →
        (S.card : ℝ) ≤ eta * ((N : ℝ) / Real.log (N : ℝ)) := by
    filter_upwards [habsorb, eventually_ge_atTop (2 : ℕ)] with N hbudget hN
    refine ⟨hN, ?_⟩
    intro S hprime hprod
    have hcard : (S.card : ℝ) ≤
        2 * (Nat.ceil (manuscriptHalfProductCutoff kappa N) : ℝ) := by
      exact_mod_cast prime_pairs_card_le_two_ceil S
        (manuscriptHalfProductCutoff kappa N) hprime hprod
    exact hcard.trans hbudget
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hbound
  exact ⟨N0, (hN0 N0 le_rfl).1, fun N hN => (hN0 N hN).2⟩

/-- The whole lower-product strip is negligible on N/log N.  One threshold
works for ALL real widths, and for both actual pair-carrier conventions. -/
theorem lowerProductStrip_uniform_mass_reserve {kappa eta : ℝ}
    (hkappa : 0 < kappa) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ delta : ℝ,
      ((lowerProductStrip kappa delta N).card : ℝ) ≤
          eta * ((N : ℝ) / Real.log (N : ℝ)) ∧
        ((labelledLowerProductStrip kappa delta N).card : ℝ) ≤
          eta * ((N : ℝ) / Real.log (N : ℝ)) := by
  classical
  obtain ⟨N0, hN0, hbound⟩ := prime_pairs_below_cutoff_uniform_mass_reserve hkappa heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN delta
  have hord : ((lowerProductStrip kappa delta N).card : ℝ) ≤
      eta * ((N : ℝ) / Real.log (N : ℝ)) := by
    apply hbound N hN (lowerProductStrip kappa delta N)
    · intro p hp
      have hcarrier := (Finset.mem_filter.mp hp).1
      exact ⟨(mem_ordinaryPrimePairs.mp hcarrier).2.2.1,
        (mem_ordinaryPrimePairs.mp hcarrier).2.2.2⟩
    · intro p hp
      exact (lowerProductStrip_product_bounds (hN0.trans hN) hp).2
  refine ⟨hord, ?_⟩
  simpa only [labelledLowerProductStrip_card_eq] using hord

/-- A positive width smaller than kappa is available before the single
eventual threshold, as required by the coarse expanded-cutoff convention too. -/
theorem exists_lowerProductStrip_mass_reserve {kappa eta : ℝ}
    (hkappa : 0 < kappa) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ delta < kappa ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N →
        ((lowerProductStrip kappa delta N).card : ℝ) ≤
            eta * ((N : ℝ) / Real.log (N : ℝ)) ∧
          ((labelledLowerProductStrip kappa delta N).card : ℝ) ≤
            eta * ((N : ℝ) / Real.log (N : ℝ)) := by
  obtain ⟨N0, hN0, hbound⟩ := lowerProductStrip_uniform_mass_reserve hkappa heta
  refine ⟨kappa / 2, half_pos hkappa, by linarith, N0, hN0, ?_⟩
  intro N hN
  exact hbound N hN (kappa / 2)

/-- The actual physical lower-product margin is precisely the signed
normalized log-product margin on the genuine prime carrier. -/
theorem physical_lower_margin_eq {kappa b : ℝ} {N : ℕ}
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N) :
    P4B.physicalPairMargins b N (manuscriptHalfProductCutoff kappa N) t 2 =
      normalizedLowerWall kappa N (labelledProduct t) := by
  have hp : ∀ i : Fin 2, Nat.Prime (t i).val := (Finset.mem_filter.mp ht).2
  have hp0 : (0 : ℝ) < ((t 0).val : ℝ) := by exact_mod_cast (hp 0).pos
  have hp1 : (0 : ℝ) < ((t 1).val : ℝ) := by exact_mod_cast (hp 1).pos
  rw [P4B.physicalPairMargins_eq_original_of_ne_upper b
    (manuscriptHalfProductCutoff kappa N) N t (by decide : (2 : Fin 4) ≠ 3)]
  simp [P4B.actualPairMargins, P4BLabelledLogGeometry.logPoint,
    normalizedLowerWall, labelledProduct_eq_pairProduct, tuplePair,
    Nat.cast_mul, Real.log_mul hp0.ne' hp1.ne'] <;> ring

/-- Direct adapter from the EXACT jointly supported physical strip at wall
2. All other softened margins remain on the source of this inclusion. -/
theorem physicalSupportedLowerStrip_subset (width b kappa : ℝ) (N : ℕ) :
    P4B.physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 2 ⊆
      labelledLowerProductStrip kappa width N := by
  classical
  intro t ht
  rcases (P4B.mem_physicalSupportedStrip width b N
    (manuscriptHalfProductCutoff kappa N) 2 t).mp ht with ⟨hprime, hwall, hsoft⟩
  apply Finset.mem_filter.mpr
  refine ⟨hprime, ?_⟩
  simpa only [physical_lower_margin_eq (kappa := kappa) (b := b) hprime] using hwall

/-- Direct unconditional i=2 reserve for the actual jointly supported
physical strips. A single threshold works for all widths and all b; callers
may therefore select any common positive width below their widthMax. -/
theorem physicalSupportedLowerStrip_mass_reserve {kappa eta : ℝ}
    (hkappa : 0 < kappa) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ width b : ℝ,
      ((P4B.physicalSupportedStrip width b N
        (manuscriptHalfProductCutoff kappa N) 2).card : ℝ) ≤
          eta * ((N : ℝ) / Real.log (N : ℝ)) := by
  obtain ⟨N0, hN0, hbound⟩ := lowerProductStrip_uniform_mass_reserve hkappa heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN width b
  have hcard : ((P4B.physicalSupportedStrip width b N
      (manuscriptHalfProductCutoff kappa N) 2).card : ℝ) ≤
      ((labelledLowerProductStrip kappa width N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (physicalSupportedLowerStrip_subset width b kappa N)
  exact hcard.trans (hbound N hN width).2

end
end ImbalancedChen.P4BLowerProductStripMass
