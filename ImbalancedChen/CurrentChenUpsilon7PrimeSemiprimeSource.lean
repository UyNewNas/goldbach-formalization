import ImbalancedChen.CurrentChenUpsilon9PrimeSource

/-!
# Exact prime, semiprime and unit branches of the current seventh source

The literal seventh quotient is rough at the second selected prime. Its
cofactor need not be prime: the current lower exponent is below one fourth.
The actual exponent nevertheless gives `5 * (59 / 250) > 1`, so every
cofactor is strictly below the cube of the second prime. This leaves one,
a prime, or an ordered product of two primes, including prime squares.

All branches retain the original outer pair, its strict square-root cap
with centre `N`, and the original primitive additive prime. No squarefree
receiver assumption, mean estimate, numerical sieve constant or analytic
supplier occurs here. The unit and diagonal branches are retained exactly.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical

private theorem currentChenSeventh_rough_lt_cube_classification
    {q y : ℕ} (hq : 0 < q) (hrough : ChenPrimeRough (y : ℝ) q)
    (hsmall : q < y ^ 3) :
    q = 1 ∨ Nat.Prime q ∨ ∃ r s : ℕ,
      Nat.Prime r ∧ Nat.Prime s ∧ y ≤ r ∧ r ≤ s ∧ q = r * s := by
  by_cases hone : q = 1
  · exact Or.inl hone
  by_cases hprime : Nat.Prime q
  · exact Or.inr (Or.inl hprime)
  let r := Nat.minFac q
  let s := q / r
  have hr : Nat.Prime r := Nat.minFac_prime hone
  have hmul : r * s = q := Nat.mul_div_cancel' (Nat.minFac_dvd q)
  have hrs : r ≤ s := Nat.minFac_le_div hq hprime
  have hyr : y ≤ r := by
    exact_mod_cast hrough r hr (Nat.minFac_dvd q)
  have hspos : 0 < s := hr.pos.trans_le hrs
  have hsone : s ≠ 1 := by
    have hr2 := hr.two_le
    omega
  have hs : Nat.Prime s := by
    by_contra hsnot
    have ht : Nat.Prime (Nat.minFac s) := Nat.minFac_prime hsone
    have hsq : s ∣ q := by
      rw [← hmul]
      exact dvd_mul_left s r
    have hyt : y ≤ Nat.minFac s := by
      exact_mod_cast hrough (Nat.minFac s) ht ((Nat.minFac_dvd s).trans hsq)
    have hysq : y ^ 2 ≤ s :=
      (pow_le_pow_left' hyt 2).trans (Nat.minFac_sq_le_self hspos hsnot)
    have hcube : y ^ 3 ≤ q := by
      calc
        y ^ 3 = y * y ^ 2 := by ring
        _ ≤ r * s := Nat.mul_le_mul hyr hysq
        _ = q := hmul
    exact (not_le_of_gt hsmall) hcube
  exact Or.inr (Or.inr ⟨r, s, hr, hs, hyr, hrs, hmul.symm⟩)

/-- The current seventh rough cofactor has at most two prime factors with
multiplicity. The inclusive lower wall allows both `r = p₂` and `r = s`. -/
theorem currentChenUpsilon7_quotient_classification {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) {q : ℕ}
    (hq : q ∈ chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)) :
    q < t.2 ^ 3 ∧
      (q = 1 ∨ Nat.Prime q ∨ ∃ r s : ℕ,
        Nat.Prime r ∧ Nat.Prime s ∧ t.2 ≤ r ∧ r ≤ s ∧ q = r * s) := by
  obtain ⟨hc, hD, h₁₂, _hcap⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc₁, hc₂⟩ := Finset.mem_product.mp hc
  have hp₁ := (mem_chenAdditivePrimeCarrier.mp hc₁).2.1
  have hp₂ := (mem_chenAdditivePrimeCarrier.mp hc₂).2.1
  have hb : 0 < t.1 * t.2 := mul_pos hp₁.pos hp₂.pos
  obtain ⟨hqsource, hrough⟩ := Finset.mem_filter.mp hq
  obtain ⟨_P, _hP, _hmul, hlt, hqpos, _hquot⟩ :=
    currentChenUpsilon9_quotient_witness hb hqsource
  have hN : (1 : ℝ) < N := by
    exact_mod_cast lt_trans hp₁.one_lt (mem_chenAdditivePrimeCarrier.mp hc₁).1
  have hDpow : ((N : ℝ) ^ (59 / 250 : ℝ)) ^ 5 =
      (N : ℝ) ^ (59 / 50 : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N) (59 / 250 : ℝ) 5]
    congr 1
    norm_num
  have hNpow : (N : ℝ) < ((N : ℝ) ^ (59 / 250 : ℝ)) ^ 5 := by
    rw [hDpow]
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ < (N : ℝ) ^ (59 / 50 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt hN (by norm_num)
  have hDfive : ((N : ℝ) ^ (59 / 250 : ℝ)) ^ 5 ≤ (t.1 : ℝ) ^ 5 :=
    pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg N) _) hD 5
  have h₁₂R : (t.1 : ℝ) ≤ (t.2 : ℝ) := by exact_mod_cast h₁₂.le
  have hfirst : (t.1 : ℝ) ^ 5 ≤ (t.1 : ℝ) * (t.2 : ℝ) ^ 4 := by
    calc
      (t.1 : ℝ) ^ 5 = (t.1 : ℝ) * (t.1 : ℝ) ^ 4 := by ring
      _ ≤ (t.1 : ℝ) * (t.2 : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) h₁₂R 4) (Nat.cast_nonneg _)
  have hNprod : (N : ℝ) < (t.1 : ℝ) * (t.2 : ℝ) ^ 4 :=
    hNpow.trans_le (hDfive.trans hfirst)
  have hqsmall : q < t.2 ^ 3 := by
    by_contra hnot
    have hlower : t.2 ^ 3 ≤ q := Nat.le_of_not_gt hnot
    have hlowerR : (t.2 : ℝ) ^ 3 ≤ (q : ℝ) := by exact_mod_cast hlower
    have hltR : (t.1 : ℝ) * (t.2 : ℝ) * (q : ℝ) < (N : ℝ) := by
      exact_mod_cast hlt
    have hprod : (t.1 : ℝ) * (t.2 : ℝ) ^ 4 ≤
        (t.1 : ℝ) * (t.2 : ℝ) * (q : ℝ) := by
      calc
        (t.1 : ℝ) * (t.2 : ℝ) ^ 4 =
            ((t.1 : ℝ) * (t.2 : ℝ)) * (t.2 : ℝ) ^ 3 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlowerR
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    exact (not_lt_of_ge hprod) (hltR.trans hNprod)
  exact ⟨hqsmall, currentChenSeventh_rough_lt_cube_classification hqpos hrough hqsmall⟩

private theorem currentChenSeventh_sifted_mem_iff {N b q : ℕ}
    (hb : 0 < b) (z : ℝ) :
    q ∈ chenSiftedQuotientPrimeSource N b z ↔
      b * q < N ∧ N - b * q ∈ chenAdditivePrimeCarrier N ∧ ChenPrimeRough z q := by
  constructor
  · intro hq
    obtain ⟨hqsource, hrough⟩ := Finset.mem_filter.mp hq
    obtain ⟨P, hP, hmul, hlt, _hqpos, _hquot⟩ :=
      currentChenUpsilon9_quotient_witness hb hqsource
    have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
    have hrecover : N - b * q = P := by omega
    exact ⟨hlt, by simpa only [hrecover] using hP, hrough⟩
  · rintro ⟨hlt, hP, hrough⟩
    have hreceiver : N - (N - b * q) = b * q := Nat.sub_sub_self hlt.le
    have hdiv : b ∣ N - (N - b * q) := by
      rw [hreceiver]
      exact dvd_mul_right b q
    have hquot : (N - (N - b * q)) / b = q := by
      rw [hreceiver]
      exact Nat.mul_div_cancel_left q hb
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨N - b * q,
        mem_chenQuotientPrimeCarrier.mpr ⟨hP, hdiv⟩, hquot⟩, hrough⟩

private theorem currentChenSeventh_rough_prime_mul_iff {r s : ℕ} {z : ℝ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrs : r ≤ s) :
    ChenPrimeRough z (r * s) ↔ z ≤ (r : ℝ) := by
  constructor
  · intro h
    exact h r hr (dvd_mul_right r s)
  · intro h q hq hdiv
    rcases hq.dvd_mul.mp hdiv with hdr | hds
    · have heq : q = r := (Nat.prime_dvd_prime_iff_eq hq hr).mp hdr
      simpa only [heq] using h
    · have heq : q = s := (Nat.prime_dvd_prime_iff_eq hq hs).mp hds
      subst q
      exact h.trans (by exact_mod_cast hrs)

private theorem currentChenSeventh_prime_factor_mem_carrier {N b q r : ℕ}
    (hb : 0 < b) (hq : q ∈ chenQuotientPrimeSource N b)
    (hr : Nat.Prime r) (hrq : r ∣ q) : r ∈ chenAdditivePrimeCarrier N := by
  obtain ⟨_P, _hP, _hmul, hlt, hqpos, _hquot⟩ :=
    currentChenUpsilon9_quotient_witness hb hq
  have hqle : q ≤ b * q := by
    calc
      q = 1 * q := (one_mul q).symm
      _ ≤ b * q := Nat.mul_le_mul_right q (by omega)
  have hrle : r ≤ q := Nat.le_of_dvd hqpos hrq
  exact mem_chenAdditivePrimeCarrier.mpr
    ⟨hrle.trans_lt (hqle.trans_lt hlt), hr,
      (chenQuotientPrimeSource_data hq).2.2.of_dvd_left hrq⟩

def currentChenUpsilon7PrimeTriples (N : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ) :=
  (chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))).sigma fun t =>
    (chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)).filter Nat.Prime

def currentChenUpsilon7UnitFibres (N : ℕ) : Finset (ℕ × ℕ) :=
  (chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))).filter fun t =>
    1 ∈ chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)

def currentChenUpsilon7SemiprimeQuadruples (N : ℕ) :
    Finset (Σ _ : ℕ × ℕ, ℕ × ℕ) :=
  (chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))).sigma fun t =>
    (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N).filter fun u =>
      t.2 ≤ u.1 ∧ u.1 ≤ u.2 ∧
        u.1 * u.2 ∈ chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)

theorem mem_currentChenUpsilon7PrimeTriples_iff {N p₁ p₂ q : ℕ} :
    (⟨(p₁, p₂), q⟩ : Σ _ : ℕ × ℕ, ℕ) ∈ currentChenUpsilon7PrimeTriples N ↔
      p₁ ∈ chenAdditivePrimeCarrier N ∧ p₂ ∈ chenAdditivePrimeCarrier N ∧
      (N : ℝ) ^ (59 / 250 : ℝ) ≤ (p₁ : ℝ) ∧ p₁ < p₂ ∧
      (p₂ : ℝ) < Real.sqrt ((N : ℝ) / (p₁ : ℝ)) ∧
      Nat.Prime q ∧ p₂ ≤ q ∧ p₁ * p₂ * q < N ∧
      N - p₁ * p₂ * q ∈ chenAdditivePrimeCarrier N := by
  simp only [currentChenUpsilon7PrimeTriples, Finset.mem_sigma,
    chenY7PrimeSelector, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨h₁, h₂⟩, hD, h₁₂, hcap⟩, hq, hprime⟩
    have hb : 0 < p₁ * p₂ := mul_pos
      (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
    obtain ⟨hlt, hP, hcut⟩ := (currentChenUpsilon9_prime_mem_iff hb hprime _).mp hq
    exact ⟨h₁, h₂, hD, h₁₂, hcap, hprime, by exact_mod_cast hcut, hlt, hP⟩
  · rintro ⟨h₁, h₂, hD, h₁₂, hcap, hprime, hcut, hlt, hP⟩
    have hb : 0 < p₁ * p₂ := mul_pos
      (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
    exact ⟨⟨⟨h₁, h₂⟩, hD, h₁₂, hcap⟩,
      (currentChenUpsilon9_prime_mem_iff hb hprime _).mpr
        ⟨hlt, hP, by exact_mod_cast hcut⟩, hprime⟩

theorem mem_currentChenUpsilon7SemiprimeQuadruples_iff {N p₁ p₂ r s : ℕ} :
    (⟨(p₁, p₂), (r, s)⟩ : Σ _ : ℕ × ℕ, ℕ × ℕ) ∈
        currentChenUpsilon7SemiprimeQuadruples N ↔
      p₁ ∈ chenAdditivePrimeCarrier N ∧ p₂ ∈ chenAdditivePrimeCarrier N ∧
      (N : ℝ) ^ (59 / 250 : ℝ) ≤ (p₁ : ℝ) ∧ p₁ < p₂ ∧
      (p₂ : ℝ) < Real.sqrt ((N : ℝ) / (p₁ : ℝ)) ∧
      Nat.Prime r ∧ Nat.Prime s ∧ p₂ ≤ r ∧ r ≤ s ∧
      p₁ * p₂ * (r * s) < N ∧
      N - p₁ * p₂ * (r * s) ∈ chenAdditivePrimeCarrier N := by
  simp only [currentChenUpsilon7SemiprimeQuadruples, Finset.mem_sigma,
    chenY7PrimeSelector, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨h₁, h₂⟩, hD, h₁₂, hcap⟩, ⟨hrc, hsc⟩, hcut, hrs, hsource⟩
    have hb : 0 < p₁ * p₂ := mul_pos
      (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
    obtain ⟨hlt, hP, _hrough⟩ := (currentChenSeventh_sifted_mem_iff hb _).mp hsource
    exact ⟨h₁, h₂, hD, h₁₂, hcap,
      (mem_chenAdditivePrimeCarrier.mp hrc).2.1,
      (mem_chenAdditivePrimeCarrier.mp hsc).2.1, hcut, hrs, hlt, hP⟩
  · rintro ⟨h₁, h₂, hD, h₁₂, hcap, hr, hs, hcut, hrs, hlt, hP⟩
    have hb : 0 < p₁ * p₂ := mul_pos
      (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
    have hsource : r * s ∈ chenSiftedQuotientPrimeSource N (p₁ * p₂) (p₂ : ℝ) :=
      (currentChenSeventh_sifted_mem_iff hb _).mpr
        ⟨hlt, hP, (currentChenSeventh_rough_prime_mul_iff hr hs hrs).mpr
          (by exact_mod_cast hcut)⟩
    have hraw := (Finset.mem_filter.mp hsource).1
    have hrc := currentChenSeventh_prime_factor_mem_carrier hb hraw hr (dvd_mul_right r s)
    have hsc := currentChenSeventh_prime_factor_mem_carrier hb hraw hs (dvd_mul_left s r)
    exact ⟨⟨⟨h₁, h₂⟩, hD, h₁₂, hcap⟩, ⟨hrc, hsc⟩, hcut, hrs, hsource⟩

private def currentChenSeventhSemiprimePairs (N : ℕ) (t : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N).filter fun u =>
    t.2 ≤ u.1 ∧ u.1 ≤ u.2 ∧
      u.1 * u.2 ∈ chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)

private theorem currentChenSeventh_pairs_mul_injective {N : ℕ} {t a c : ℕ × ℕ}
    (ha : a ∈ currentChenSeventhSemiprimePairs N t)
    (hc : c ∈ currentChenSeventhSemiprimePairs N t)
    (hmul : a.1 * a.2 = c.1 * c.2) : a = c := by
  obtain ⟨hac, _hca, haorder, _haF⟩ := Finset.mem_filter.mp ha
  obtain ⟨hcc, _hccut, hcorder, _hcF⟩ := Finset.mem_filter.mp hc
  obtain ⟨ha₁, ha₂⟩ := Finset.mem_product.mp hac
  obtain ⟨hc₁, hc₂⟩ := Finset.mem_product.mp hcc
  obtain ⟨hfirst, hsecond⟩ := ordered_prime_factors_unique
    (mem_chenAdditivePrimeCarrier.mp ha₁).2.1
    (mem_chenAdditivePrimeCarrier.mp ha₂).2.1
    (mem_chenAdditivePrimeCarrier.mp hc₁).2.1
    (mem_chenAdditivePrimeCarrier.mp hc₂).2.1 haorder hcorder hmul
  exact Prod.ext hfirst hsecond

private theorem currentChenSeventh_composite_eq_pairs_image {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) :
    (chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)).filter
        (fun q => q ≠ 1 ∧ ¬ Nat.Prime q) =
      (currentChenSeventhSemiprimePairs N t).image (fun u => u.1 * u.2) := by
  obtain ⟨hc, _hD, _h₁₂, _hcap⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc₁, hc₂⟩ := Finset.mem_product.mp hc
  have hb : 0 < t.1 * t.2 := mul_pos
    (mem_chenAdditivePrimeCarrier.mp hc₁).2.1.pos
    (mem_chenAdditivePrimeCarrier.mp hc₂).2.1.pos
  ext q
  constructor
  · intro hq
    obtain ⟨hqF, hqone, hqnotprime⟩ := Finset.mem_filter.mp hq
    rcases (currentChenUpsilon7_quotient_classification ht hqF).2 with
      hone | hprime | ⟨r, s, hr, hs, hcut, hrs, hprod⟩
    · exact (hqone hone).elim
    · exact (hqnotprime hprime).elim
    · have hraw := (Finset.mem_filter.mp hqF).1
      have hrd : r ∣ q := by
        rw [hprod]
        exact dvd_mul_right r s
      have hsd : s ∣ q := by
        rw [hprod]
        exact dvd_mul_left s r
      have hrc := currentChenSeventh_prime_factor_mem_carrier hb hraw hr hrd
      have hsc := currentChenSeventh_prime_factor_mem_carrier hb hraw hs hsd
      refine Finset.mem_image.mpr ⟨(r, s), ?_, hprod.symm⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hrc, hsc⟩, hcut, hrs, by simpa only [hprod] using hqF⟩
  · intro hq
    obtain ⟨⟨r, s⟩, hpairs, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hc, _hcut, _hrs, hF⟩ := Finset.mem_filter.mp hpairs
    obtain ⟨hrc, hsc⟩ := Finset.mem_product.mp hc
    have hr := (mem_chenAdditivePrimeCarrier.mp hrc).2.1
    have hs := (mem_chenAdditivePrimeCarrier.mp hsc).2.1
    have hprod : 4 ≤ r * s := Nat.mul_le_mul hr.two_le hs.two_le
    have hnonunit : r * s ≠ 1 :=
      ne_of_gt (lt_of_lt_of_le (by decide : 1 < 4) hprod)
    exact Finset.mem_filter.mpr
      ⟨hF, hnonunit, Nat.not_prime_mul hr.ne_one hs.ne_one⟩

private theorem currentChenSeventh_row_card_partition {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) :
    let F := chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)
    F.card = (F.filter Nat.Prime).card +
      (currentChenSeventhSemiprimePairs N t).card + if 1 ∈ F then 1 else 0 := by
  intro F
  let G := F.filter (fun q => ¬ Nat.Prime q)
  have hunitset : G.filter (fun q => q = 1) = if 1 ∈ F then {1} else ∅ := by
    ext q
    by_cases hq : q = 1
    · subst q
      by_cases hu : 1 ∈ F <;> simp [G, hu, Nat.not_prime_one]
    · by_cases hu : 1 ∈ F <;> simp [hq, hu]
  have hcompset : G.filter (fun q => q ≠ 1) =
      F.filter (fun q => q ≠ 1 ∧ ¬ Nat.Prime q) := by
    ext q
    simp only [G, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq, hnot⟩, hneq⟩
      exact ⟨hq, hneq, hnot⟩
    · rintro ⟨hq, hneq, hnot⟩
      exact ⟨⟨hq, hnot⟩, hneq⟩
  have hcompcard : (G.filter (fun q => q ≠ 1)).card =
      (currentChenSeventhSemiprimePairs N t).card := by
    rw [hcompset, currentChenSeventh_composite_eq_pairs_image ht]
    apply Finset.card_image_of_injOn
    intro a ha c hc heq
    exact currentChenSeventh_pairs_mul_injective ha hc heq
  have hunitcard : (G.filter (fun q => q = 1)).card = if 1 ∈ F then 1 else 0 := by
    rw [hunitset]
    by_cases hu : 1 ∈ F <;> simp only [hu, if_true, if_false,
      Finset.card_singleton, Finset.card_empty]
  have hprimepart := Finset.card_filter_add_card_filter_not (s := F) Nat.Prime
  change (F.filter Nat.Prime).card + G.card = F.card at hprimepart
  have hunitpart := Finset.card_filter_add_card_filter_not (s := G) (fun q => q = 1)
  rw [hunitcard, hcompcard] at hunitpart
  omega

/-- The original seventh Upsilon splits exactly into its prime, ordered
semiprime and unit fibres. No mean bound or branch omission occurs. -/
theorem currentChenUpsilon7_eq_primeTriples_add_semiprimeQuadruples_add_unitFibres
    (N : ℕ) :
    currentChenUpsilon7 N =
      ((currentChenUpsilon7PrimeTriples N).card : ℝ) +
        ((currentChenUpsilon7SemiprimeQuadruples N).card : ℝ) +
        ((currentChenUpsilon7UnitFibres N).card : ℝ) := by
  rw [currentChenUpsilon7_eq_siftedQuotientPrimeSource]
  have hprimecount : ((currentChenUpsilon7PrimeTriples N).card : ℝ) =
      ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
        (((chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)).filter Nat.Prime).card : ℝ) := by
    simp only [currentChenUpsilon7PrimeTriples, Finset.card_sigma, Nat.cast_sum]
  have hsemicount : ((currentChenUpsilon7SemiprimeQuadruples N).card : ℝ) =
      ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
        ((currentChenSeventhSemiprimePairs N t).card : ℝ) := by
    simp only [currentChenUpsilon7SemiprimeQuadruples, currentChenSeventhSemiprimePairs,
      Finset.card_sigma, Nat.cast_sum]
  have hunitcount : ((currentChenUpsilon7UnitFibres N).card : ℝ) =
      ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
        if 1 ∈ chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)
          then (1 : ℝ) else 0 := by
    simp only [currentChenUpsilon7UnitFibres, Finset.card_eq_sum_ones,
      Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hprimecount, hsemicount, hunitcount]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  exact_mod_cast currentChenSeventh_row_card_partition ht

end

end ImbalancedChen
