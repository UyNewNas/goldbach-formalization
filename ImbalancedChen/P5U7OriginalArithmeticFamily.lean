import ImbalancedChen.CurrentChenUpsilon7LargePrimeSwitch

/-!
# Original U7 positive arithmetic source, with the additive-prime gate removed

All arithmetic labels remain marked.  The three-prime and ordered four-prime
families below do not test primality of N minus their physical product.
Their product weight counts fibres, so no multiplicity is lost by passing
to the product variable.  The literal current U7 is recovered exactly by
the prime gate, plus the unit branch; the large-original-prime version pays
the actual existing small-prime/unit error budget with coefficient two.

No ordinary factor-eight estimate, PP licence, distribution theorem,
source-mass asymptotic, or sharp U7 mean is asserted. Source only/uncompiled.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical

abbrev P5U7ThreeLabel := Σ _ : ℕ × ℕ, ℕ
abbrev P5U7FourLabel := Σ _ : ℕ × ℕ, ℕ × ℕ

def p5U7ThreeProduct (x : P5U7ThreeLabel) : ℕ := x.1.1 * x.1.2 * x.2
def p5U7FourProduct (x : P5U7FourLabel) : ℕ := x.1.1 * x.1.2 * (x.2.1 * x.2.2)

/-- No primality condition on the additive complement occurs here. -/
def p5U7ArithmeticThree (N : ℕ) : Finset P5U7ThreeLabel :=
  (chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))).sigma fun t =>
    (chenAdditivePrimeCarrier N).filter fun q => t.2 ≤ q ∧ t.1 * t.2 * q < N

/-- The order is p1<p2<=r<=s. Equal adjacent terminal factors are retained. -/
def p5U7ArithmeticFour (N : ℕ) : Finset P5U7FourLabel :=
  (chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))).sigma fun t =>
    (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N).filter fun u =>
      t.2 ≤ u.1 ∧ u.1 ≤ u.2 ∧ t.1 * t.2 * (u.1 * u.2) < N

theorem p5U7ArithmeticThree_data {N : ℕ} {x : P5U7ThreeLabel}
    (hx : x ∈ p5U7ArithmeticThree N) :
    x.1 ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)) ∧
      Nat.Prime x.1.1 ∧ Nat.Prime x.1.2 ∧ Nat.Prime x.2 ∧
      x.1.1 < x.1.2 ∧ x.1.2 ≤ x.2 ∧
      0 < p5U7ThreeProduct x ∧ p5U7ThreeProduct x < N ∧
      Nat.Coprime (p5U7ThreeProduct x) N := by
  obtain ⟨ht, hq⟩ := Finset.mem_sigma.mp hx
  obtain ⟨hc, _hD, ho, _hcap⟩ := Finset.mem_filter.mp ht
  obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hc
  obtain ⟨hqc, hwall, hlt⟩ := Finset.mem_filter.mp hq
  have hp₁ := mem_chenAdditivePrimeCarrier.mp h₁
  have hp₂ := mem_chenAdditivePrimeCarrier.mp h₂
  have hpq := mem_chenAdditivePrimeCarrier.mp hqc
  exact ⟨ht, hp₁.2.1, hp₂.2.1, hpq.2.1, ho, hwall,
    mul_pos (mul_pos hp₁.2.1.pos hp₂.2.1.pos) hpq.2.1.pos, hlt,
    (hp₁.2.2.mul_left hp₂.2.2).mul_left hpq.2.2⟩

theorem p5U7ArithmeticFour_data {N : ℕ} {x : P5U7FourLabel}
    (hx : x ∈ p5U7ArithmeticFour N) :
    x.1 ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)) ∧
      Nat.Prime x.1.1 ∧ Nat.Prime x.1.2 ∧ Nat.Prime x.2.1 ∧ Nat.Prime x.2.2 ∧
      x.1.1 < x.1.2 ∧ x.1.2 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2 ∧
      0 < p5U7FourProduct x ∧ p5U7FourProduct x < N ∧
      Nat.Coprime (p5U7FourProduct x) N := by
  obtain ⟨ht, hrs⟩ := Finset.mem_sigma.mp hx
  obtain ⟨hc, _hD, ho, _hcap⟩ := Finset.mem_filter.mp ht
  obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hc
  obtain ⟨hrsc, hwall, hrs, hlt⟩ := Finset.mem_filter.mp hrs
  obtain ⟨hrc, hsc⟩ := Finset.mem_product.mp hrsc
  have hp₁ := mem_chenAdditivePrimeCarrier.mp h₁
  have hp₂ := mem_chenAdditivePrimeCarrier.mp h₂
  have hpr := mem_chenAdditivePrimeCarrier.mp hrc
  have hps := mem_chenAdditivePrimeCarrier.mp hsc
  exact ⟨ht, hp₁.2.1, hp₂.2.1, hpr.2.1, hps.2.1, ho, hwall, hrs,
    mul_pos (mul_pos hp₁.2.1.pos hp₂.2.1.pos) (mul_pos hpr.2.1.pos hps.2.1.pos), hlt,
    (hp₁.2.2.mul_left hp₂.2.2).mul_left (hpr.2.2.mul_left hps.2.2)⟩

theorem p5U7ArithmeticThree_original_walls {N : ℕ} {x : P5U7ThreeLabel}
    (hx : x ∈ p5U7ArithmeticThree N) :
    (N : ℝ) ^ (59 / 250 : ℝ) ≤ (x.1.1 : ℝ) ∧ x.1.1 < x.1.2 ∧ x.1.2 ≤ x.2 ∧
      (x.1.2 : ℝ) < Real.sqrt ((N : ℝ) / (x.1.1 : ℝ)) := by
  obtain ⟨ht, hq⟩ := Finset.mem_sigma.mp hx
  obtain ⟨_hc, hD, ho, hcap⟩ := Finset.mem_filter.mp ht
  obtain ⟨_hqc, hwall, _hlt⟩ := Finset.mem_filter.mp hq
  exact ⟨hD, ho, hwall, hcap⟩

theorem p5U7ArithmeticFour_original_walls {N : ℕ} {x : P5U7FourLabel}
    (hx : x ∈ p5U7ArithmeticFour N) :
    (N : ℝ) ^ (59 / 250 : ℝ) ≤ (x.1.1 : ℝ) ∧ x.1.1 < x.1.2 ∧
      x.1.2 ≤ x.2.1 ∧ x.1.2 ≤ x.2.2 ∧
      (x.1.2 : ℝ) < Real.sqrt ((N : ℝ) / (x.1.1 : ℝ)) := by
  obtain ⟨ht, hrs⟩ := Finset.mem_sigma.mp hx
  obtain ⟨_hc, hD, ho, hcap⟩ := Finset.mem_filter.mp ht
  obtain ⟨_hrsc, hwall, horder, _hlt⟩ := Finset.mem_filter.mp hrs
  exact ⟨hD, ho, hwall, hwall.trans horder, hcap⟩

private theorem p5U7Arithmetic_complement_carrier {N m : ℕ}
    (hmpos : 0 < m) (hmN : m < N) (hcop : Nat.Coprime m N)
    (hprime : Nat.Prime (N - m)) : N - m ∈ chenAdditivePrimeCarrier N := by
  exact mem_chenAdditivePrimeCarrier.mpr
    ⟨by omega, hprime, (Nat.coprime_self_sub_left hmN.le).mpr hcop⟩

/-- Exact recovery of the original prime branch by its only removed gate. -/
theorem p5U7_originalPrimeTriples_eq_gated_arithmetic (N : ℕ) :
    currentChenUpsilon7PrimeTriples N =
      (p5U7ArithmeticThree N).filter (fun x => Nat.Prime (N - p5U7ThreeProduct x)) := by
  ext x
  rcases x with ⟨⟨p₁, p₂⟩, q⟩
  constructor
  · intro hx
    have ht := (Finset.mem_sigma.mp hx).1
    obtain ⟨_h₁, _h₂, _hD, _ho, _hcap, hq, hwall, hlt, hP⟩ :=
      mem_currentChenUpsilon7PrimeTriples_iff.mp hx
    have hdiv : q ∣ N - (N - p₁ * p₂ * q) := by
      rw [Nat.sub_sub_self hlt.le]
      exact dvd_mul_left q (p₁ * p₂)
    have hqc := chen_prime_dvd_receiver_mem_additiveCarrier hP hq hdiv
    exact Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr
      ⟨ht, Finset.mem_filter.mpr ⟨hqc, hwall, hlt⟩⟩,
      (mem_chenAdditivePrimeCarrier.mp hP).2.1⟩
  · intro hx
    obtain ⟨hxA, hprime⟩ := Finset.mem_filter.mp hx
    obtain ⟨ht, hq⟩ := Finset.mem_sigma.mp hxA
    obtain ⟨hc, hD, ho, hcap⟩ := Finset.mem_filter.mp ht
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hc
    obtain ⟨hqc, hwall, hlt⟩ := Finset.mem_filter.mp hq
    have hdata := p5U7ArithmeticThree_data hxA
    have hpos := hdata.2.2.2.2.2.2.1
    have hcop := hdata.2.2.2.2.2.2.2.2
    have hP := p5U7Arithmetic_complement_carrier hpos hlt hcop hprime
    exact mem_currentChenUpsilon7PrimeTriples_iff.mpr
      ⟨h₁, h₂, hD, ho, hcap, (mem_chenAdditivePrimeCarrier.mp hqc).2.1,
        hwall, hlt, hP⟩

/-- Exact recovery of the original ordered semiprime branch. -/
theorem p5U7_originalSemiprimeQuadruples_eq_gated_arithmetic (N : ℕ) :
    currentChenUpsilon7SemiprimeQuadruples N =
      (p5U7ArithmeticFour N).filter (fun x => Nat.Prime (N - p5U7FourProduct x)) := by
  ext x
  rcases x with ⟨⟨p₁, p₂⟩, ⟨r, s⟩⟩
  constructor
  · intro hx
    have ht := (Finset.mem_sigma.mp hx).1
    have hrs := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).1
    obtain ⟨_h₁, _h₂, _hD, _ho, _hcap, _hr, _hs, hwall, horder, hlt, hP⟩ :=
      mem_currentChenUpsilon7SemiprimeQuadruples_iff.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr
      ⟨ht, Finset.mem_filter.mpr ⟨hrs, hwall, horder, hlt⟩⟩,
      (mem_chenAdditivePrimeCarrier.mp hP).2.1⟩
  · intro hx
    obtain ⟨hxA, hprime⟩ := Finset.mem_filter.mp hx
    obtain ⟨ht, hrs⟩ := Finset.mem_sigma.mp hxA
    obtain ⟨hc, hD, ho, hcap⟩ := Finset.mem_filter.mp ht
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hc
    obtain ⟨hrsc, hwall, horder, hlt⟩ := Finset.mem_filter.mp hrs
    obtain ⟨hrc, hsc⟩ := Finset.mem_product.mp hrsc
    have hdata := p5U7ArithmeticFour_data hxA
    have hpos := hdata.2.2.2.2.2.2.2.2.1
    have hcop := hdata.2.2.2.2.2.2.2.2.2.2
    have hP := p5U7Arithmetic_complement_carrier hpos hlt hcop hprime
    exact mem_currentChenUpsilon7SemiprimeQuadruples_iff.mpr
      ⟨h₁, h₂, hD, ho, hcap, (mem_chenAdditivePrimeCarrier.mp hrc).2.1,
        (mem_chenAdditivePrimeCarrier.mp hsc).2.1, hwall, horder, hlt, hP⟩

/-- No receiver prime is used for the original five-power argument. -/
theorem p5U7Arithmetic_rough_cofactor_lt_cube {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)))
    {q : ℕ} (hlt : t.1 * t.2 * q < N) : q < t.2 ^ 3 := by
  obtain ⟨hc, hD, h₁₂, _hcap⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc₁, hc₂⟩ := Finset.mem_product.mp hc
  have hp₁ := (mem_chenAdditivePrimeCarrier.mp hc₁).2.1
  have hN : (1 : ℝ) < N := by
    exact_mod_cast lt_trans hp₁.one_lt (mem_chenAdditivePrimeCarrier.mp hc₁).1
  have hDpow : ((N : ℝ) ^ (59 / 250 : ℝ)) ^ 5 = (N : ℝ) ^ (59 / 50 : ℝ) := by
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
  have hoR : (t.1 : ℝ) ≤ t.2 := by exact_mod_cast h₁₂.le
  have hfirst : (t.1 : ℝ) ^ 5 ≤ (t.1 : ℝ) * (t.2 : ℝ) ^ 4 := by
    calc
      _ = (t.1 : ℝ) * (t.1 : ℝ) ^ 4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hoR 4) (Nat.cast_nonneg _)
  have hNprod : (N : ℝ) < (t.1 : ℝ) * (t.2 : ℝ) ^ 4 :=
    hNpow.trans_le (hDfive.trans hfirst)
  by_contra hnot
  have hlow : t.2 ^ 3 ≤ q := Nat.le_of_not_gt hnot
  have hlowR : (t.2 : ℝ) ^ 3 ≤ (q : ℝ) := by exact_mod_cast hlow
  have hltR : (t.1 : ℝ) * (t.2 : ℝ) * (q : ℝ) < (N : ℝ) := by exact_mod_cast hlt
  have hprod : (t.1 : ℝ) * (t.2 : ℝ) ^ 4 ≤ (t.1 : ℝ) * (t.2 : ℝ) * (q : ℝ) := by
    calc
      _ = ((t.1 : ℝ) * (t.2 : ℝ)) * (t.2 : ℝ) ^ 3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlowR
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact (not_lt_of_ge hprod) (hltR.trans hNprod)

private theorem p5U7Arithmetic_rough_cube_classification {y q : ℕ}
    (hq : 0 < q) (hrough : ChenPrimeRough (y : ℝ) q) (hsmall : q < y ^ 3) :
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
  have hyr : y ≤ r := by exact_mod_cast hrough r hr (Nat.minFac_dvd q)
  have hspos : 0 < s := hr.pos.trans_le hrs
  have hsone : s ≠ 1 := by have htwo := hr.two_le; omega
  have hs : Nat.Prime s := by
    by_contra hsnot
    have ht : Nat.Prime (Nat.minFac s) := Nat.minFac_prime hsone
    have hsd : s ∣ q := by rw [← hmul]; exact dvd_mul_left s r
    have hyt : y ≤ Nat.minFac s := by
      exact_mod_cast hrough (Nat.minFac s) ht ((Nat.minFac_dvd s).trans hsd)
    have hysq : y ^ 2 ≤ s :=
      (pow_le_pow_left' hyt 2).trans (Nat.minFac_sq_le_self hspos hsnot)
    have hcube : y ^ 3 ≤ q := by
      calc
        _ = y * y ^ 2 := by ring
        _ ≤ r * s := Nat.mul_le_mul hyr hysq
        _ = q := hmul
    exact (not_le_of_gt hsmall) hcube
  exact Or.inr (Or.inr ⟨r, s, hr, hs, hyr, hrs, hmul.symm⟩)

/-- Actual original roughness with no additive-prime premise has no higher
branch. This is the supplier strengthening absent from the gated source. -/
theorem p5U7Arithmetic_rough_cofactor_classification {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)))
    {q : ℕ} (hq : 0 < q) (hlt : t.1 * t.2 * q < N)
    (hrough : ChenPrimeRough (t.2 : ℝ) q) :
    q = 1 ∨ Nat.Prime q ∨ ∃ r s : ℕ,
      Nat.Prime r ∧ Nat.Prime s ∧ t.2 ≤ r ∧ r ≤ s ∧ q = r * s := by
  exact p5U7Arithmetic_rough_cube_classification hq hrough
    (p5U7Arithmetic_rough_cofactor_lt_cube ht hlt)

private theorem p5U7Arithmetic_factor_carrier {N q r : ℕ}
    (hq : 0 < q) (hqN : q < N) (hqcop : Nat.Coprime q N)
    (hr : Nat.Prime r) (hrq : r ∣ q) : r ∈ chenAdditivePrimeCarrier N := by
  exact mem_chenAdditivePrimeCarrier.mpr
    ⟨(Nat.le_of_dvd hq hrq).trans_lt hqN, hr, hqcop.of_dvd_left hrq⟩

/-- A primitive, nonunit rough cofactor belongs to one of the actual ungated
labelled families, retaining its original marked pair. -/
theorem p5U7Arithmetic_rough_nonunit_mem_three_or_four {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)))
    {q : ℕ} (hq : 0 < q) (hqone : q ≠ 1) (hqcop : Nat.Coprime q N)
    (hlt : t.1 * t.2 * q < N) (hrough : ChenPrimeRough (t.2 : ℝ) q) :
    (⟨t, q⟩ : P5U7ThreeLabel) ∈ p5U7ArithmeticThree N ∨
      ∃ r s : ℕ, q = r * s ∧
        (⟨t, (r,s)⟩ : P5U7FourLabel) ∈ p5U7ArithmeticFour N := by
  obtain ⟨hc, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hc
  have hb : 0 < t.1 * t.2 := mul_pos
    (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
  have hqle : q ≤ (t.1 * t.2) * q := by
    calc
      q = 1 * q := (one_mul q).symm
      _ ≤ _ := Nat.mul_le_mul_right q (by omega)
  have hqN : q < N := hqle.trans_lt hlt
  rcases p5U7Arithmetic_rough_cofactor_classification ht hq hlt hrough with
    hone | hprime | ⟨r, s, hr, hs, hcut, hrs, hprod⟩
  · exact (hqone hone).elim
  · have hqc := mem_chenAdditivePrimeCarrier.mpr ⟨hqN, hprime, hqcop⟩
    have hwall : t.2 ≤ q := by exact_mod_cast hrough q hprime (dvd_refl q)
    exact Or.inl (Finset.mem_sigma.mpr ⟨ht, Finset.mem_filter.mpr ⟨hqc, hwall, hlt⟩⟩)
  · have hrd : r ∣ q := by rw [hprod]; exact dvd_mul_right r s
    have hsd : s ∣ q := by rw [hprod]; exact dvd_mul_left s r
    have hrc := p5U7Arithmetic_factor_carrier hq hqN hqcop hr hrd
    have hsc := p5U7Arithmetic_factor_carrier hq hqN hqcop hs hsd
    exact Or.inr ⟨r, s, hprod, Finset.mem_sigma.mpr ⟨ht,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hrc,hsc⟩, hcut, hrs,
        by simpa only [hprod] using hlt⟩⟩⟩

/-- Product-fibre cardinalities preserve ALL marked label multiplicities. -/
def p5U7ArithmeticProductWeight (N m : ℕ) : ℝ :=
  (((p5U7ArithmeticThree N).filter (fun x => p5U7ThreeProduct x = m)).card : ℝ) +
    (((p5U7ArithmeticFour N).filter (fun x => p5U7FourProduct x = m)).card : ℝ)

theorem p5U7ArithmeticProductWeight_nonneg (N m : ℕ) :
    0 ≤ p5U7ArithmeticProductWeight N m := by
  exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Positive product weight has an actual marked three- or four-prime
witness, rather than a guessed unlabelled squarefree support. -/
theorem p5U7ArithmeticProductWeight_pos_labelled_support {N m : ℕ}
    (hm : 0 < p5U7ArithmeticProductWeight N m) :
    (∃ x ∈ p5U7ArithmeticThree N, p5U7ThreeProduct x = m) ∨
      ∃ x ∈ p5U7ArithmeticFour N, p5U7FourProduct x = m := by
  have hex :
      ((p5U7ArithmeticThree N).filter (fun x => p5U7ThreeProduct x = m)).Nonempty ∨
      ((p5U7ArithmeticFour N).filter (fun x => p5U7FourProduct x = m)).Nonempty := by
    by_contra hnot
    have hn₃ : ¬((p5U7ArithmeticThree N).filter
        (fun x => p5U7ThreeProduct x = m)).Nonempty := fun h₃ => hnot (Or.inl h₃)
    have hn₄ : ¬((p5U7ArithmeticFour N).filter
        (fun x => p5U7FourProduct x = m)).Nonempty := fun h₄ => hnot (Or.inr h₄)
    have h₃ := Finset.not_nonempty_iff_eq_empty.mp hn₃
    have h₄ := Finset.not_nonempty_iff_eq_empty.mp hn₄
    simp only [p5U7ArithmeticProductWeight, h₃, h₄, Finset.card_empty, Nat.cast_zero,
      add_zero, lt_self_iff_false] at hm
  rcases hex with h₃ | h₄
  · obtain ⟨x, hx⟩ := h₃
    obtain ⟨hx, heq⟩ := Finset.mem_filter.mp hx
    exact Or.inl ⟨x, hx, heq⟩
  · obtain ⟨x, hx⟩ := h₄
    obtain ⟨hx, heq⟩ := Finset.mem_filter.mp hx
    exact Or.inr ⟨x, hx, heq⟩

theorem p5U7ArithmeticProductWeight_pos_support {N m : ℕ}
    (hm : 0 < p5U7ArithmeticProductWeight N m) :
    0 < m ∧ m < N ∧ Nat.Coprime m N := by
  rcases p5U7ArithmeticProductWeight_pos_labelled_support hm with
    ⟨x, hx, heq⟩ | ⟨x, hx, heq⟩
  · have hd := p5U7ArithmeticThree_data hx
    simpa only [heq] using hd.2.2.2.2.2.2
  · have hd := p5U7ArithmeticFour_data hx
    simpa only [heq] using hd.2.2.2.2.2.2.2.2

theorem p5U7ArithmeticProductWeight_ne_zero_support {N m : ℕ}
    (hm : p5U7ArithmeticProductWeight N m ≠ 0) :
    0 < m ∧ m < N ∧ Nat.Coprime m N := by
  exact p5U7ArithmeticProductWeight_pos_support
    (lt_of_le_of_ne (p5U7ArithmeticProductWeight_nonneg N m) hm.symm)

private theorem p5U7Arithmetic_fibre_sum {α : Type*} [DecidableEq α]
    (N : ℕ) (S : Finset α) (f : α → ℕ) (hN : ∀ x ∈ S, f x < N) (H : ℕ → ℝ) :
    (∑ m ∈ Finset.range N, (((S.filter (fun x => f x = m)).card : ℝ) * H m)) =
      ∑ x ∈ S, H (f x) := by
  have hmap : ∀ x ∈ S, f x ∈ Finset.range N := fun x hx => Finset.mem_range.mpr (hN x hx)
  simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_fiberwise_of_maps_to' hmap H

/-- Finite Fubini for arbitrary signed product tests, with the exact
cardinality weight and without product injectivity or squarefreeness. -/
theorem p5U7Arithmetic_product_weighted_Fubini (N : ℕ) (H : ℕ → ℝ) :
    (∑ m ∈ Finset.range N, p5U7ArithmeticProductWeight N m * H m) =
      (∑ x ∈ p5U7ArithmeticThree N, H (p5U7ThreeProduct x)) +
        ∑ x ∈ p5U7ArithmeticFour N, H (p5U7FourProduct x) := by
  simp only [p5U7ArithmeticProductWeight, add_mul, Finset.sum_add_distrib]
  rw [p5U7Arithmetic_fibre_sum N _ _
    (fun x hx => (p5U7ArithmeticThree_data hx).2.2.2.2.2.2.2.1) H,
    p5U7Arithmetic_fibre_sum N _ _
    (fun x hx => (p5U7ArithmeticFour_data hx).2.2.2.2.2.2.2.2.2.1) H]

theorem p5U7Arithmetic_product_weight_mass (N : ℕ) :
    (∑ m ∈ Finset.range N, p5U7ArithmeticProductWeight N m) =
      ((p5U7ArithmeticThree N).card : ℝ) + ((p5U7ArithmeticFour N).card : ℝ) := by
  simpa only [mul_one, Finset.sum_const, nsmul_eq_mul] using
    p5U7Arithmetic_product_weighted_Fubini N (fun _ => 1)

/-- The same no-prime-gate positive weight gives the exact progression
source required before a signed physical-distribution estimate. -/
theorem p5U7Arithmetic_progression_Fubini (N d : ℕ) :
    (∑ m ∈ Finset.range N,
      if Nat.ModEq d m N then p5U7ArithmeticProductWeight N m else 0) =
      (∑ x ∈ p5U7ArithmeticThree N,
        if Nat.ModEq d (p5U7ThreeProduct x) N then (1 : ℝ) else 0) +
      ∑ x ∈ p5U7ArithmeticFour N,
        if Nat.ModEq d (p5U7FourProduct x) N then (1 : ℝ) else 0 := by
  have h := p5U7Arithmetic_product_weighted_Fubini N
    (fun m => if Nat.ModEq d m N then (1 : ℝ) else 0)
  convert h using 1
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hAP : Nat.ModEq d m N <;> simp only [hAP, if_true, if_false, mul_one, mul_zero]

def p5U7ArithmeticWeightedPrimeGate (N : ℕ) (G : ℕ → Prop) : ℝ :=
  ∑ m ∈ Finset.range N,
    if Nat.Prime (N - m) ∧ G m then p5U7ArithmeticProductWeight N m else 0

private theorem p5U7Arithmetic_real_indicator_count {α : Type*} [DecidableEq α]
    (S : Finset α) (P : α → Prop) :
    (∑ x ∈ S, if P x then (1 : ℝ) else 0) = ((S.filter P).card : ℝ) := by
  rw [← Finset.sum_filter]
  simp

/-- Every additional product gate, including the large-original-P wall,
is transported exactly between weighted products and original labels. -/
theorem p5U7Arithmetic_weighted_prime_gate_eq_labelled (N : ℕ) (G : ℕ → Prop) :
    p5U7ArithmeticWeightedPrimeGate N G =
      (((currentChenUpsilon7PrimeTriples N).filter (fun x => G (p5U7ThreeProduct x))).card : ℝ) +
        (((currentChenUpsilon7SemiprimeQuadruples N).filter
          (fun x => G (p5U7FourProduct x))).card : ℝ) := by
  have hF := p5U7Arithmetic_product_weighted_Fubini N
    (fun m => if Nat.Prime (N - m) ∧ G m then (1 : ℝ) else 0)
  have hgate : p5U7ArithmeticWeightedPrimeGate N G =
      ∑ m ∈ Finset.range N, p5U7ArithmeticProductWeight N m *
        (if Nat.Prime (N - m) ∧ G m then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hg : Nat.Prime (N - m) ∧ G m <;> simp only [hg, if_true, if_false, mul_one, mul_zero]
  rw [hgate, hF, p5U7Arithmetic_real_indicator_count, p5U7Arithmetic_real_indicator_count]
  rw [p5U7_originalPrimeTriples_eq_gated_arithmetic,
    p5U7_originalSemiprimeQuadruples_eq_gated_arithmetic]
  have hthree : ((p5U7ArithmeticThree N).filter
      (fun x => Nat.Prime (N - p5U7ThreeProduct x) ∧ G (p5U7ThreeProduct x))) =
      ((p5U7ArithmeticThree N).filter (fun x => Nat.Prime (N - p5U7ThreeProduct x))).filter
        (fun x => G (p5U7ThreeProduct x)) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hp, hG⟩
      exact ⟨⟨hx, hp⟩, hG⟩
    · rintro ⟨⟨hx, hp⟩, hG⟩
      exact ⟨hx, hp, hG⟩
  have hfour : ((p5U7ArithmeticFour N).filter
      (fun x => Nat.Prime (N - p5U7FourProduct x) ∧ G (p5U7FourProduct x))) =
      ((p5U7ArithmeticFour N).filter (fun x => Nat.Prime (N - p5U7FourProduct x))).filter
        (fun x => G (p5U7FourProduct x)) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hp, hG⟩
      exact ⟨⟨hx, hp⟩, hG⟩
    · rintro ⟨⟨hx, hp⟩, hG⟩
      exact ⟨hx, hp, hG⟩
  rw [hthree, hfour]

theorem p5U7_original_eq_weighted_prime_source_add_unit (N : ℕ) :
    currentChenUpsilon7 N = p5U7ArithmeticWeightedPrimeGate N (fun _ => True) +
      ((currentChenUpsilon7UnitFibres N).card : ℝ) := by
  rw [p5U7Arithmetic_weighted_prime_gate_eq_labelled,
    currentChenUpsilon7_eq_primeTriples_add_semiprimeQuadruples_add_unitFibres]
  simp only [Finset.filter_true]

def p5U7ArithmeticLargePrimeSource (N : ℕ) : ℝ :=
  p5U7ArithmeticWeightedPrimeGate N (fun m =>
    (N : ℝ) ^ (1 / 5 : ℝ) < ((N - m : ℕ) : ℝ))

def p5U7ArithmeticSmallUnitError (N : ℕ) : ℝ :=
  ((currentChenUpsilon7UnitFibres N).card : ℝ) +
    (((currentChenUpsilon7PrimeTriples N).filter (fun x =>
      ((N - p5U7ThreeProduct x : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ))).card : ℝ) +
    (((currentChenUpsilon7SemiprimeQuadruples N).filter (fun x =>
      ((N - p5U7FourProduct x : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ))).card : ℝ)

theorem p5U7_original_eq_large_weighted_source_add_error (N : ℕ) :
    currentChenUpsilon7 N = p5U7ArithmeticLargePrimeSource N + p5U7ArithmeticSmallUnitError N := by
  have hp := Finset.card_filter_add_card_filter_not (s := currentChenUpsilon7PrimeTriples N)
    (fun x => ((N - p5U7ThreeProduct x : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ))
  have hs := Finset.card_filter_add_card_filter_not (s := currentChenUpsilon7SemiprimeQuadruples N)
    (fun x => ((N - p5U7FourProduct x : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ))
  have hpR := congrArg (fun n : ℕ => (n : ℝ)) hp
  have hsR := congrArg (fun n : ℕ => (n : ℝ)) hs
  simp only [not_le, Nat.cast_add] at hpR hsR
  unfold p5U7ArithmeticLargePrimeSource
  rw [p5U7Arithmetic_weighted_prime_gate_eq_labelled,
    currentChenUpsilon7_eq_primeTriples_add_semiprimeQuadruples_add_unitFibres]
  unfold p5U7ArithmeticSmallUnitError
  linarith only [hpR, hsR]

theorem p5U7ArithmeticSmallUnitError_nonneg (N : ℕ) : 0 ≤ p5U7ArithmeticSmallUnitError N := by
  exact add_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem p5U7Arithmetic_eventually_error_budget (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, 2 * p5U7ArithmeticSmallUnitError N ≤ epsilon * singularNormalization N := by
  exact eventually_currentChenUpsilon7_unit_smallGoldbach_error_le epsilon hepsilon

theorem p5U7Arithmetic_eventually_original_le_weighted_source
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, 2 * currentChenUpsilon7 N ≤
      2 * p5U7ArithmeticLargePrimeSource N + epsilon * singularNormalization N := by
  filter_upwards [p5U7Arithmetic_eventually_error_budget epsilon hepsilon] with N hN
  rw [p5U7_original_eq_large_weighted_source_add_error]
  linarith only [hN]

end

end ImbalancedChen
