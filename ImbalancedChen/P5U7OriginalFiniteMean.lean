import ImbalancedChen.CurrentChenUpsilon7LargePrimeSwitch
import ImbalancedChen.ActualSmallRosser

/-!
# P5: the original seventh source and its signed finite upper sieve

This draft retains the literal `59/250` outer wall, the strict outer
square-root cap, the prime and ordered-semiprime branches (including
diagonals), and the coefficient two.  It adds the previously absent
prime-branch switch, then bounds both switched branches by *actual*
Rosser divisor sums on terminal-prime fibres with their ordered walls.

This is a finite prerequisite, not the missing sharp U7 mean.  No
asymptotic upper-density constant, physical distribution estimate, or
target-equivalent hypothesis is used.  In particular, this file does not
identify the resulting ordinary Rosser expression with the manuscript's
sharp original seventh coefficient.  That analytic comparison is open.

Source only: not compiled under the active execution prohibition.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical

/-- The physical progression source, with the prime test on the recovered
terminal factor and its inclusive ordered wall. -/
def p5U7OriginalAPSource (N a ell : ℕ) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).filter fun P =>
    a ∣ N - P ∧ Nat.Prime ((N - P) / a) ∧
      ell ≤ (N - P) / a ∧ (N : ℝ) ^ (1 / 5 : ℝ) < (P : ℝ)

/-- The original prime branch, switched at the actual modulus p₁*p₂. -/
def p5U7OriginalPrimeAPSum (N : ℕ) : ℝ :=
  ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
    ((p5U7OriginalAPSource N (t.1 * t.2) t.2).card : ℝ)

theorem p5U7Original_semiprimeAPSource_eq (N : ℕ)
    (x : Σ _ : ℕ × ℕ, ℕ) :
    currentChenUpsilon7LargePrimeSemiprimeAPSource N x =
      p5U7OriginalAPSource N (x.1.1 * x.1.2 * x.2) x.2 := by
  rfl

/-- Both physical prefix families are primitive at the target.  This
allows p₂ = r; squarefreeness is deliberately not part of the conclusion. -/
theorem p5U7Original_prefixes_coprime_target {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) :
    Nat.Coprime (t.1 * t.2) N ∧
      ∀ r ∈ (chenAdditivePrimeCarrier N).filter (fun r => t.2 ≤ r),
        Nat.Coprime (t.1 * t.2 * r) N := by
  obtain ⟨hc, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hc
  have hcop := (mem_chenAdditivePrimeCarrier.mp h₁).2.2.mul_left
    (mem_chenAdditivePrimeCarrier.mp h₂).2.2
  refine ⟨hcop, ?_⟩
  intro r hr
  exact hcop.mul_left
    (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hr).1).2.2

private theorem p5U7Original_AP_recover {N a ell P : ℕ} (ha : 0 < a)
    (hP : P ∈ p5U7OriginalAPSource N a ell) :
    a * ((N - P) / a) < N ∧
      N - a * ((N - P) / a) = P := by
  obtain ⟨hPc, hd, _hq, _hwall, _hlarge⟩ := Finset.mem_filter.mp hP
  have hPN := (mem_chenAdditivePrimeCarrier.mp hPc).1
  have hPpos := (mem_chenAdditivePrimeCarrier.mp hPc).2.1.pos
  have hmul := Nat.mul_div_cancel' hd
  constructor <;> omega

/-- Exact switching of the large-original-prime *prime* branch.  Together
with the existing semiprime equality this covers both genuine branches. -/
theorem p5U7Original_largePrime_prime_card_eq_APSum (N : ℕ) :
    (((currentChenUpsilon7PrimeTriples N).filter (fun x =>
      (N : ℝ) ^ (1 / 5 : ℝ) <
        ((N - x.1.1 * x.1.2 * x.2 : ℕ) : ℝ))).card : ℝ) =
      p5U7OriginalPrimeAPSum N := by
  let T := chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))
  have hcard : ((currentChenUpsilon7PrimeTriples N).filter (fun x =>
      (N : ℝ) ^ (1 / 5 : ℝ) <
        ((N - x.1.1 * x.1.2 * x.2 : ℕ) : ℝ))).card =
      (T.sigma (fun t => p5U7OriginalAPSource N (t.1 * t.2) t.2)).card := by
    refine Finset.card_bij'
      (fun x _ => ⟨x.1, N - x.1.1 * x.1.2 * x.2⟩)
      (fun y _ => ⟨y.1, (N - y.2) / (y.1.1 * y.1.2)⟩) ?_ ?_ ?_ ?_
    · rintro ⟨⟨p₁, p₂⟩, q⟩ hx
      obtain ⟨hx, hlarge⟩ := Finset.mem_filter.mp hx
      obtain ⟨h₁, h₂, _hD, _ho, _hc, hq, hwall, hlt, hP⟩ :=
        mem_currentChenUpsilon7PrimeTriples_iff.mp hx
      have ha := mul_pos (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
        (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
      have hreceiver : N - (N - p₁ * p₂ * q) = (p₁ * p₂) * q :=
        Nat.sub_sub_self hlt.le
      have hquot : (N - (N - p₁ * p₂ * q)) / (p₁ * p₂) = q := by
        rw [hreceiver]
        exact Nat.mul_div_cancel_left q ha
      apply Finset.mem_sigma.mpr
      refine ⟨(Finset.mem_sigma.mp hx).1, Finset.mem_filter.mpr ?_⟩
      refine ⟨hP, ?_, ?_, ?_, hlarge⟩
      · rw [hreceiver]
        exact dvd_mul_right _ _
      · simpa only [hquot] using hq
      · simpa only [hquot] using hwall
    · rintro ⟨⟨p₁, p₂⟩, P⟩ hy
      obtain ⟨ht, hP⟩ := Finset.mem_sigma.mp hy
      obtain ⟨hc, hD, ho, hcap⟩ := Finset.mem_filter.mp ht
      obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hc
      have ha := mul_pos (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
        (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
      obtain ⟨hPc, _hd, hq, hwall, hlarge⟩ := Finset.mem_filter.mp hP
      obtain ⟨hlt, hrecover⟩ := p5U7Original_AP_recover ha hP
      apply Finset.mem_filter.mpr
      refine ⟨mem_currentChenUpsilon7PrimeTriples_iff.mpr ?_, ?_⟩
      · exact ⟨h₁, h₂, hD, ho, hcap, hq, hwall, hlt,
          by simpa only [hrecover] using hPc⟩
      · simpa only [hrecover] using hlarge
    · rintro ⟨⟨p₁, p₂⟩, q⟩ hx
      obtain ⟨hx, _⟩ := Finset.mem_filter.mp hx
      obtain ⟨h₁, h₂, _hD, _ho, _hc, _hq, _hwall, hlt, _hP⟩ :=
        mem_currentChenUpsilon7PrimeTriples_iff.mp hx
      have ha := mul_pos (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
        (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
      have hquot : (N - (N - p₁ * p₂ * q)) / (p₁ * p₂) = q := by
        rw [Nat.sub_sub_self hlt.le]
        exact Nat.mul_div_cancel_left q ha
      simp only [hquot]
    · rintro ⟨⟨p₁, p₂⟩, P⟩ hy
      obtain ⟨ht, hP⟩ := Finset.mem_sigma.mp hy
      obtain ⟨hc, _⟩ := Finset.mem_filter.mp ht
      obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hc
      have ha := mul_pos (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
        (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
      have hrecover := (p5U7Original_AP_recover ha hP).2
      simp only [hrecover]
  have hreal := congrArg (fun n : ℕ => (n : ℝ)) hcard
  simpa only [T, Finset.card_sigma, Nat.cast_sum, p5U7OriginalPrimeAPSum] using hreal

/-- A native terminal-prime carrier.  It retains the inclusive ordered
wall and the strict product bound; the large receiver wall is physical. -/
def p5U7OriginalTerminalPrimeFibre (N a ell : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun q =>
    Nat.Prime q ∧ ell ≤ q ∧ a * q < N ∧
      (N : ℝ) ^ (1 / 5 : ℝ) < ((N - a * q : ℕ) : ℝ)

/-- Reversing the switch retains the original additive-prime test exactly. -/
theorem p5U7Original_APSource_card_eq_terminal (N a ell : ℕ) (ha : 0 < a) :
    (p5U7OriginalAPSource N a ell).card =
      ((p5U7OriginalTerminalPrimeFibre N a ell).filter
        (fun q => N - a * q ∈ chenAdditivePrimeCarrier N)).card := by
  refine Finset.card_bij' (fun P _ => (N - P) / a)
    (fun q _ => N - a * q) ?_ ?_ ?_ ?_
  · intro P hP
    obtain ⟨hPc, _hd, hq, hwall, hlarge⟩ := Finset.mem_filter.mp hP
    obtain ⟨hlt, hrecover⟩ := p5U7Original_AP_recover ha hP
    have hqle : (N - P) / a ≤ a * ((N - P) / a) := by
      calc
        (N - P) / a = 1 * ((N - P) / a) := (one_mul _).symm
        _ ≤ a * ((N - P) / a) := Nat.mul_le_mul_right _ (by omega)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hqle.trans_lt hlt),
      hq, hwall, hlt, ?_⟩, ?_⟩
    · simpa only [hrecover] using hlarge
    · simpa only [hrecover] using hPc
  · intro q hq
    obtain ⟨hqF, hPc⟩ := Finset.mem_filter.mp hq
    obtain ⟨_hqN, hprime, hwall, hlt, hlarge⟩ := Finset.mem_filter.mp hqF
    have hreceiver : N - (N - a * q) = a * q := Nat.sub_sub_self hlt.le
    have hquot : (N - (N - a * q)) / a = q := by
      rw [hreceiver]
      exact Nat.mul_div_cancel_left q ha
    apply Finset.mem_filter.mpr
    refine ⟨hPc, ?_, ?_, ?_, hlarge⟩
    · rw [hreceiver]
      exact dvd_mul_right _ _
    · simpa only [hquot] using hprime
    · simpa only [hquot] using hwall
  · intro P hP
    exact (p5U7Original_AP_recover ha hP).2
  · intro q hq
    have hlt := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.2.2.1
    rw [Nat.sub_sub_self hlt.le]
    exact Nat.mul_div_cancel_left q ha

private theorem p5U7Original_upperDivisorSum_nonneg
    (N cap : ℕ) (z L : ℝ) (hL : 1 < L) (hzL : z ≤ L) (n : ℕ) :
    0 ≤ supportedDivisorSum (actualSmallRosserSupport N cap z)
      (actualSmallRosserPlus N cap z L) n := by
  have h := (actualSmallRosser_sandwich_nat N cap z L hL hzL n).2
  have hi : 0 ≤ (if Nat.Coprime (actualSmallPrimeProduct N cap z) n then
      (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  exact hi.trans h

private theorem p5U7Original_prime_coprime_product
    (N cap : ℕ) (z : ℝ) {P : ℕ} (hP : Nat.Prime P) (hzP : z ≤ (P : ℝ)) :
    Nat.Coprime (actualSmallPrimeProduct N cap z) P := by
  rw [actualSmallPrimeProduct, Nat.coprime_prod_left_iff]
  intro p hp
  have hpd := mem_actualSmallPrimeFinset.mp hp
  apply hpd.2.1.coprime_iff_not_dvd.mpr
  intro hd
  have heq : p = P := (Nat.prime_dvd_prime_iff_eq hpd.2.1 hP).mp hd
  have hlt : (p : ℝ) < (P : ℝ) := hpd.2.2.2.trans_le hzP
  exact hlt.ne (by exact_mod_cast heq)

/-- Actual signed finite sieve bound.  Coefficients are allowed to be
negative: only the proved whole divisor sum is used for enlargement. -/
theorem p5U7Original_APSource_card_le_actualRosser
    (N a ell cap : ℕ) (ha : 0 < a) (L : ℝ)
    (hL : 1 < L) (hzL : (N : ℝ) ^ (1 / 5 : ℝ) ≤ L) :
    ((p5U7OriginalAPSource N a ell).card : ℝ) ≤
      ∑ q ∈ p5U7OriginalTerminalPrimeFibre N a ell,
        supportedDivisorSum
          (actualSmallRosserSupport N cap ((N : ℝ) ^ (1 / 5 : ℝ)))
          (actualSmallRosserPlus N cap ((N : ℝ) ^ (1 / 5 : ℝ)) L) (N - a * q) := by
  let F := p5U7OriginalTerminalPrimeFibre N a ell
  let A := F.filter (fun q => N - a * q ∈ chenAdditivePrimeCarrier N)
  rw [p5U7Original_APSource_card_eq_terminal N a ell ha]
  change (A.card : ℝ) ≤ _
  calc
    _ = ∑ _q ∈ A, (1 : ℝ) := by simp
    _ ≤ ∑ q ∈ A, supportedDivisorSum
        (actualSmallRosserSupport N cap ((N : ℝ) ^ (1 / 5 : ℝ)))
        (actualSmallRosserPlus N cap ((N : ℝ) ^ (1 / 5 : ℝ)) L) (N - a * q) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hqF, hPc⟩ := Finset.mem_filter.mp hq
      have hprime := (mem_chenAdditivePrimeCarrier.mp hPc).2.1
      have hcut := (Finset.mem_filter.mp hqF).2.2.2.2
      have hcop := p5U7Original_prime_coprime_product N cap _ hprime hcut.le
      have h := (actualSmallRosser_sandwich_nat N cap _ L hL hzL (N - a * q)).2
      rwa [if_pos hcop] at h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun q _ _ => p5U7Original_upperDivisorSum_nonneg N cap _ L hL hzL (N - a * q))

/-- Physical divisor-AP counts on a row, with all three literal walls. -/
def p5U7OriginalDivisorAPCount (N a ell d : ℕ) : ℝ :=
  (((p5U7OriginalTerminalPrimeFibre N a ell).filter
    (fun q => d ∣ N - a * q)).card : ℝ)

/-- Exact finite Fubini.  No absolute values replace the signed weights. -/
theorem p5U7Original_terminal_sum_eq_signed_APSum
    (N a ell cap : ℕ) (L : ℝ) :
    (∑ q ∈ p5U7OriginalTerminalPrimeFibre N a ell,
      supportedDivisorSum
        (actualSmallRosserSupport N cap ((N : ℝ) ^ (1 / 5 : ℝ)))
        (actualSmallRosserPlus N cap ((N : ℝ) ^ (1 / 5 : ℝ)) L) (N - a * q)) =
      ∑ d ∈ actualSmallRosserSupport N cap ((N : ℝ) ^ (1 / 5 : ℝ)),
        actualSmallRosserPlus N cap ((N : ℝ) ^ (1 / 5 : ℝ)) L d *
          p5U7OriginalDivisorAPCount N a ell d := by
  simp only [supportedDivisorSum, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter]
  simp only [p5U7OriginalDivisorAPCount, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The two physical families to which a genuine sharp upper mean must
eventually be applied.  Repeated prefix values retain their outer labels. -/
def p5U7OriginalSignedAPMean (N cap : ℕ) (L : ℝ) : ℝ :=
  (∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
    ∑ d ∈ actualSmallRosserSupport N cap ((N : ℝ) ^ (1 / 5 : ℝ)),
      actualSmallRosserPlus N cap ((N : ℝ) ^ (1 / 5 : ℝ)) L d *
        p5U7OriginalDivisorAPCount N (t.1 * t.2) t.2 d) +
  ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
    ∑ r ∈ (chenAdditivePrimeCarrier N).filter (fun r => t.2 ≤ r),
      ∑ d ∈ actualSmallRosserSupport N cap ((N : ℝ) ^ (1 / 5 : ℝ)),
        actualSmallRosserPlus N cap ((N : ℝ) ^ (1 / 5 : ℝ)) L d *
          p5U7OriginalDivisorAPCount N (t.1 * t.2 * r) r d

theorem p5U7Original_two_families_le_signed_APMean
    (N cap : ℕ) (L : ℝ) (hL : 1 < L)
    (hzL : (N : ℝ) ^ (1 / 5 : ℝ) ≤ L) :
    p5U7OriginalPrimeAPSum N + currentChenUpsilon7LargePrimeSemiprimeAPSum N ≤
      p5U7OriginalSignedAPMean N cap L := by
  unfold p5U7OriginalPrimeAPSum currentChenUpsilon7LargePrimeSemiprimeAPSum
    p5U7OriginalSignedAPMean
  apply add_le_add
  · apply Finset.sum_le_sum
    intro t ht
    obtain ⟨hc, _⟩ := Finset.mem_filter.mp ht
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hc
    have ha := mul_pos (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
    exact (p5U7Original_APSource_card_le_actualRosser N _ _ cap ha L hL hzL).trans_eq
      (p5U7Original_terminal_sum_eq_signed_APSum N _ _ cap L)
  · apply Finset.sum_le_sum
    intro t ht
    obtain ⟨hc, _⟩ := Finset.mem_filter.mp ht
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hc
    apply Finset.sum_le_sum
    intro r hr
    have hrp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hr).1).2.1.pos
    have ha := mul_pos (mul_pos (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos) hrp
    rw [p5U7Original_semiprimeAPSource_eq]
    exact (p5U7Original_APSource_card_le_actualRosser N _ _ cap ha L hL hzL).trans_eq
      (p5U7Original_terminal_sum_eq_signed_APSum N _ _ cap L)

/-- The original ledger coefficient two reaches an actual signed finite
AP sum, with the already proved unit/small-original-prime error paid.
The sharp asymptotic bound for this displayed sum is not asserted. -/
theorem p5U7Original_eventually_two_Upsilon7_le_signed_APMean
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ cap : ℕ, ∀ L : ℝ,
      1 < L → (N : ℝ) ^ (1 / 5 : ℝ) ≤ L →
      2 * currentChenUpsilon7 N ≤
        2 * p5U7OriginalSignedAPMean N cap L + epsilon * singularNormalization N := by
  filter_upwards [eventually_two_currentChenUpsilon7_le_largePrime_counts
    epsilon hepsilon] with N hN
  intro cap L hL hzL
  rw [p5U7Original_largePrime_prime_card_eq_APSum] at hN
  have hmean := p5U7Original_two_families_le_signed_APMean N cap L hL hzL
  linarith only [hN, hmean]

end

end ImbalancedChen
