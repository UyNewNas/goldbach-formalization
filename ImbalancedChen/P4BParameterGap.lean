import ImbalancedChen.ActualUpperCountingInputs

/-!
# P4B: a uniform elementary parameter region for the upper-counting gate

YELLOW / SOURCE-ONLY / UNCOMPILED. This is a proposed source file, not an
installed module or kernel-qualified result. No Lean/lake execution is claimed.

The real imbalance parameter is `b`. The internal sieve exponent is `nu * r`.
For `kappa = 1/4`, the exact fixed-b geometric gap is
`4 * (nu * r) * (1 + b) < 3 * b`. A sufficient b-independent region is
`0 < nu`, `0 < r`, `nu * r <= 1/4`; the suggested bound `<= 1/8` lies inside it.
No value of `nu` or `r` is selected here for a manuscript policy. In particular,
these elementary gates do not supply a full-policy integral certificate, a
compiler budget, or the exact signed distribution estimate.
-/

namespace ImbalancedChen

noncomputable section
open Filter Topology

/-- Uniform strict slack at the manuscript lower product cutoff. -/
theorem p4b_quarter_lt_manuscript_gap {b : ℝ} (hbHalf : 1 / 2 < b) :
    (1 / 4 : ℝ) < (1 - (1 / 4 : ℝ)) * (b / (1 + b)) := by
  have hden : 0 < 1 + b := by linarith
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hden).2
  nlinarith

/-- Concrete exponents independent of b; no density-policy parameter is chosen. -/
theorem p4b_exists_uniform_cutoff_and_sieve_exponent :
    ∃ kappa theta : ℝ, 0 < kappa ∧ kappa < 1 ∧ 0 < theta ∧ theta < 1 ∧
      ∀ b : ℝ, 1 / 2 < b → b < 1 →
        theta < (1 - kappa) * (b / (1 + b)) := by
  refine ⟨1 / 4, 1 / 8, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_⟩
  intro b hbHalf _hbOne
  exact lt_trans (by norm_num) (p4b_quarter_lt_manuscript_gap hbHalf)

/-- Exact fixed-b algebraic form of the positive gap, with no hidden rounding. -/
theorem p4b_quarter_gap_iff {b theta : ℝ} (hb : 0 < b) :
    theta < (1 - (1 / 4 : ℝ)) * (b / (1 + b)) ↔
      4 * theta * (1 + b) < 3 * b := by
  have hden : 0 < 1 + b := by linarith
  rw [← mul_div_assoc, lt_div_iff₀ hden]
  constructor <;> intro h <;> nlinarith only [h]

/-- Exact b-independent region for a fixed exponent at kappa = 1/4.
The endpoint 1/4 is permitted because the b interval is open at 1/2. -/
theorem p4b_uniform_quarter_gap_iff (theta : ℝ) :
    (∀ b : ℝ, 1 / 2 < b → b < 1 →
      theta < (1 - (1 / 4 : ℝ)) * (b / (1 + b))) ↔ theta ≤ 1 / 4 := by
  constructor
  · intro hall
    by_contra hle
    have htheta : (1 / 4 : ℝ) < theta := lt_of_not_ge hle
    let m : ℝ := min (1 / 4) (theta - 1 / 4)
    have hm : 0 < m := by
      dsimp [m]
      exact lt_min (by norm_num) (by linarith)
    have hmQuarter : m ≤ 1 / 4 := min_le_left _ _
    have hmTheta : m ≤ theta - 1 / 4 := min_le_right _ _
    let b : ℝ := 1 / 2 + m
    have hbHalf : (1 / 2 : ℝ) < b := by dsimp [b]; linarith
    have hbOne : b < 1 := by dsimp [b]; linarith
    have hbTheta : b ≤ theta + 1 / 4 := by dsimp [b]; linarith
    have hb : 0 < b := by linarith
    have hgap := (p4b_quarter_gap_iff hb).mp (hall b hbHalf hbOne)
    have hmul : 0 ≤ (theta - 1 / 4) * b :=
      mul_nonneg (by linarith) hb.le
    nlinarith
  · intro htheta b hbHalf _hbOne
    exact lt_of_le_of_lt htheta (p4b_quarter_lt_manuscript_gap hbHalf)

/-- The exact fixed-b gap already implies the assembly's `hsieve` condition. -/
theorem p4b_sieve_lt_one_of_fixed_b_gap {b theta : ℝ}
    (hb : 0 < b)
    (hgap : theta < (1 - (1 / 4 : ℝ)) * (b / (1 + b))) :
    theta < 1 := by
  have hden : 0 < 1 + b := by linarith
  have hfrac : b / (1 + b) < 1 := (div_lt_one hden).2 (by linarith)
  nlinarith

/-- All elementary scalar hypotheses for the actual upper-counting API.
The bound on the positive product is sufficient uniformly for every b in
the target interval; it asserts nothing about density or distribution. -/
theorem p4b_actual_upper_scalar_constraints {b nu r : ℝ}
    (hbHalf : 1 / 2 < b) (hbOne : b < 1)
    (hnu : 0 < nu) (hr : 0 < r) (hproduct : nu * r ≤ 1 / 4) :
    0 < b ∧ b < 1 ∧ 0 < (1 / 4 : ℝ) ∧ (1 / 4 : ℝ) < 1 ∧
      0 < nu ∧ 0 < r ∧ 0 < nu * r ∧ nu * r < 1 ∧
      nu * r < (1 - (1 / 4 : ℝ)) * (b / (1 + b)) := by
  have hb : 0 < b := by linarith
  have hgap : nu * r < (1 - (1 / 4 : ℝ)) * (b / (1 + b)) :=
    lt_of_le_of_lt hproduct (p4b_quarter_lt_manuscript_gap hbHalf)
  exact ⟨hb, hbOne, by norm_num, by norm_num, hnu, hr,
    mul_pos hnu hr, p4b_sieve_lt_one_of_fixed_b_gap hb hgap, hgap⟩

/-- The suggested one-eighth reserve is an explicit subregion. -/
theorem p4b_eighth_product_constraints {b nu r : ℝ}
    (hbHalf : 1 / 2 < b) (hnu : 0 < nu) (hr : 0 < r)
    (hproduct : nu * r ≤ 1 / 8) :
    0 ≤ nu * r ∧ nu * r < 1 ∧
      nu * r < (1 - (1 / 4 : ℝ)) * (b / (1 + b)) := by
  have hquarter : nu * r ≤ 1 / 4 := by linarith
  have hgap := lt_of_le_of_lt hquarter (p4b_quarter_lt_manuscript_gap hbHalf)
  exact ⟨(mul_pos hnu hr).le,
    p4b_sieve_lt_one_of_fixed_b_gap (by linarith) hgap, hgap⟩

/-- Any positive r admits arbitrarily small legal attachment precisions.
`epsilonMax` is supplied by the policy caller, not invented by this lemma. -/
theorem p4b_exists_admissible_attachment_precision {r epsilonMax : ℝ}
    (hr : 0 < r) (hmax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < epsilonMax ∧
      epsilon ≤ 1 ∧ epsilon ^ 2 ≤ r := by
  let m : ℝ := min (1 / 8) (min epsilonMax (min 1 r))
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min (by norm_num) (lt_min hmax (lt_min zero_lt_one hr))
  let epsilon : ℝ := m / 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hsmall : epsilon < m := by dsimp [epsilon]; linarith
  have hm8 : m ≤ 1 / 8 := by exact min_le_left _ _
  have hmMax : m ≤ epsilonMax :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hmOne : m ≤ 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmr : m ≤ r :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hepsilonOne : epsilon ≤ 1 := hsmall.le.trans hmOne
  have hepsilonR : epsilon ≤ r := hsmall.le.trans hmr
  refine ⟨epsilon, hepsilon, hsmall.trans_le hm8, hsmall.trans_le hmMax,
    hepsilonOne, ?_⟩
  have hsquare : epsilon ^ 2 ≤ epsilon := by
    simpa only [pow_two, mul_one] using
      mul_le_mul_of_nonneg_left hepsilonOne hepsilon.le
  exact hsquare.trans hepsilonR

/-- The proven rounding API supplies the literal natural-ceiling sieve gate. -/
theorem p4b_eventually_manuscript_sieve_gate {b nu r : ℝ}
    (hbHalf : 1 / 2 < b) (hnu : 0 < nu) (hr : 0 < r)
    (hproduct : nu * r ≤ 1 / 4) :
    ∀ᶠ N : ℕ in atTop,
      0 < manuscriptHalfProductCutoff (1 / 4) N ∧
        (Nat.ceil ((N : ℝ) ^ (nu * r)) : ℝ) ≤
          (manuscriptHalfProductCutoff (1 / 4) N) ^ (b / (1 + b)) := by
  exact eventually_manuscript_sieve_gate (by linarith) (mul_pos hnu hr).le
    (lt_of_le_of_lt hproduct (p4b_quarter_lt_manuscript_gap hbHalf))

/-- The same legal product region discharges the exact coprime correction
for any retained policy and cap, provided epsilon has the required support. -/
theorem p4b_eventually_attachedUpper_coprimeCorrection_eq_zero
    {b nu r epsilon : ℝ} (hbHalf : 1 / 2 < b)
    (hnu : 0 < nu) (hr : 0 < r) (hproduct : nu * r ≤ 1 / 4)
    (hepsilonR : epsilon ^ 2 ≤ r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop,
      realPhysicalCoprimeCorrection b N (manuscriptHalfProductCutoff (1 / 4) N)
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) = 0 := by
  exact eventually_attachedUpper_coprimeCorrection_eq_zero (by linarith)
    hnu hr.le hepsilonR
    (lt_of_le_of_lt hproduct (p4b_quarter_lt_manuscript_gap hbHalf)) retain cap

end
end ImbalancedChen
