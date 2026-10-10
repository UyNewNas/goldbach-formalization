import ImbalancedChen.HalfProductPanFinite
import ImbalancedChen.PrimeRectanglePrefixes

/-!
# Exact product strips for the bounded-coefficient Pan interface

The Pan prime-progressions used by the intended analytic supplier have a
closed product prefix `r * q ≤ Y`, while the manuscript cells have a strict
lower product wall and a closed upper wall.  This file fixes the finite
endpoint convention before any external distribution theorem is imported.

For `A₁ < r ≤ A₂`, a strip `Y₀ < r*q ≤ Y₁` is exactly the difference of the
two closed prefixes at `Y₁` and `Y₀`.  The identity is proved for the literal
AP count, coprime mass and primitive discrepancy.  When the target residue is
primitive, the AP count is also written with the coprimality gate on `r` that
appears in the bounded Pan interval sum.  All coefficients are zero-one prime
indicators and are independent of the modulus.

These are finite identities.  They do not assert a Pan estimate, a prime
number theorem or a main-term approximation.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Ordered prime pairs in a first-coordinate interval and below a closed
product prefix.  No ordering between the two primes is imposed here. -/
def panProductPrefixPairs (A₁ A₂ Y : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((((Finset.Ioc A₁ A₂).filter Nat.Prime).product
    ((Finset.range (Y + 1)).filter Nat.Prime)).filter
      (fun p => p.1 * p.2 ≤ Y))

@[simp] theorem mem_panProductPrefixPairs {A₁ A₂ Y : ℕ} {p : ℕ × ℕ} :
    p ∈ panProductPrefixPairs A₁ A₂ Y ↔
      A₁ < p.1 ∧ p.1 ≤ A₂ ∧ Nat.Prime p.1 ∧
        Nat.Prime p.2 ∧ p.1 * p.2 ≤ Y := by
  classical
  simp only [panProductPrefixPairs, Finset.mem_filter,
    Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Ioc,
    Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨⟨⟨hA₁, hA₂⟩, hr⟩, _, hq⟩, hprod⟩
    exact ⟨hA₁, hA₂, hr, hq, hprod⟩
  · rintro ⟨hA₁, hA₂, hr, hq, hprod⟩
    have hqY : p.2 ≤ Y := by
      calc
        p.2 = 1 * p.2 := (Nat.one_mul p.2).symm
        _ ≤ p.1 * p.2 := Nat.mul_le_mul_right p.2 hr.one_le
        _ ≤ Y := hprod
    exact ⟨⟨⟨⟨hA₁, hA₂⟩, hr⟩, hqY, hq⟩, hprod⟩

/-- Closed product prefixes are monotone in their product endpoint. -/
theorem panProductPrefixPairs_mono (A₁ A₂ : ℕ) {Y₀ Y₁ : ℕ}
    (hY : Y₀ ≤ Y₁) :
    panProductPrefixPairs A₁ A₂ Y₀ ⊆
      panProductPrefixPairs A₁ A₂ Y₁ := by
  intro p hp
  obtain ⟨hA₁, hA₂, hr, hq, hprod⟩ := mem_panProductPrefixPairs.mp hp
  exact mem_panProductPrefixPairs.mpr
    ⟨hA₁, hA₂, hr, hq, hprod.trans hY⟩

/-- The literal open-closed product strip used by a manuscript cell. -/
def panProductStripPairs (A₁ A₂ Y₀ Y₁ : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (panProductPrefixPairs A₁ A₂ Y₁).filter
    (fun p => Y₀ < p.1 * p.2)

@[simp] theorem mem_panProductStripPairs
    {A₁ A₂ Y₀ Y₁ : ℕ} {p : ℕ × ℕ} :
    p ∈ panProductStripPairs A₁ A₂ Y₀ Y₁ ↔
      A₁ < p.1 ∧ p.1 ≤ A₂ ∧ Nat.Prime p.1 ∧ Nat.Prime p.2 ∧
        Y₀ < p.1 * p.2 ∧ p.1 * p.2 ≤ Y₁ := by
  classical
  simp only [panProductStripPairs, Finset.mem_filter,
    mem_panProductPrefixPairs]
  tauto

/-- A strict-lower, closed-upper product strip is exactly a difference of
closed prefixes.  The equality also covers an empty or reversed strip. -/
theorem panProductStripPairs_eq_prefix_sdiff
    (A₁ A₂ Y₀ Y₁ : ℕ) :
    panProductStripPairs A₁ A₂ Y₀ Y₁ =
      panProductPrefixPairs A₁ A₂ Y₁ \
        panProductPrefixPairs A₁ A₂ Y₀ := by
  classical
  ext p
  constructor
  · intro hp
    rcases mem_panProductStripPairs.mp hp with
      ⟨hA₁, hA₂, hr, hq, hlo, hhi⟩
    refine Finset.mem_sdiff.mpr
      ⟨mem_panProductPrefixPairs.mpr ⟨hA₁, hA₂, hr, hq, hhi⟩, ?_⟩
    intro hp₀
    exact (not_le_of_gt hlo) (mem_panProductPrefixPairs.mp hp₀).2.2.2.2
  · intro hp
    rcases Finset.mem_sdiff.mp hp with ⟨hp₁, hn⟩
    rcases mem_panProductPrefixPairs.mp hp₁ with
      ⟨hA₁, hA₂, hr, hq, hhi⟩
    refine mem_panProductStripPairs.mpr
      ⟨hA₁, hA₂, hr, hq, ?_, hhi⟩
    by_contra hlo
    apply hn
    exact mem_panProductPrefixPairs.mpr
      ⟨hA₁, hA₂, hr, hq, Nat.le_of_not_gt hlo⟩

/-- The single-fibre prime count in a closed product prefix.  This mirrors the
finite count inside the external `primesInAPBelow` definition. -/
def panProductPrefixFibreAPCount (Y r a d : ℕ) : ℝ :=
  (((Finset.range (Y + 1)).filter (fun q =>
    Nat.Prime q ∧ r * q ≤ Y ∧ Nat.ModEq d (r * q) a)).card : ℝ)

/-- The moving product wall in one fibre is exactly the closed Pan endpoint
`q ≤ Y / r`.  The positivity hypothesis is available whenever the outer
coefficient is nonzero, because that coefficient is a prime indicator. -/
theorem panProductPrefixFibreAPCount_eq_div
    {Y r a d : ℕ} (hr : 0 < r) :
    panProductPrefixFibreAPCount Y r a d =
      (((Nat.primesLE (Y / r)).filter
        (fun q => Nat.ModEq d (r * q) a)).card : ℝ) := by
  classical
  unfold panProductPrefixFibreAPCount
  have hset :
      (Finset.range (Y + 1)).filter (fun q =>
          Nat.Prime q ∧ r * q ≤ Y ∧ Nat.ModEq d (r * q) a) =
        (Nat.primesLE (Y / r)).filter
          (fun q => Nat.ModEq d (r * q) a) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
      Nat.mem_primesLE]
    constructor
    · rintro ⟨_, hqPrime, hprod, hAP⟩
      have hqDiv : q ≤ Y / r :=
        (Nat.le_div_iff_mul_le hr).mpr (by
          simpa only [Nat.mul_comm] using hprod)
      exact ⟨⟨hqDiv, hqPrime⟩, hAP⟩
    · rintro ⟨⟨hqDiv, hqPrime⟩, hAP⟩
      have hprod : r * q ≤ Y := by
        simpa only [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le hr).mp hqDiv
      have hqY : q ≤ Y := hqDiv.trans (Nat.div_le_self Y r)
      exact ⟨hqY, hqPrime, hprod, hAP⟩
  rw [hset]

/-- Literal AP count on the complete product prefix. -/
def panProductPrefixAPCount (A₁ A₂ Y a d : ℕ) : ℝ :=
  (((panProductPrefixPairs A₁ A₂ Y).filter
    (fun p => Nat.ModEq d (p.1 * p.2) a)).card : ℝ)

/-- Literal coprime mass on the same product prefix. -/
def panProductPrefixCoprimeMass (A₁ A₂ Y d : ℕ) : ℝ :=
  (((panProductPrefixPairs A₁ A₂ Y).filter
    (fun p => Nat.Coprime (p.1 * p.2) d)).card : ℝ)

/-- Primitive discrepancy on the same product prefix. -/
def panProductPrefixDiscrepancy (A₁ A₂ Y a d : ℕ) : ℝ :=
  panProductPrefixAPCount A₁ A₂ Y a d -
    panProductPrefixCoprimeMass A₁ A₂ Y d / (Nat.totient d : ℝ)

/-- Literal AP count on one strict-lower, closed-upper product strip. -/
def panProductStripAPCount (A₁ A₂ Y₀ Y₁ a d : ℕ) : ℝ :=
  (((panProductStripPairs A₁ A₂ Y₀ Y₁).filter
    (fun p => Nat.ModEq d (p.1 * p.2) a)).card : ℝ)

/-- Literal coprime mass on the same product strip. -/
def panProductStripCoprimeMass (A₁ A₂ Y₀ Y₁ d : ℕ) : ℝ :=
  (((panProductStripPairs A₁ A₂ Y₀ Y₁).filter
    (fun p => Nat.Coprime (p.1 * p.2) d)).card : ℝ)

/-- Primitive discrepancy on the same product strip. -/
def panProductStripDiscrepancy (A₁ A₂ Y₀ Y₁ a d : ℕ) : ℝ :=
  panProductStripAPCount A₁ A₂ Y₀ Y₁ a d -
    panProductStripCoprimeMass A₁ A₂ Y₀ Y₁ d / (Nat.totient d : ℝ)

/-- A product-prefix AP count is an iterated sum over the first prime. -/
theorem panProductPrefixAPCount_eq_sum (A₁ A₂ Y a d : ℕ) :
    panProductPrefixAPCount A₁ A₂ Y a d =
      ∑ r ∈ (Finset.Ioc A₁ A₂).filter Nat.Prime,
        panProductPrefixFibreAPCount Y r a d := by
  classical
  unfold panProductPrefixAPCount panProductPrefixPairs
    panProductPrefixFibreAPCount
  rw [Finset.filter_filter, card_filter_product_cast_eq_sum]
  simp only [Finset.filter_filter]

/-- The iterated prefix count with its moving endpoint already normalized to
the closed division form used by a Pan theorem. -/
theorem panProductPrefixAPCount_eq_sum_div (A₁ A₂ Y a d : ℕ) :
    panProductPrefixAPCount A₁ A₂ Y a d =
      ∑ r ∈ (Finset.Ioc A₁ A₂).filter Nat.Prime,
        (((Nat.primesLE (Y / r)).filter
          (fun q => Nat.ModEq d (r * q) a)).card : ℝ) := by
  rw [panProductPrefixAPCount_eq_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [panProductPrefixFibreAPCount_eq_div
    (Finset.mem_filter.mp hr).2.pos]

/-- Equivalent bounded-coefficient form on the complete first interval. -/
theorem panProductPrefixAPCount_eq_indicator_sum (A₁ A₂ Y a d : ℕ) :
    panProductPrefixAPCount A₁ A₂ Y a d =
      ∑ r ∈ Finset.Ioc A₁ A₂,
        (if Nat.Prime r then (1 : ℝ) else 0) *
          panProductPrefixFibreAPCount Y r a d := by
  classical
  rw [panProductPrefixAPCount_eq_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : Nat.Prime r <;> simp [hr]

/-- In a primitive target residue, an AP fibre with a non-coprime first
coordinate is empty. -/
theorem panProductPrefixFibreAPCount_eq_zero_of_not_coprime
    {Y r a d : ℕ} (ha : Nat.Coprime a d) (hrd : ¬Nat.Coprime r d) :
    panProductPrefixFibreAPCount Y r a d = 0 := by
  classical
  unfold panProductPrefixFibreAPCount
  rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q hq hmem
  rcases hmem with ⟨_, _, hAP⟩
  have hprod : Nat.Coprime (r * q) d := by
    rw [Nat.Coprime, hAP.gcd_eq]
    exact ha
  exact hrd (Nat.coprime_mul_iff_left.mp hprod).1

/-- Supplier-facing prefix identity: the coprimality gate is exactly the gate
used by the bounded Pan interval sum, while the coefficient remains the
modulus-independent prime indicator. -/
theorem panProductPrefixAPCount_eq_coprime_indicator_sum
    (A₁ A₂ Y a d : ℕ) (ha : Nat.Coprime a d) :
    panProductPrefixAPCount A₁ A₂ Y a d =
      ∑ r ∈ Finset.Ioc A₁ A₂,
        if Nat.Coprime r d then
          (if Nat.Prime r then (1 : ℝ) else 0) *
            panProductPrefixFibreAPCount Y r a d
        else 0 := by
  rw [panProductPrefixAPCount_eq_indicator_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hrd : Nat.Coprime r d
  · simp [hrd]
  · rw [if_neg hrd,
      panProductPrefixFibreAPCount_eq_zero_of_not_coprime ha hrd]
    simp

/-- Fully normalized supplier-facing form: the moving prime prefix is
`q ≤ Y / r`, the coprimality gate is outside the coefficient, and the
coefficient itself is independent of the modulus. -/
theorem panProductPrefixAPCount_eq_coprime_indicator_sum_div
    (A₁ A₂ Y a d : ℕ) (ha : Nat.Coprime a d) :
    panProductPrefixAPCount A₁ A₂ Y a d =
      ∑ r ∈ Finset.Ioc A₁ A₂,
        if Nat.Coprime r d then
          (if Nat.Prime r then (1 : ℝ) else 0) *
            (((Nat.primesLE (Y / r)).filter
              (fun q => Nat.ModEq d (r * q) a)).card : ℝ)
        else 0 := by
  rw [panProductPrefixAPCount_eq_coprime_indicator_sum A₁ A₂ Y a d ha]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hrd : Nat.Coprime r d
  · by_cases hr : Nat.Prime r
    · simp [hr, panProductPrefixFibreAPCount_eq_div hr.pos]
    · simp [hr]
  · simp [hrd]

/-- Exact AP-count subtraction for a product strip. -/
theorem panProductStripAPCount_eq_prefix_sub
    (A₁ A₂ Y₀ Y₁ a d : ℕ) (hY : Y₀ ≤ Y₁) :
    panProductStripAPCount A₁ A₂ Y₀ Y₁ a d =
      panProductPrefixAPCount A₁ A₂ Y₁ a d -
        panProductPrefixAPCount A₁ A₂ Y₀ a d := by
  classical
  unfold panProductStripAPCount panProductPrefixAPCount
  rw [panProductStripPairs_eq_prefix_sdiff]
  exact card_filter_pair_sdiff_cast
    (panProductPrefixPairs_mono A₁ A₂ hY) _

/-- Exact coprime-mass subtraction for the same product strip. -/
theorem panProductStripCoprimeMass_eq_prefix_sub
    (A₁ A₂ Y₀ Y₁ d : ℕ) (hY : Y₀ ≤ Y₁) :
    panProductStripCoprimeMass A₁ A₂ Y₀ Y₁ d =
      panProductPrefixCoprimeMass A₁ A₂ Y₁ d -
        panProductPrefixCoprimeMass A₁ A₂ Y₀ d := by
  classical
  unfold panProductStripCoprimeMass panProductPrefixCoprimeMass
  rw [panProductStripPairs_eq_prefix_sdiff]
  exact card_filter_pair_sdiff_cast
    (panProductPrefixPairs_mono A₁ A₂ hY) _

/-- Exact primitive-discrepancy subtraction.  Both the AP count and coprime
mass use the same two prefixes, so no normalization correction is hidden. -/
theorem panProductStripDiscrepancy_eq_prefix_sub
    (A₁ A₂ Y₀ Y₁ a d : ℕ) (hY : Y₀ ≤ Y₁) :
    panProductStripDiscrepancy A₁ A₂ Y₀ Y₁ a d =
      panProductPrefixDiscrepancy A₁ A₂ Y₁ a d -
        panProductPrefixDiscrepancy A₁ A₂ Y₀ a d := by
  rw [panProductStripDiscrepancy,
    panProductStripAPCount_eq_prefix_sub A₁ A₂ Y₀ Y₁ a d hY,
    panProductStripCoprimeMass_eq_prefix_sub A₁ A₂ Y₀ Y₁ d hY]
  unfold panProductPrefixDiscrepancy
  ring

/-- Final finite Pan-facing strip identity.  The lower wall is strict because
the lower closed prefix is subtracted from the upper closed prefix. -/
theorem panProductStripAPCount_eq_coprime_indicator_sum_sub
    (A₁ A₂ Y₀ Y₁ a d : ℕ) (hY : Y₀ ≤ Y₁)
    (ha : Nat.Coprime a d) :
    panProductStripAPCount A₁ A₂ Y₀ Y₁ a d =
      ∑ r ∈ Finset.Ioc A₁ A₂,
        if Nat.Coprime r d then
          (if Nat.Prime r then (1 : ℝ) else 0) *
            (panProductPrefixFibreAPCount Y₁ r a d -
              panProductPrefixFibreAPCount Y₀ r a d)
        else 0 := by
  rw [panProductStripAPCount_eq_prefix_sub A₁ A₂ Y₀ Y₁ a d hY,
    panProductPrefixAPCount_eq_coprime_indicator_sum A₁ A₂ Y₁ a d ha,
    panProductPrefixAPCount_eq_coprime_indicator_sum A₁ A₂ Y₀ a d ha,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hrd : Nat.Coprime r d
  · simp only [if_pos hrd]
    ring
  · simp [hrd]

/-- Abstract main term attached to the same closed moving prefixes.  Taking
`mainTerm t` to be the logarithmic integral at `t` gives the algebraic shape
of the imported Liu--Pan error, without asserting that analytic estimate. -/
def panProductPrefixAnalyticMain (mainTerm : ℕ → ℝ)
    (A₁ A₂ Y d : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ioc A₁ A₂,
    if Nat.Coprime r d then
      (if Nat.Prime r then (1 : ℝ) else 0) *
        (mainTerm (Y / r) / (Nat.totient d : ℝ))
    else 0

/-- Prefix error relative to an abstract prime-counting main term. -/
def panProductPrefixAnalyticError (mainTerm : ℕ → ℝ)
    (A₁ A₂ Y a d : ℕ) : ℝ :=
  panProductPrefixAPCount A₁ A₂ Y a d -
    panProductPrefixAnalyticMain mainTerm A₁ A₂ Y d

/-- On a primitive residue, the prefix error is literally the bounded
prime-indicator sum of the individual moving-prefix errors. -/
theorem panProductPrefixAnalyticError_eq_sum
    (mainTerm : ℕ → ℝ) (A₁ A₂ Y a d : ℕ)
    (ha : Nat.Coprime a d) :
    panProductPrefixAnalyticError mainTerm A₁ A₂ Y a d =
      ∑ r ∈ Finset.Ioc A₁ A₂,
        if Nat.Coprime r d then
          (if Nat.Prime r then (1 : ℝ) else 0) *
            (panProductPrefixFibreAPCount Y r a d -
              mainTerm (Y / r) / (Nat.totient d : ℝ))
        else 0 := by
  unfold panProductPrefixAnalyticError panProductPrefixAnalyticMain
  rw [panProductPrefixAPCount_eq_coprime_indicator_sum A₁ A₂ Y a d ha,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hrd : Nat.Coprime r d
  · simp only [if_pos hrd]
    ring
  · simp [hrd]

/-- The analytic main term assigned to a product strip is the difference of
the two closed-prefix main terms. -/
def panProductStripAnalyticMain (mainTerm : ℕ → ℝ)
    (A₁ A₂ Y₀ Y₁ d : ℕ) : ℝ :=
  panProductPrefixAnalyticMain mainTerm A₁ A₂ Y₁ d -
    panProductPrefixAnalyticMain mainTerm A₁ A₂ Y₀ d

/-- Error of the literal strip count relative to that difference main term. -/
def panProductStripAnalyticError (mainTerm : ℕ → ℝ)
    (A₁ A₂ Y₀ Y₁ a d : ℕ) : ℝ :=
  panProductStripAPCount A₁ A₂ Y₀ Y₁ a d -
    panProductStripAnalyticMain mainTerm A₁ A₂ Y₀ Y₁ d

/-- The strip error is exactly upper-prefix error minus lower-prefix error.
This is the two-prefix reduction to which bounded Pan is applied. -/
theorem panProductStripAnalyticError_eq_prefix_sub
    (mainTerm : ℕ → ℝ) (A₁ A₂ Y₀ Y₁ a d : ℕ)
    (hY : Y₀ ≤ Y₁) :
    panProductStripAnalyticError mainTerm A₁ A₂ Y₀ Y₁ a d =
      panProductPrefixAnalyticError mainTerm A₁ A₂ Y₁ a d -
        panProductPrefixAnalyticError mainTerm A₁ A₂ Y₀ a d := by
  unfold panProductStripAnalyticError panProductStripAnalyticMain
    panProductPrefixAnalyticError
  rw [panProductStripAPCount_eq_prefix_sub A₁ A₂ Y₀ Y₁ a d hY]
  ring

/-- Consequently, controlling the two prefix errors controls the strip error
with no hidden endpoint or normalization term. -/
theorem abs_panProductStripAnalyticError_le
    (mainTerm : ℕ → ℝ) (A₁ A₂ Y₀ Y₁ a d : ℕ)
    (hY : Y₀ ≤ Y₁) :
    |panProductStripAnalyticError mainTerm A₁ A₂ Y₀ Y₁ a d| ≤
      |panProductPrefixAnalyticError mainTerm A₁ A₂ Y₁ a d| +
        |panProductPrefixAnalyticError mainTerm A₁ A₂ Y₀ a d| := by
  rw [panProductStripAnalyticError_eq_prefix_sub
    mainTerm A₁ A₂ Y₀ Y₁ a d hY]
  exact abs_sub _ _

/-- The modulus-independent prime indicator used above has absolute value at
most one, uniformly on every product strip. -/
theorem abs_panProductPrimeIndicator_le_one (r : ℕ) :
    |(if Nat.Prime r then (1 : ℝ) else 0)| ≤ 1 :=
  abs_primeIndicator_le_one r

end

end ImbalancedChen
