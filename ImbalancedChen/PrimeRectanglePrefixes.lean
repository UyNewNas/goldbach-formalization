import ImbalancedChen.RectangleDiscrepancyAssembly
import ImbalancedChen.SelectedGridRanges
import ImbalancedChen.CoprimeRecentering

/-!
# Exact prime rectangles as differences of prime-prefix counts

The first coordinate ranges over `Ioc L U`. The second coordinate is a
prime at most `V` in each prefix. Subtracting the prefixes at `Vhi` and
`Vlo` gives exactly the full prime rectangle `Ioc L U × Ioc Vlo Vhi`.
The same subtraction holds for the literal coprime mass and hence for the
coprime-normalized discrepancy.

All counts are counts of ordered pairs. There is no diagonal restriction,
product cutoff, removal of squares, or deletion of exterior support. The
identities apply to arbitrary residues and moduli, including modulus one.
Only the finite endpoint order is assumed; no distribution estimate or
external analytic supplier is used.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The full ordered-prime rectangle with open-closed natural sides. -/
def primeIntervalRectangle (L U Vlo Vhi : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ioc L U).filter Nat.Prime).product
    ((Finset.Ioc Vlo Vhi).filter Nat.Prime)

/-- A prime-prefix pair set: the first prime is in `Ioc L U`, while the
second prime satisfies `q ≤ V`. In particular, `q = 2` is retained. -/
def primeRectanglePrefixPairs (L U V : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ioc L U).filter Nat.Prime).product
    ((Finset.range (V + 1)).filter Nat.Prime)

@[simp] theorem mem_primeIntervalRectangle (L U Vlo Vhi : ℕ) (p : ℕ × ℕ) :
    p ∈ primeIntervalRectangle L U Vlo Vhi ↔
      L < p.1 ∧ p.1 ≤ U ∧ Nat.Prime p.1 ∧
        Vlo < p.2 ∧ p.2 ≤ Vhi ∧ Nat.Prime p.2 := by
  simp only [primeIntervalRectangle, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_filter, Finset.mem_Ioc]
  tauto

@[simp] theorem mem_primeRectanglePrefixPairs (L U V : ℕ) (p : ℕ × ℕ) :
    p ∈ primeRectanglePrefixPairs L U V ↔
      L < p.1 ∧ p.1 ≤ U ∧ Nat.Prime p.1 ∧ p.2 ≤ V ∧ Nat.Prime p.2 := by
  simp only [primeRectanglePrefixPairs, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
  omega

/-- The prefix includes every ordered pair of the stated primes, even
when the coordinates are equal or the product exceeds a separate cutoff. -/
theorem primeRectanglePrefixPairs_mono (L U : ℕ) {Vlo Vhi : ℕ}
    (hV : Vlo ≤ Vhi) :
    primeRectanglePrefixPairs L U Vlo ⊆ primeRectanglePrefixPairs L U Vhi := by
  intro p hp
  obtain ⟨hL, hU, hr, hq, hprime⟩ := (mem_primeRectanglePrefixPairs L U Vlo p).mp hp
  exact (mem_primeRectanglePrefixPairs L U Vhi p).mpr
    ⟨hL, hU, hr, hq.trans hV, hprime⟩

/-- Exact set subtraction already works without any endpoint-order premise. -/
theorem primeIntervalRectangle_eq_prefix_sdiff (L U Vlo Vhi : ℕ) :
    primeIntervalRectangle L U Vlo Vhi =
      primeRectanglePrefixPairs L U Vhi \ primeRectanglePrefixPairs L U Vlo := by
  classical
  ext p
  simp only [mem_primeIntervalRectangle, Finset.mem_sdiff,
    mem_primeRectanglePrefixPairs]
  omega

/-- A predicate count respects subtraction of nested finite pair sets.
The subtraction is in `ℝ`, with no truncated natural-number subtraction. -/
theorem card_filter_pair_sdiff_cast
    {A B : Finset (ℕ × ℕ)} (hAB : A ⊆ B)
    (P : (ℕ × ℕ) → Prop) [DecidablePred P] :
    (((B \ A).filter P).card : ℝ) =
      ((B.filter P).card : ℝ) - ((A.filter P).card : ℝ) := by
  classical
  have hf : (B \ A).filter P = (B.filter P) \ (A.filter P) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hs : A.filter P ⊆ B.filter P := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨hAB (Finset.mem_filter.mp hp).1,
      (Finset.mem_filter.mp hp).2⟩
  have hc := Finset.card_sdiff_add_card_eq_card hs
  have hcR : (((B.filter P) \ (A.filter P)).card : ℝ) +
      ((A.filter P).card : ℝ) = ((B.filter P).card : ℝ) := by
    exact_mod_cast hc
  rw [hf]
  linarith

/-- Literal AP count of the prime prefix; the product congruence is the
same predicate used in the actual rectangle discrepancies. -/
def primeRectanglePrefixAPCount (L U V a d : ℕ) : ℝ :=
  (((primeRectanglePrefixPairs L U V).filter
    (fun p => Nat.ModEq d (p.1 * p.2) a)).card : ℝ)

/-- Literal coprime mass of precisely the same prime-prefix pair set. -/
def primeRectanglePrefixCoprimeMass (L U V d : ℕ) : ℝ :=
  (((primeRectanglePrefixPairs L U V).filter
    (fun p => Nat.Coprime (p.1 * p.2) d)).card : ℝ)

/-- The prefix discrepancy uses the genuine Euler-totient normalizer. -/
def primeRectanglePrefixDiscrepancy (L U V a d : ℕ) : ℝ :=
  primeRectanglePrefixAPCount L U V a d -
    primeRectanglePrefixCoprimeMass L U V d / (Nat.totient d : ℝ)

/-- Evaluating the product-fibre weight on its entire product image gives
exactly the prime-prefix AP count, with all pair multiplicities retained. -/
theorem finiteCongruenceMass_primeRectanglePrefixPairs (L U V a d : ℕ) :
    finiteCongruenceMass
        ((primeRectanglePrefixPairs L U V).image (fun p => p.1 * p.2))
        (pairProductWeight (primeRectanglePrefixPairs L U V)) a d =
      primeRectanglePrefixAPCount L U V a d := by
  unfold finiteCongruenceMass primeRectanglePrefixAPCount
  exact sum_pairProductWeight_filter _ _ _ (fun _ hm => hm)

/-- The same full product image and fibre weight give exactly the prefix's
literal coprime mass, including repeated product fibres. -/
theorem finiteCoprimeMass_primeRectanglePrefixPairs (L U V d : ℕ) :
    finiteCoprimeMass
        ((primeRectanglePrefixPairs L U V).image (fun p => p.1 * p.2))
        (pairProductWeight (primeRectanglePrefixPairs L U V)) d =
      primeRectanglePrefixCoprimeMass L U V d := by
  unfold finiteCoprimeMass primeRectanglePrefixCoprimeMass
  exact sum_pairProductWeight_filter _ _ _ (fun _ hm => hm)

/-- The literal prefix discrepancy is the existing finite discrepancy on
the prefix's full product image, so finite recentering applies directly. -/
theorem finitePrimitiveDiscrepancy_primeRectanglePrefixPairs (L U V a d : ℕ) :
    finitePrimitiveDiscrepancy
        ((primeRectanglePrefixPairs L U V).image (fun p => p.1 * p.2))
        (pairProductWeight (primeRectanglePrefixPairs L U V)) a d =
      primeRectanglePrefixDiscrepancy L U V a d := by
  unfold finitePrimitiveDiscrepancy primeRectanglePrefixDiscrepancy
  rw [finiteCongruenceMass_primeRectanglePrefixPairs,
    finiteCoprimeMass_primeRectanglePrefixPairs]

/-- Any residue-independent main term cancels exactly under finite
recentering. This is an identity, with no bound or analytic hypothesis. -/
theorem primeRectanglePrefixAPCount_sub_average_eq_discrepancy
    (L U V a d : ℕ) (M : ℝ) (hd : 0 < d) :
    (primeRectanglePrefixAPCount L U V a d - M) -
        (∑ b ∈ finiteReducedResidues d,
          (primeRectanglePrefixAPCount L U V b d - M)) / (Nat.totient d : ℝ) =
      primeRectanglePrefixDiscrepancy L U V a d := by
  simpa only [finiteCommonMainError,
    finiteCongruenceMass_primeRectanglePrefixPairs,
    finitePrimitiveDiscrepancy_primeRectanglePrefixPairs] using
    finiteCommonMainError_sub_average
      ((primeRectanglePrefixPairs L U V).image (fun p => p.1 * p.2))
      (pairProductWeight (primeRectanglePrefixPairs L U V)) M a d hd

/-- Product counting agrees with an iterated finite prime-prefix AP sum. -/
theorem card_filter_product_cast_eq_sum
    (A B : Finset ℕ) (P : (ℕ × ℕ) → Prop) [DecidablePred P] :
    (((A.product B).filter P).card : ℝ) =
      ∑ r ∈ A, ((B.filter (fun q => P (r, q))).card : ℝ) := by
  classical
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    Finset.sum_filter, Finset.sum_product]

/-- Supplier-facing form: sum over first-coordinate primes, with a literal
prime AP prefix `q ≤ V` in the second coordinate. -/
theorem primeRectanglePrefixAPCount_eq_sum (L U V a d : ℕ) :
    primeRectanglePrefixAPCount L U V a d =
      ∑ r ∈ (Finset.Ioc L U).filter Nat.Prime,
        (((Finset.range (V + 1)).filter
          (fun q => Nat.Prime q ∧ Nat.ModEq d (r * q) a)).card : ℝ) := by
  classical
  unfold primeRectanglePrefixAPCount primeRectanglePrefixPairs
  rw [card_filter_product_cast_eq_sum]
  simp only [Finset.filter_filter]

/-- Equivalent indicator-coefficient form on the full first interval. -/
theorem primeRectanglePrefixAPCount_eq_indicator_sum (L U V a d : ℕ) :
    primeRectanglePrefixAPCount L U V a d =
      ∑ r ∈ Finset.Ioc L U,
        (if Nat.Prime r then (1 : ℝ) else 0) *
          (((Finset.range (V + 1)).filter
            (fun q => Nat.Prime q ∧ Nat.ModEq d (r * q) a)).card : ℝ) := by
  classical
  rw [primeRectanglePrefixAPCount_eq_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp

/-- The coprime prefix mass uses the same first-coordinate prime weights. -/
theorem primeRectanglePrefixCoprimeMass_eq_sum (L U V d : ℕ) :
    primeRectanglePrefixCoprimeMass L U V d =
      ∑ r ∈ (Finset.Ioc L U).filter Nat.Prime,
        (((Finset.range (V + 1)).filter
          (fun q => Nat.Prime q ∧ Nat.Coprime (r * q) d)).card : ℝ) := by
  classical
  unfold primeRectanglePrefixCoprimeMass primeRectanglePrefixPairs
  rw [card_filter_product_cast_eq_sum]
  simp only [Finset.filter_filter]

/-- Exact AP-count subtraction for the full open-closed prime rectangle. -/
theorem primeIntervalRectangle_APCount_eq_prefix_sub
    (L U Vlo Vhi a d : ℕ) (hV : Vlo ≤ Vhi) :
    (((primeIntervalRectangle L U Vlo Vhi).filter
        (fun p => Nat.ModEq d (p.1 * p.2) a)).card : ℝ) =
      primeRectanglePrefixAPCount L U Vhi a d -
        primeRectanglePrefixAPCount L U Vlo a d := by
  classical
  rw [primeIntervalRectangle_eq_prefix_sdiff]
  exact card_filter_pair_sdiff_cast (primeRectanglePrefixPairs_mono L U hV) _

/-- The matching exact coprime-mass subtraction, without replacing it by
a noncoprime total or by an assumed main term. -/
theorem primeIntervalRectangle_coprimeMass_eq_prefix_sub
    (L U Vlo Vhi d : ℕ) (hV : Vlo ≤ Vhi) :
    (((primeIntervalRectangle L U Vlo Vhi).filter
        (fun p => Nat.Coprime (p.1 * p.2) d)).card : ℝ) =
      primeRectanglePrefixCoprimeMass L U Vhi d -
        primeRectanglePrefixCoprimeMass L U Vlo d := by
  classical
  rw [primeIntervalRectangle_eq_prefix_sdiff]
  exact card_filter_pair_sdiff_cast (primeRectanglePrefixPairs_mono L U hV) _

/-- Exact discrepancy subtraction: AP and coprime mass are both taken on
the same prefixes, so the normalizer is preserved without error. -/
theorem primeIntervalRectangle_discrepancy_eq_prefix_sub
    (L U Vlo Vhi a d : ℕ) (hV : Vlo ≤ Vhi) :
    (((primeIntervalRectangle L U Vlo Vhi).filter
        (fun p => Nat.ModEq d (p.1 * p.2) a)).card : ℝ) -
      (((primeIntervalRectangle L U Vlo Vhi).filter
        (fun p => Nat.Coprime (p.1 * p.2) d)).card : ℝ) / (Nat.totient d : ℝ) =
      primeRectanglePrefixDiscrepancy L U Vhi a d -
        primeRectanglePrefixDiscrepancy L U Vlo a d := by
  rw [primeIntervalRectangle_APCount_eq_prefix_sub L U Vlo Vhi a d hV,
    primeIntervalRectangle_coprimeMass_eq_prefix_sub L U Vlo Vhi d hV]
  unfold primeRectanglePrefixDiscrepancy
  ring

/-- The grid endpoint rounding preserves the order needed for subtraction,
including empty natural grid sides. -/
theorem multiplicativeGridIocEndpoint_le_succ {κ : ℝ} (hκ : 1 < κ) (i : ℕ) :
    multiplicativeGridIocEndpoint κ i ≤ multiplicativeGridIocEndpoint κ (i + 1) := by
  have hpow : κ ^ i ≤ κ ^ (i + 1) := by
    rw [pow_succ]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hκ.le (pow_pos (zero_lt_one.trans hκ) i).le
  exact Nat.sub_le_sub_right (Nat.ceil_mono hpow) 1

/-- The literal full prime grid rectangle has exactly these four natural
endpoints; no pair-order or product condition has been added. -/
theorem actualGridPrimeRectangle_eq_primeIntervalRectangle
    {κ : ℝ} (hκ : 1 < κ) (ij : ℕ × ℕ) :
    actualGridPrimeRectangle κ ij =
      primeIntervalRectangle
        (multiplicativeGridIocEndpoint κ ij.1)
        (multiplicativeGridIocEndpoint κ (ij.1 + 1))
        (multiplicativeGridIocEndpoint κ ij.2)
        (multiplicativeGridIocEndpoint κ (ij.2 + 1)) := by
  rw [actualGridPrimeRectangle_eq_product,
    multiplicativeGridSide_eq_Ioc hκ, multiplicativeGridSide_eq_Ioc hκ]
  rfl

/-- Application-facing identity for the actual full grid-rectangle AP count. -/
theorem actualGridPrimeRectangle_APCount_eq_prefix_sub
    {κ : ℝ} (hκ : 1 < κ) (ij : ℕ × ℕ) (a d : ℕ) :
    (((actualGridPrimeRectangle κ ij).filter
        (fun p => Nat.ModEq d (p.1 * p.2) a)).card : ℝ) =
      primeRectanglePrefixAPCount
        (multiplicativeGridIocEndpoint κ ij.1)
        (multiplicativeGridIocEndpoint κ (ij.1 + 1))
        (multiplicativeGridIocEndpoint κ (ij.2 + 1)) a d -
      primeRectanglePrefixAPCount
        (multiplicativeGridIocEndpoint κ ij.1)
        (multiplicativeGridIocEndpoint κ (ij.1 + 1))
        (multiplicativeGridIocEndpoint κ ij.2) a d := by
  rw [actualGridPrimeRectangle_eq_primeIntervalRectangle hκ]
  exact primeIntervalRectangle_APCount_eq_prefix_sub _ _ _ _ a d
    (multiplicativeGridIocEndpoint_le_succ hκ ij.2)

/-- The actual full grid rectangle has the matching coprime-mass identity. -/
theorem actualGridPrimeRectangle_coprimeMass_eq_prefix_sub
    {κ : ℝ} (hκ : 1 < κ) (ij : ℕ × ℕ) (d : ℕ) :
    (((actualGridPrimeRectangle κ ij).filter
        (fun p => Nat.Coprime (p.1 * p.2) d)).card : ℝ) =
      primeRectanglePrefixCoprimeMass
        (multiplicativeGridIocEndpoint κ ij.1)
        (multiplicativeGridIocEndpoint κ (ij.1 + 1))
        (multiplicativeGridIocEndpoint κ (ij.2 + 1)) d -
      primeRectanglePrefixCoprimeMass
        (multiplicativeGridIocEndpoint κ ij.1)
        (multiplicativeGridIocEndpoint κ (ij.1 + 1))
        (multiplicativeGridIocEndpoint κ ij.2) d := by
  rw [actualGridPrimeRectangle_eq_primeIntervalRectangle hκ]
  exact primeIntervalRectangle_coprimeMass_eq_prefix_sub _ _ _ _ d
    (multiplicativeGridIocEndpoint_le_succ hκ ij.2)

/-- Every actual rectangle discrepancy is exactly a difference of two
prime-prefix discrepancies. This retains all squares and exterior products. -/
theorem actualGridRectangleDiscrepancy_eq_prefix_sub
    {κ : ℝ} (hκ : 1 < κ) (ij : ℕ × ℕ) (a d : ℕ) :
    actualGridRectangleDiscrepancy κ ij a d =
      primeRectanglePrefixDiscrepancy
        (multiplicativeGridIocEndpoint κ ij.1)
        (multiplicativeGridIocEndpoint κ (ij.1 + 1))
        (multiplicativeGridIocEndpoint κ (ij.2 + 1)) a d -
      primeRectanglePrefixDiscrepancy
        (multiplicativeGridIocEndpoint κ ij.1)
        (multiplicativeGridIocEndpoint κ (ij.1 + 1))
        (multiplicativeGridIocEndpoint κ ij.2) a d := by
  unfold actualGridRectangleDiscrepancy
  rw [actualGridPrimeRectangle_eq_primeIntervalRectangle hκ]
  exact primeIntervalRectangle_discrepancy_eq_prefix_sub _ _ _ _ a d
    (multiplicativeGridIocEndpoint_le_succ hκ ij.2)

end

end ImbalancedChen
