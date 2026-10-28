import ImbalancedChen.P2OriginalSelectedIntegerPrefixSquares
import ImbalancedChen.P2EnhancedNativeLowerAtomSupport
import ImbalancedChen.CurrentChenP5CausalRhoFactorization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Append actual unselected descendants to the exact tagged SourceForm
prefix, keeping its selected mask and its frozen cap literally unchanged.
The final application appends the CANONICAL small-prime factor word of a
nonzero actual sign-attached lower-rho pair. Its residual square support
is proved from the actual beta-minus/beta-plus coefficient, not assumed.

The incoming word may already contain rough descendants. Their actual
producer must supply its old gate lists and the scalar residual budget;
this file does not infer support for an arbitrary retained rough policy.
-/

namespace ImbalancedChen.P2OriginalSelectedNativeSmallExtension

noncomputable section
open scoped Classical
open P2OriginalSelectedIntegerPrefixSquares
open P2EnhancedNativeLowerAtomSupport
open Part3.ActualCompactAllRankSupport
open P2EnhancedSortedDwellMerge P2EnhancedPrimeAtomSortedMerge
open P5CausalRhoFactorization

/-- Converse of the first batch's indexed extraction theorem. -/
theorem integerSquareGates_of_indexed {N B : ℕ} {cap : ℝ}
    (ps : List ℕ)
    (hgates : ∀ i : ℕ, ∀ hi : i < ps.length,
      ((B * (ps.take i).prod : ℕ) : ℝ) * (ps[i] : ℝ)^2 ≤ (N : ℝ)^cap) :
    IntegerSquareGates N cap B ps := by
  induction ps generalizing B with
  | nil => trivial
  | cons p ps ih =>
      constructor
      · simpa using hgates 0 (by simp)
      · apply ih
        intro i hi
        have h := hgates (i+1) (by simpa using Nat.succ_lt_succ hi)
        simpa [Nat.mul_assoc] using h

theorem integerSquareGates_append_iff (N B : ℕ) (cap : ℝ)
    (ps ds : List ℕ) :
    IntegerSquareGates N cap B (ps ++ ds) ↔
      IntegerSquareGates N cap B ps ∧
        IntegerSquareGates N cap (B * ps.prod) ds := by
  induction ps generalizing B with
  | nil => simp [IntegerSquareGates]
  | cons p ps ih =>
      simp [IntegerSquareGates, ih, Nat.mul_assoc, and_assoc]

/-- The residual level is scaled by the ACTUAL prefix product B. -/
theorem integerSquareGates_of_dwell_scaled (N B : ℕ) (cap R : ℝ)
    (ds : List ℕ) (hres : actualDwellSupport R ds)
    (hbudget : (B : ℝ) * R ≤ (N : ℝ)^cap) :
    IntegerSquareGates N cap B ds := by
  apply integerSquareGates_of_indexed
  intro i hi
  calc
    ((B * (ds.take i).prod : ℕ) : ℝ) * (ds[i] : ℝ)^2 =
        (B : ℝ) * (((ds.take i).map (fun p : ℕ => (p : ℝ))).prod *
          (ds[i] : ℝ)^2) := by
      rw [actualNatList_cast_prod, Nat.cast_mul]
      ring
    _ ≤ (B : ℝ) * R :=
      mul_le_mul_of_nonneg_left (hres i hi) (Nat.cast_nonneg B)
    _ ≤ (N : ℝ)^cap := hbudget

/-- New primes have no original selected-slot tag. -/
def appendUnselected (slots : List (ℕ × Bool)) (ds : List ℕ) : List (ℕ × Bool) :=
  slots ++ ds.map (fun p => (p, false))

@[simp] theorem appendUnselected_values (slots : List (ℕ × Bool)) (ds : List ℕ) :
    (appendUnselected slots ds).map Prod.fst = slots.map Prod.fst ++ ds := by
  simp [appendUnselected, List.map_map, Function.comp_def]

@[simp] theorem appendUnselected_selected (slots : List (ℕ × Bool)) (ds : List ℕ) :
    selectedPrimes (appendUnselected slots ds) = selectedPrimes slots := by
  have hfilter : (ds.map (fun p => (p, false))).filter
      (fun a : ℕ × Bool => a.2) = [] := by
    induction ds with
    | nil => rfl
    | cons p ds ih => simpa using ih
  simp [appendUnselected, selectedPrimes, List.filter_append, hfilter]

@[simp] theorem appendUnselected_remaining (slots : List (ℕ × Bool)) (ds : List ℕ) :
    remainingPrimes (appendUnselected slots ds) = remainingPrimes slots ++ ds := by
  have hfilter : (ds.map (fun p => (p, false))).filter
      (fun a : ℕ × Bool => !a.2) = ds.map (fun p => (p, false)) := by
    induction ds with
    | nil => rfl
    | cons p ds ih => simpa using congrArg (List.cons (p,false)) ih
  simp [appendUnselected, remainingPrimes, List.filter_append, hfilter,
    List.map_map, Function.comp_def]

/-- Exact extension of BOTH gate lists. The complement starts from
    A*C=B, not an independent residual level or replacement mask. -/
theorem append_unselected_same_cap {N : ℕ} {cap R : ℝ}
    (slots : List (ℕ × Bool)) (ds : List ℕ)
    (hfull : IntegerSquareGates N cap 1 (slots.map Prod.fst))
    (hselected : IntegerSquareGates N cap
      (selectedPrimes slots).prod (remainingPrimes slots))
    (hres : actualDwellSupport R ds)
    (hbudget : ((slots.map Prod.fst).prod : ℝ) * R ≤ (N : ℝ)^cap) :
    IntegerSquareGates N cap 1 ((appendUnselected slots ds).map Prod.fst) ∧
      IntegerSquareGates N cap (selectedPrimes (appendUnselected slots ds)).prod
        (remainingPrimes (appendUnselected slots ds)) ∧
      selectedPrimes (appendUnselected slots ds) = selectedPrimes slots ∧
      ((appendUnselected slots ds).map Prod.fst).prod =
        (slots.map Prod.fst).prod * ds.prod := by
  have htail := integerSquareGates_of_dwell_scaled N
    (slots.map Prod.fst).prod cap R ds hres hbudget
  have hselectedTail : IntegerSquareGates N cap
      ((selectedPrimes slots).prod * (remainingPrimes slots).prod) ds := by
    rw [P2OriginalSelectedIntegerPrefixSquares.selected_mul_remaining]
    exact htail
  refine ⟨?_, ?_, appendUnselected_selected slots ds, ?_⟩
  · rw [appendUnselected_values, integerSquareGates_append_iff]
    exact ⟨hfull, by simpa only [Nat.one_mul] using htail⟩
  · rw [appendUnselected_selected, appendUnselected_remaining,
      integerSquareGates_append_iff]
    exact ⟨hselected, hselectedTail⟩
  · rw [appendUnselected_values, List.prod_append]

/-- The literal upper small Rosser coefficient pays its own full squares.
    This completes the OTHER sign of the existing native-minus supplier. -/
theorem actual_plus_residual_well {N enum s : ℕ} {w L : ℝ}
    (hs : actualSmallRosserPlus N enum w L s ≠ 0) :
    actualDwellSupport L s.primeFactorsList.reverse := by
  have ha := MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_active hs
  have hsf := actualSmallRosserSupport_squarefree N enum w ha.1
  have hprime : ∀ p ∈ s.primeFactorsList.reverse, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hp)
  have hge : s.primeFactorsList.reverse.Pairwise (· ≥ ·) :=
    (Nat.primeFactorsList_sorted s).reverse.pairwise
  have hnd : s.primeFactorsList.reverse.Nodup := hsf.nodup_primeFactorsList.reverse
  have hgt : s.primeFactorsList.reverse.Pairwise (· > ·) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hle := (List.pairwise_iff_getElem.mp hge) i j hi hj hij
    have hne := (List.pairwise_iff_getElem.mp hnd) i j hi hj hij
    omega
  apply upper_set_dwell_support s.primeFactorsList.reverse hprime hgt
  simpa only [List.toFinset_reverse, Nat.toFinset_factors] using ha.2.2

/-- The nonzero signed pair selects the actual beta sign. Its small
    support is a CONCLUSION; beta-minus requires its genuine head cutoff. -/
theorem active_pair_small_word_well (policy : List ℕ → Bool)
    (N enum : ℕ) (w z L : ℝ) {x : ℕ × ℕ}
    (hx : x ∈ activePairs policy N enum w z L) (hhead : w^2 ≤ L) :
    actualDwellSupport L x.1.primeFactorsList.reverse := by
  have hn := (Finset.mem_filter.mp hx).2
  change fixedEvenRoughCoefficient policy N enum w z x.2 *
    (if 0 ≤ fixedEvenRoughCoefficient policy N enum w z x.2 then
      actualSmallRosserMinus N enum w L x.1 else
      actualSmallRosserPlus N enum w L x.1) ≠ 0 at hn
  have hbeta := (mul_ne_zero_iff.mp hn).2
  by_cases hsign : 0 ≤ fixedEvenRoughCoefficient policy N enum w z x.2
  · rw [if_pos hsign] at hbeta
    exact actual_minus_residual_well hbeta hhead
  · rw [if_neg hsign] at hbeta
    exact actual_plus_residual_well hbeta

/-- Actual small factors remain strictly below the real presieve cutoff. -/
theorem active_pair_small_word_cutoff (policy : List ℕ → Bool)
    (N enum : ℕ) (w z L : ℝ) {x : ℕ × ℕ}
    (hx : x ∈ activePairs policy N enum w z L) :
    ∀ p ∈ x.1.primeFactorsList.reverse, (p : ℝ) < w := by
  have hpairs := (Finset.mem_filter.mp hx).1
  have hsmall := actualSmallRosserSupport_smallPrimeSupportedAt N enum w
    (Finset.mem_product.mp hpairs).1
  intro p hp
  apply hsmall.2 p
  exact Nat.mem_primeFactors.mpr
    ⟨Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hp),
      Nat.dvd_of_mem_primeFactorsList (List.mem_reverse.mp hp), hsmall.1⟩

/-- A concrete actual signed rho pair (s,r) now appends its actual small
    prime word AFTER the incoming full/rough word. The selected SourceForm
    mask and cap do not change. Cutoff separation proves sortedness, and
    unique factorization identifies the final actual canonical vector.

    The incoming gate lists may be supplied by the first-batch SourceForm
    plus a licensed rough extension. This statement does not fabricate
    that missing rough producer or its scalar budget. -/
theorem actual_signed_small_extension (policy : List ℕ → Bool)
    (N enum B : ℕ) (w z L cap : ℝ) {x : ℕ × ℕ}
    (hx : x ∈ activePairs policy N enum w z L)
    (hhead : w^2 ≤ L) (slots : List (ℕ × Bool))
    (hprod : (slots.map Prod.fst).prod = B * x.2)
    (hprime : ∀ p ∈ slots.map Prod.fst, p.Prime)
    (hsort : (slots.map Prod.fst).Pairwise (· ≥ ·))
    (hcut : ∀ p ∈ slots.map Prod.fst, w ≤ (p : ℝ))
    (hfull : IntegerSquareGates N cap 1 (slots.map Prod.fst))
    (hselected : IntegerSquareGates N cap
      (selectedPrimes slots).prod (remainingPrimes slots))
    (hbudget : ((B * x.2 : ℕ) : ℝ) * L ≤ (N : ℝ)^cap) :
    let ds := x.1.primeFactorsList.reverse
    let extended := appendUnselected slots ds
    IntegerSquareGates N cap 1 (extended.map Prod.fst) ∧
      IntegerSquareGates N cap (selectedPrimes extended).prod (remainingPrimes extended) ∧
      selectedPrimes extended = selectedPrimes slots ∧
      extended.map Prod.fst = ((B * x.2) * x.1).primeFactorsList.reverse ∧
      actualLowerSmallRoughRho policy N enum w z L (x.1*x.2) =
        coefficient policy N enum w z L x := by
  let ds := x.1.primeFactorsList.reverse
  have hsmallWell := active_pair_small_word_well policy N enum w z L hx hhead
  have hbudget' : ((slots.map Prod.fst).prod : ℝ) * L ≤ (N : ℝ)^cap := by
    simpa only [hprod] using hbudget
  have hext := append_unselected_same_cap slots ds hfull hselected hsmallWell hbudget'
  have hpairs := (Finset.mem_filter.mp hx).1
  have hsmallSf := actualSmallRosserSupport_squarefree N enum w
    (Finset.mem_product.mp hpairs).1
  have hsmallPrime : ∀ p ∈ ds, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hp)
  have hsmallProduct : ds.prod = x.1 := by
    rw [List.prod_reverse, Nat.prod_primeFactorsList hsmallSf.ne_zero]
  have hsmallSort : ds.Pairwise (· ≥ ·) :=
    (Nat.primeFactorsList_sorted x.1).reverse.pairwise
  have hcross : ∀ p ∈ slots.map Prod.fst, ∀ q ∈ ds, p ≥ q := by
    intro p hp q hq
    have hqsmall := active_pair_small_word_cutoff policy N enum w z L hx q hq
    have hpbig := hcut p hp
    exact_mod_cast hqsmall.le.trans hpbig
  have hsortExtended : (slots.map Prod.fst ++ ds).Pairwise (· ≥ ·) :=
    List.pairwise_append.mpr ⟨hsort, hsmallSort, hcross⟩
  have hprefixPos : 0 < (slots.map Prod.fst).prod := by
    apply List.prod_pos
    intro p hp
    exact (hprime p hp).pos
  have hprefixNZ : B * x.2 ≠ 0 := by
    rw [← hprod]
    exact Nat.ne_of_gt hprefixPos
  have hcanonical := sortedUnion_eq_primeFactors (slots.map Prod.fst) ds
    hprod hsmallProduct hprefixNZ hsmallSf.ne_zero hprime hsmallPrime
  have happend : slots.map Prod.fst ++ ds = sortedUnion (slots.map Prod.fst) ds :=
    (sortedUnion_perm (slots.map Prod.fst) ds).symm.eq_of_pairwise'
      hsortExtended (sortedUnion_sorted (slots.map Prod.fst) ds)
  refine ⟨hext.1, hext.2.1, hext.2.2.1, ?_, rho_at_pair policy N enum w z L hpairs⟩
  rw [appendUnselected_values, happend, hcanonical]

end
end ImbalancedChen.P2OriginalSelectedNativeSmallExtension
