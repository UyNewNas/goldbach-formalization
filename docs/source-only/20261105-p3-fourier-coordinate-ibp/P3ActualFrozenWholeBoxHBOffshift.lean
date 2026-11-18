import ImbalancedChen.P3ActualFrozenThreeWholeBoxHBTarget
import ImbalancedChen.P3ActualMarkedOffShiftDivisors

/-!
P3.6 manuscript-internal full physical nonzero-shift reduction for the
actual frozen THREE independent fine-prime boxes and the genuine literal
strict-rough HB occurrence.  Unlike a diagonal-only zero statement, this
retains every original nonzero complete-product term, all four ordered
source words, the original positional W, original signed rho, and the
exact coprime mean.  No product-Mobius substitution or normalization of
repeated labels is made.  This is an exact finite reduction, NOT a shifted
moment bound, not compiler exhaustiveness, not a PP theorem.
Pinned manuscript: 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product-completion §§2–4.  SOURCE_ONLY / UNCOMPILED.
-/

namespace ImbalancedChen.P3ActualFrozenWholeBoxHBOffshift
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualFrozenThreeWholeBoxHBTarget
open ImbalancedChen.P3ActualMarkedOffShiftDivisors
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P3HBOriginalMarkedFineTarget
open ImbalancedChen.P3ActualFrozenTaggedPrimeBox
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords

/-- The entire three-box plus HB physical error, not merely its exact
product=N fibre.  There is only one physical product. -/
def threeWholeHBAtQ (N m j q : ℕ) (τ z y : ℝ)
    (u v w : List ℕ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ) : ℂ :=
  let B := actualPrimeFineLabelFinset N τ
  ∑ a ∈ actualPrimeSlotBox B u,
    ∑ b ∈ actualPrimeSlotBox B v,
      ∑ d ∈ actualPrimeSlotBox B w,
        ∑ h ∈ factorTuples (2 * (j + 1)) m,
          (W a b d h * roughTupleWeight z y (roles j) h) *
            ((fineKernel N q (a.prod * b.prod * d.prod * h.prod) : ℝ) : ℂ)

/-- All original HB words retained; the full physical nonzero integer
shift is tested before Nat.divisors is formed. -/
def threeWholeHBOffDivisorsAtQ (N m j q : ℕ) (τ z y : ℝ)
    (u v w : List ℕ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ) : ℂ :=
  let B := actualPrimeFineLabelFinset N τ
  ∑ a ∈ actualPrimeSlotBox B u,
    ∑ b ∈ actualPrimeSlotBox B v,
      ∑ d ∈ actualPrimeSlotBox B w,
        ∑ h ∈ (factorTuples (2 * (j + 1)) m).filter
            (fun h => a.prod * b.prod * d.prod * h.prod ≠ N),
          (W a b d h * roughTupleWeight z y (roles j) h) *
            (((if q ∈ (markedShiftAbs (a.prod * b.prod * d.prod) N h.prod).divisors
               then (1 : ℝ) else 0) -
              (if Nat.Coprime (a.prod * b.prod * d.prod * h.prod) q
               then (Nat.totient q : ℝ)⁻¹ else 0)) : ℂ)

/-- Source-level main step.  Every product=N term is annihilated by
the actual fine-prime/strict-rough HB coefficient, while every other
term uses the genuine complete shifted integer, not a residual shift.
The exact coprime indicator stays inside the signed kernel. -/
theorem threeWholeHBAtQ_eq_off_divisors
    (N m j q : ℕ) (τ z y : ℝ) (u v w : List ℕ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    threeWholeHBAtQ N m j q τ z y u v w W =
      threeWholeHBOffDivisorsAtQ N m j q τ z y u v w W := by
  unfold threeWholeHBAtQ threeWholeHBOffDivisorsAtQ
  dsimp
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro d hd
  let S : Finset (List ℕ) := factorTuples (2 * (j + 1)) m
  let r : ℕ := a.prod * b.prod * d.prod
  let f : List ℕ → ℂ := fun h =>
    (W a b d h * roughTupleWeight z y (roles j) h) *
      ((fineKernel N q (r * h.prod) : ℝ) : ℂ)
  let g : List ℕ → ℂ := fun h =>
    (W a b d h * roughTupleWeight z y (roles j) h) *
      (((if q ∈ (markedShiftAbs r N h.prod).divisors
         then (1 : ℝ) else 0) -
        (if Nat.Coprime (r * h.prod) q
         then (Nat.totient q : ℝ)⁻¹ else 0)) : ℂ)
  have hmarked : a ++ b ++ d ∈
      actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) (u ++ v ++ w) :=
    three_prime_boxes_whole_mem _ u v w a b d ha hb hd
  have hdiag :
      (∑ h ∈ S.filter (fun h => r * h.prod = N), f h) = 0 := by
    apply Finset.sum_eq_zero
    intro h hh
    have hhb : h ∈ factorTuples (2 * (j + 1)) m :=
      (Finset.mem_filter.mp hh).1
    have hfull : (a ++ b ++ d).prod * h.prod = N := by
      simpa only [List.prod_append, mul_assoc, r] using
        (Finset.mem_filter.mp hh).2
    have hzero := original_marked_fine_rough_occurrence_target_zero
      N m j τ z y (u ++ v ++ w) (a ++ b ++ d) h
      hz hN hmarked hhb hfull
    dsimp [f]
    rw [hzero]
    simp
  have hoff :
      (∑ h ∈ S.filter (fun h => r * h.prod ≠ N), f h) =
        (∑ h ∈ S.filter (fun h => r * h.prod ≠ N), g h) := by
    apply Finset.sum_congr rfl
    intro h hh
    have hne : r * h.prod ≠ N := (Finset.mem_filter.mp hh).2
    dsimp [f, g]
    rw [fineKernel_marked_off_divisors r N q h.prod hne]
  change (∑ h ∈ S, f h) =
    (∑ h ∈ S.filter (fun h => r * h.prod ≠ N), g h)
  calc
    (∑ h ∈ S, f h) =
      (∑ h ∈ S.filter (fun h => r * h.prod = N), f h) +
      (∑ h ∈ S.filter (fun h => r * h.prod ≠ N), f h) := by
        rw [Finset.sum_filter_add_sum_filter_not]
    _ = ∑ h ∈ S.filter (fun h => r * h.prod ≠ N), f h := by
      rw [hdiag, zero_add]
    _ = _ := hoff

/-- Actual original-ID frozen selection: the same simultaneous source
and original full-product shift for all three groups. -/
theorem frozenThreeWholeHB_off_divisors {n : ℕ}
    (N m j q : ℕ) (τ z y D A : ℝ) (yz : Bool)
    (upper : Fin n → ℕ) (label : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    let ids := actualFrozenSelectedPairSlots D A yz upper p tail
    threeWholeHBAtQ N m j q τ z y
      (ids.1.map label) (ids.2.1.map label) (ids.2.2.map label) W =
    threeWholeHBOffDivisorsAtQ N m j q τ z y
      (ids.1.map label) (ids.2.1.map label) (ids.2.2.map label) W := by
  dsimp only
  exact threeWholeHBAtQ_eq_off_divisors N m j q τ z y _ _ _ W hz hN

/-- The ORIGINAL physical Q and a SINGLE signed integer rho(q) survive
in both the congruence count and exact coprime mean, including all
three original HB signs (+3,-3,+1).  No absolute value is taken before
the original q sum.  This equality is not an asymptotic PP estimate. -/
theorem frozenThreeWholeSameRho_off_divisors {n : ℕ}
    (N m : ℕ) (τ z y D A : ℝ) (yz : Bool)
    (upper : Fin n → ℕ) (label : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : ℕ → List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    let ids := actualFrozenSelectedPairSlots D A yz upper p tail
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          threeWholeHBAtQ N m j q τ z y
            (ids.1.map label) (ids.2.1.map label)
            (ids.2.2.map label) (W j)) =
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          threeWholeHBOffDivisorsAtQ N m j q τ z y
            (ids.1.map label) (ids.2.1.map label)
            (ids.2.2.map label) (W j)) := by
  dsimp only
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [threeWholeHBAtQ_eq_off_divisors N m j q τ z y
    _ _ _ (W j) hz hN]

end
end ImbalancedChen.P3ActualFrozenWholeBoxHBOffshift
