import ImbalancedChen.P3HBOrderedFactorMajorant
import ImbalancedChen.P5LiteralHeathBrownOccurrenceWords

/-!
P3.6: actual order-three HB words, BEFORE any extra prime labels.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

The previous ordered-factor majorant was for a freely specified bounded
slot family.  Here the prefix is exactly the real-cutoff mu_Z occurrences
and the one-slots of the literal manuscript HB identity; the LAST occurrence
is the unique logarithm.  The original +3,-3,+1 scalar is retained.

This derives a true finite absolute coefficient bound at each nonzero
complete product, not a near-linear shifted-divisor asymptotic or a
fully labelled original PP compiler.  No Gamma mother-word or factorial
normalization is silently identified with an HB log slot.
-/

namespace ImbalancedChen.P3HBLiteralWordMajorant

noncomputable section
open scoped Classical BigOperators ArithmeticFunction.zeta
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.RealTruncatedMobiusSupport

/-- The exact non-log prefix of the ORIGINAL j-th order-three HB word. -/
def hbPrefix (y : ℝ) (j : ℕ) : List (ArithmeticFunction ℝ) :=
  List.replicate (j + 1) (muTrunc y) ++
    List.replicate j (ζ : ArithmeticFunction ℝ)

theorem hbWord_eq_prefix_log (y : ℝ) (j : ℕ) :
    hbWord y j = hbPrefix y j ++ [ArithmeticFunction.log] := rfl

/-- The real-cutoff Möbius slot is genuinely one-bounded, including
values beyond the literal real cutoff and at n=0. -/
theorem muTrunc_abs_le_one (y : ℝ) (n : ℕ) :
    |muTrunc y n| ≤ 1 := by
  by_cases hn : (n : ℝ) ≤ y
  · rw [muTrunc_of_le hn]
    rcases ArithmeticFunction.moebius_eq_or n with h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
  · rw [muTrunc_of_gt (lt_of_not_ge hn)]
    simp

/-- The original one-slots are zeta slots, not extra log marks. -/
theorem zeta_abs_le_one (n : ℕ) :
    |(ζ : ArithmeticFunction ℝ) n| ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp [ArithmeticFunction.zeta_apply_ne hn]

theorem hbPrefix_one_bounded (y : ℝ) (j : ℕ) :
    ∀ f ∈ hbPrefix y j, ∀ n : ℕ, |f n| ≤ 1 := by
  intro f hf n
  rcases List.mem_append.mp hf with hm | hz
  · have heq : f = muTrunc y :=
      List.eq_of_mem_replicate hm
    rw [heq]
    exact muTrunc_abs_le_one y n
  · have heq : f = (ζ : ArithmeticFunction ℝ) :=
      List.eq_of_mem_replicate hz
    rw [heq]
    exact zeta_abs_le_one n

/-- Any one-bounded prefix followed by exactly ONE actual log slot
is bounded by the logarithm of its POSITIVE complete product.
The proof follows the ordered factors, not a fibre-level assertion. -/
theorem bounded_prefix_log_product :
    ∀ fs : List (ArithmeticFunction ℝ),
      (∀ f ∈ fs, ∀ n : ℕ, |f n| ≤ 1) →
      ∀ ps : List ℕ, ps.length = fs.length + 1 →
        0 < ps.prod →
        |tupleWeight (fs ++ [ArithmeticFunction.log]) ps| ≤
          Real.log (ps.prod : ℝ) := by
  intro fs
  induction fs with
  | nil =>
      intro _ ps hlen hprod
      cases ps with
      | nil => simp at hlen
      | cons p ps =>
          cases ps with
          | nil =>
              have hp : 0 < p := by simpa using hprod
              have hlog : 0 ≤ Real.log (p : ℝ) :=
                Real.log_nonneg (by exact_mod_cast (Nat.one_le_of_lt hp))
              simpa [tupleWeight, ArithmeticFunction.log_apply,
                abs_of_nonneg hlog]
          | cons q qs =>
              simp at hlen
  | cons f fs ih =>
      intro hfs ps hlen hprod
      cases ps with
      | nil => simp at hlen
      | cons p qs =>
          have hlen' : qs.length = fs.length + 1 := by simpa using hlen
          have hmul : p * qs.prod ≠ 0 :=
            Nat.ne_of_gt (by simpa using hprod)
          have hp : 0 < p :=
            Nat.pos_of_ne_zero (mul_ne_zero_iff.mp hmul).1
          have hq : 0 < qs.prod :=
            Nat.pos_of_ne_zero (mul_ne_zero_iff.mp hmul).2
          have htail : ∀ f' ∈ fs, ∀ n : ℕ, |f' n| ≤ 1 := by
            intro f' hf' n
            exact hfs f' (List.mem_cons_of_mem f hf') n
          have hi := ih htail qs hlen' hq
          have hf : |f p| ≤ 1 := hfs f (by simp) p
          have hsize : qs.prod ≤ p * qs.prod := by
            calc
              qs.prod = 1 * qs.prod := by simp
              _ ≤ p * qs.prod :=
                Nat.mul_le_mul_right _ (Nat.one_le_of_lt hp)
          have hlogle : Real.log (qs.prod : ℝ) ≤
              Real.log ((p * qs.prod : ℕ) : ℝ) :=
            Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hsize)
          change |f p * tupleWeight (fs ++ [ArithmeticFunction.log]) qs| ≤
            Real.log ((p * qs.prod : ℕ) : ℝ)
          rw [abs_mul]
          calc
            |f p| * |tupleWeight (fs ++ [ArithmeticFunction.log]) qs|
                ≤ 1 * |tupleWeight (fs ++ [ArithmeticFunction.log]) qs| :=
                  mul_le_mul_of_nonneg_right hf (abs_nonneg _)
            _ ≤ Real.log (qs.prod : ℝ) := by simpa using hi
            _ ≤ Real.log ((p * qs.prod : ℕ) : ℝ) := hlogle

/-- The original HB word has 2(j+1) actual ordered occurrences.
For a nonzero product it is bounded without any artificial bounded-log
hypothesis on unrelated integers. -/
theorem literal_hb_word_abs_le_log (y : ℝ) (j n : ℕ)
    (hn : n ≠ 0) (ps : List ℕ)
    (hps : ps ∈ factorTuples (2 * (j + 1)) n) :
    |tupleWeight (hbWord y j) ps| ≤ Real.log (n : ℝ) := by
  have hs := factorTuples_spec (2 * (j + 1)) n ps hps
  have hlen : ps.length = (hbPrefix y j).length + 1 := by
    rw [hs.1]
    simp only [hbPrefix, List.length_append, List.length_replicate]
    omega
  have hpos : 0 < ps.prod := by
    rw [hs.2.1]
    exact Nat.pos_of_ne_zero hn
  have h := bounded_prefix_log_product (hbPrefix y j)
    (hbPrefix_one_bounded y j) ps hlen hpos
  simpa only [← hbWord_eq_prefix_log, hs.2.1] using h

/-- The literal original HB coefficient's ABSOLUTE ordered-fibre mass.
This does not fold equal tuples together or change the original signs. -/
def literalHBAbsMass (y : ℝ) (j n : ℕ) : ℝ :=
  ∑ ps ∈ factorTuples (2 * (j + 1)) n,
    |tupleWeight (hbWord y j) ps|

theorem literalHBAbsMass_le_card_log (y : ℝ) (j n : ℕ)
    (hn : n ≠ 0) :
    literalHBAbsMass y j n ≤
      Real.log (n : ℝ) * ((factorTuples (2 * (j + 1)) n).card : ℝ) := by
  unfold literalHBAbsMass
  calc
    _ ≤ ∑ _ps ∈ factorTuples (2 * (j + 1)) n, Real.log (n : ℝ) := by
      apply Finset.sum_le_sum
      intro ps hps
      exact literal_hb_word_abs_le_log y j n hn ps hps
    _ = Real.log (n : ℝ) *
        ((factorTuples (2 * (j + 1)) n).card : ℝ) := by
      simp [mul_comm]

/-- The EXACT original binomial magnitudes 3,3,1 multiply the
respective actual HB-word masses. No arbitrary coefficient compiler
or global source tag is inserted. -/
theorem literalHBThreeTermAbsMass_le (y : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (∑ j ∈ Finset.range 3,
      (Nat.choose 3 (j + 1) : ℝ) * literalHBAbsMass y j n)
      ≤ Real.log (n : ℝ) *
        (∑ j ∈ Finset.range 3,
          (Nat.choose 3 (j + 1) : ℝ) *
            ((factorTuples (2 * (j + 1)) n).card : ℝ)) := by
  calc
    _ ≤ ∑ j ∈ Finset.range 3,
          (Nat.choose 3 (j + 1) : ℝ) *
            (Real.log (n : ℝ) *
              ((factorTuples (2 * (j + 1)) n).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (literalHBAbsMass_le_card_log y j n hn) (Nat.cast_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

end
end ImbalancedChen.P3HBLiteralWordMajorant
