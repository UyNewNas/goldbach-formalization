import ImbalancedChen.OriginalPairedN48OmegaStepArithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual 48-term reversed Horner program and its original /97 tail,
not the coarser RationalLogCertificate tail.  Positive denominator tokens
are obtained from the existing *arithmetic* SourceProducerValid clause.
No U-array, producer/checker, or Omega evaluator is executed here.
-/

namespace ImbalancedChen.OriginalPairedN48SmallLogSoundness

noncomputable section

open Set LiLiuPrereqBuchstab
open scoped BigOperators
open Certificates.P2DirectedLogRounding
open OriginalN48Q112LocalProduct
open OriginalPairedN48OmegaProducerAdapter
open OriginalPairedN48OmegaTrapezoidStep
open OriginalPairedN48OmegaStepArithmetic

def oddSum (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, x ^ (2 * k + 1) / (2 * (k : ℝ) + 1)

/-- The sharper original remainder follows from the derivative of the
proved finite-logarithm remainder.  The comparison function keeps the
denominator 1-x^2 fixed while its argument varies from 0 to x. -/
theorem original_48_term_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    2 * oddSum x 48 ≤ Real.log ((1 + x) / (1 - x)) ∧
    Real.log ((1 + x) / (1 - x)) ≤
      2 * oddSum x 48 + 2 * x ^ 97 / (97 * (1 - x ^ 2)) := by
  let F : ℝ → ℝ := fun y =>
    1 / 2 * Real.log ((1 + y) / (1 - y)) - oddSum y 48
  let G : ℝ → ℝ := fun y => y ^ 97 / (97 * (1 - x ^ 2))
  let H : ℝ → ℝ := fun y => G y - F y
  have hden : 0 < 1 - x ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hx1)
      (show 0 < 1 + x by linarith only [hx0])
    nlinarith only [hp]
  have hD : ∀ y ∈ Icc 0 x,
      HasDerivAt H (y ^ 96 / (1 - x ^ 2) - y ^ 96 / (1 - y ^ 2)) y := by
    intro y hy
    have hF := Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range
      48 (show -1 < y by linarith only [hy.1])
      (show y < 1 by linarith only [hy.2, hx1])
    have hpow : (y ^ 2) ^ 48 = y ^ 96 := by
      rw [← pow_mul]
      norm_num
    rw [hpow] at hF
    have hG : HasDerivAt G (y ^ 96 / (1 - x ^ 2)) y := by
      convert (hasDerivAt_pow 97 y).div_const (97 * (1 - x ^ 2)) using 1
      <;> dsimp only [G]
      <;> norm_num
      <;> field_simp [hden.ne']
      <;> ring
    exact hG.sub hF
  have hmono : MonotoneOn H (Icc 0 x) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun y hy => (hD y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hD y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    have hyy : y ∈ Icc 0 x := interior_subset hy
    have hcomp : 1 - x ^ 2 ≤ 1 - y ^ 2 := by
      have hp := mul_nonneg (sub_nonneg.mpr hyy.2) (add_nonneg hx0 hyy.1)
      nlinarith only [hp]
    exact sub_nonneg.mpr
      (div_le_div_of_nonneg_left (pow_nonneg hyy.1 96) hden hcomp)
  have hcmp := hmono ⟨le_rfl, hx0⟩ ⟨hx0, le_rfl⟩ hx0
  have hzero : H 0 = 0 := by simp [H, G, F, oddSum]
  rw [hzero] at hcmp
  have hlo := Real.sum_range_le_log_div hx0 hx1 48
  change oddSum x 48 ≤ 1 / 2 * Real.log ((1 + x) / (1 - x)) at hlo
  dsimp [H, G, F] at hcmp
  constructor <;> linarith only [hlo, hcmp]

def coefficient (k : ℕ) : ℚ := 1 / (2 * (k : ℚ) + 1)

/-- Soundness for the actual left-fold operation, with a signed accumulator
and an arbitrary list of original coefficient indices. -/
theorem source_horner_fold_contains (ks : List ℕ) (Z : Token) {z : ℝ}
    (hz : (decode Z).Contains z) (A : Token) {a : ℝ}
    (ha : (decode A).Contains a) :
    (decode (ks.foldl
      (fun acc k => sourceAdd (rational (coefficient k)) (sourceMul Z acc)) A)).Contains
      (ks.foldl (fun acc k => (coefficient k : ℝ) + z * acc) a) := by
  induction ks generalizing A a with
  | nil => simpa only [List.foldl_nil] using ha
  | cons k ks ih =>
    simp only [List.foldl_cons]
    exact ih _ (sourceAdd_contains _ _ (rational_contains (coefficient k))
      (sourceMul_contains Z A hz ha))

/-- Exact algebra for the producer's reversed order.  Retaining the free
accumulator makes the induction follow `range(n+1).reverse` literally. -/
theorem reverse_horner_identity (n : ℕ) (z a : ℝ) :
    (List.range n).reverse.foldl
      (fun acc k => (coefficient k : ℝ) + z * acc) a =
      (∑ k ∈ Finset.range n, (coefficient k : ℝ) * z ^ k) + z ^ n * a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    rw [ih, Finset.sum_range_succ, pow_succ]
    ring

theorem logPoly_contains (Z : Token) {z : ℝ}
    (hz : (decode Z).Contains z) :
    (decode (logPoly Z)).Contains
      (∑ k ∈ Finset.range 48, (coefficient k : ℝ) * z ^ k) := by
  have h := source_horner_fold_contains (List.range 48).reverse Z hz
    (rational 0) (rational_contains 0)
  rw [reverse_horner_identity] at h
  simpa only [logPoly, coefficient, Rat.cast_zero, mul_zero, add_zero] using h

theorem sourcePow_contains (U : Token) {u : ℝ}
    (hu : (decode U).Contains u) (n : ℕ) :
    (decode (sourcePow U n)).Contains (u ^ n) := by
  induction n with
  | zero => simpa only [sourcePow, pow_zero, Rat.cast_one] using rational_contains 1
  | succ n ih =>
    simpa only [sourcePow, pow_succ] using sourceMul_contains _ _ ih hu

theorem sourceNeg_contains (A : Token) {a : ℝ}
    (ha : (decode A).Contains a) :
    (decode (sourceNeg A)).Contains (-a) := by
  have he : decode (sourceNeg A) = (decode A).neg := by
    apply congrArg₂ Enclosure.mk
    <;> simp only [decode, sourceNeg, Enclosure.neg, Int.cast_neg, neg_div]
  rw [he]
  exact Enclosure.neg_contains ha

theorem sourceSub_contains (A B : Token) {a b : ℝ}
    (ha : (decode A).Contains a) (hb : (decode B).Contains b) :
    (decode (sourceSub A B)).Contains (a - b) := by
  simpa only [sourceSub, sub_eq_add_neg] using
    sourceAdd_contains A (sourceNeg B) ha (sourceNeg_contains B hb)

private theorem parameter_bounds {q : ℚ} (hq : 1 ≤ q) :
    0 ≤ logX q ∧ logX q < 1 := by
  have hd : 0 < q + 1 := by linarith only [hq]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hq) hd.le
  · exact (div_lt_one hd).2 (by linarith)

private theorem parameter_identity {q : ℚ} (hq : 1 ≤ q) :
    (1 + logX q) / (1 - logX q) = q := by
  have hd : q + 1 ≠ 0 := ne_of_gt (by linarith only [hq] : 0 < q + 1)
  have hu := (parameter_bounds hq).2
  have hdu : 1 - logX q ≠ 0 := ne_of_gt (by linarith only [hu])
  unfold logX
  field_simp [hd, hdu]
  <;> ring

/-- Exact identification of the Horner output with the finite odd sum. -/
theorem twice_parameter_horner (x : ℝ) :
    2 * x * (∑ k ∈ Finset.range 48, (coefficient k : ℝ) * (x * x) ^ k) =
      2 * oddSum x 48 := by
  unfold oddSum
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hp : (x * x) ^ k = x ^ (2 * k) := by rw [← pow_two, ← pow_mul]
  rw [hp, pow_succ]
  simp only [coefficient, Rat.cast_div, Rat.cast_one, Rat.cast_add,
    Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]
  ring

/-- Directed soundness of the *literal* original small-log producer.
The positivity gate is precisely its existing arithmetic denominator
clause, not an assumption about the logarithm or the final enclosure. -/
theorem sourceSmallLog_contains {q : ℚ} (hq : 1 ≤ q)
    (hpositive : 0 < (sourceSub (rational 1)
      (sourceMul (rational (logX q)) (rational (logX q)))).lo) :
    (decode (sourceSmallLog q)).Contains (Real.log (q : ℝ)) := by
  let U := rational (logX q)
  let Z := sourceMul U U
  let result := sourceMul (sourceMul (rational 2) U) (logPoly Z)
  let tail := sourceDiv
    (sourceDiv (sourceMul (rational 2) (sourcePow U 97)) (rational 97))
    (sourceSub (rational 1) Z)
  let x : ℝ := (logX q : ℝ)
  have hx := parameter_bounds hq
  have hx0 : 0 ≤ x := by exact_mod_cast hx.1
  have hx1 : x < 1 := by exact_mod_cast hx.2
  have hu : (decode U).Contains x := rational_contains (logX q)
  have hz : (decode Z).Contains (x * x) := sourceMul_contains U U hu hu
  have hr := sourceMul_contains (sourceMul (rational 2) U) (logPoly Z)
    (sourceMul_contains (rational 2) U (rational_contains 2) hu)
    (logPoly_contains Z hz)
  simp only [Rat.cast_ofNat] at hr
  rw [twice_parameter_horner] at hr
  have hn := sourceMul_contains (rational 2) (sourcePow U 97)
    (rational_contains 2) (sourcePow_contains U hu 97)
  have ht97 := sourceDiv_contains _ (rational 97)
    (rational_lower_pos (by norm_num : (1 : ℚ) ≤ 97)) hn
    (rational_contains 97)
  have hd := sourceSub_contains (rational 1) Z (rational_contains 1) hz
  have ht := sourceDiv_contains _ (sourceSub (rational 1) Z)
    hpositive ht97 hd
  simp only [Rat.cast_ofNat, Rat.cast_one] at ht
  have he : ((2 * x ^ 97) / 97) / (1 - x * x) =
      2 * x ^ 97 / (97 * (1 - x ^ 2)) := by rw [pow_two]; ring
  rw [he] at ht
  have hid : (1 + x) / (1 - x) = (q : ℝ) := by
    exact_mod_cast parameter_identity hq
  have hb := original_48_term_bounds hx0 hx1
  rw [hid] at hb
  have hrlo : (result.lo : ℝ) / (P : ℝ) ≤ 2 * oddSum x 48 := by
    simpa only [decode, Enclosure.Contains, Rat.cast_div, Rat.cast_intCast] using hr.1
  have hrhi : 2 * oddSum x 48 ≤ (result.hi : ℝ) / (P : ℝ) := by
    simpa only [decode, Enclosure.Contains, Rat.cast_div, Rat.cast_intCast] using hr.2
  have hthi : 2 * x ^ 97 / (97 * (1 - x ^ 2)) ≤ (tail.hi : ℝ) / (P : ℝ) := by
    simpa only [decode, Enclosure.Contains, Rat.cast_div, Rat.cast_intCast] using ht.2
  have hlo : (result.lo : ℝ) / (P : ℝ) ≤ Real.log (q : ℝ) := hrlo.trans hb.1
  have hhi : Real.log (q : ℝ) ≤
      (result.hi : ℝ) / (P : ℝ) + (tail.hi : ℝ) / (P : ℝ) := by
    linarith only [hrhi, hthi, hb.2]
  simpa only [sourceSmallLog, decode, Enclosure.Contains, Rat.cast_div,
    Rat.cast_intCast, Int.cast_add, add_div] using And.intro hlo hhi

/-- Soundness of the actual original logarithmic branch of U, with
the positivity gate supplied by the exact existing producer predicate. -/
theorem logarithmic_U_contains (p : SourceArrays) (hp : SourceProducerValid p)
    (i : ℕ) (hic : i < uCount) (hil : 2 * mesh < i) (hiu : i ≤ 3 * mesh) :
    (decode (Uat p i)).Contains
      (((i : ℝ) / (mesh : ℝ)) * buchstab ((i : ℝ) / (mesh : ℝ))) := by
  rcases hp with ⟨_, _, _, _, hpositive, hrows, _⟩
  have hpos := hpositive ⟨i, hic⟩ hil hiu
  have hmQ : (0 : ℚ) < mesh := by norm_num [mesh]
  have hmR : (0 : ℝ) < mesh := by norm_num [mesh]
  have hmN : 0 < mesh := by norm_num [mesh]
  have hk : mesh ≤ i - mesh := by omega
  have hq : 1 ≤ logArg i := by
    unfold logArg
    apply (le_div_iff₀ hmQ).2
    simpa only [one_mul] using (show (mesh : ℚ) ≤ (i - mesh : ℕ) by exact_mod_cast hk)
  have hlog := sourceSmallLog_contains hq hpos
  have hsum := sourceAdd_contains (rational 1) (sourceSmallLog (logArg i))
    (rational_contains 1) hlog
  have hidx : (i - mesh : ℕ) + mesh = i := by omega
  have hqR : (logArg i : ℝ) = (i : ℝ) / (mesh : ℝ) - 1 := by
    have hreal : ((i - mesh : ℕ) : ℝ) + (mesh : ℝ) = (i : ℝ) :=
      by exact_mod_cast hidx
    unfold logArg
    push_cast
    field_simp [hmR.ne']
    linarith only [hreal]
  have hs2 : (2 : ℝ) ≤ (i : ℝ) / (mesh : ℝ) := by
    apply (le_div_iff₀ hmR).2
    exact_mod_cast hil.le
  have hs3 : (i : ℝ) / (mesh : ℝ) ≤ 3 := by
    apply (div_le_iff₀ hmR).2
    exact_mod_cast hiu
  have hs0 : (i : ℝ) / (mesh : ℝ) ≠ 0 := by linarith only [hs2]
  have hweight : ((i : ℝ) / (mesh : ℝ)) *
      buchstab ((i : ℝ) / (mesh : ℝ)) = 1 + Real.log (logArg i : ℝ) := by
    rw [buchstab_eq_log_div hs2 hs3, hqR]
    field_simp [hs0]
  have heq := hrows ⟨i, hic⟩
  simp only [Fin.val_mk] at heq
  rw [if_neg (by omega : ¬i ≤ 2 * mesh), if_pos hiu] at heq
  rw [heq, hweight]
  simpa only [Rat.cast_one] using hsum

/-- The previous batch's initial logarithm premise is now discharged.
Only the separately stated genuine trapezoid error remains analytic input. -/
theorem all_weighted_nodes_of_original_local_error (p : SourceArrays)
    (hp : SourceProducerValid p)
    (herror : ∀ i : ℕ, 3 * mesh < i → i < uCount →
      SharpCellError (((i - 1 : ℕ) : ℝ) / (mesh : ℝ))
        ((i : ℝ) / (mesh : ℝ))) :
    ∀ i : ℕ, mesh ≤ i → i < uCount → (decode (Uat p i)).Contains
      (((i : ℝ) / (mesh : ℝ)) * buchstab ((i : ℝ) / (mesh : ℝ))) := by
  exact all_weighted_nodes_of_local_errors p hp
    (fun i hil hiu hic => logarithmic_U_contains p hp i hic hil hiu) herror

end
end ImbalancedChen.OriginalPairedN48SmallLogSoundness
