import ImbalancedChen.Part3OriginalReciprocalMaskSeparation
import ImbalancedChen.Part3OriginalMediumAbelOneCoordinate

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Quantitative Abel removal of the ACTUAL w1 rectangle/product gate and
the original 1/s1 denominator. The charge is at most 2/S, S=2^k.u,
against the maximum of the unweighted arithmetic-unit reciprocal
prefixes. This maximum has NO product endpoint or r1 parameter in its
coefficient. Its subsequent simultaneous spectral estimate is OPEN.

This is not the five-coordinate retained-phase variation payment.
That earlier analytic weight must still be paid once, as in the paper.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalActualFrozenSmoothPackets20261102
open ImbalancedChen.Part3.OriginalFrozenReciprocalCauchy20261102
open ImbalancedChen.Part3.OriginalFrozenReciprocalMask20261102
open ImbalancedChen.Part3.OriginalReciprocalMaskSeparation20261102
open ImbalancedChen.Part3.OriginalMediumAbelOneCoordinate
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028

namespace ImbalancedChen.Part3.OriginalReciprocalProductAbel20261102

attribute [local instance] Classical.propDecidable

def prefixEnvelope (c : ℕ → ℂ) (N : ℕ) : ℝ :=
  (insert 0 ((range (N+1)).image (fun i => ‖prefix c i‖))).max'
    ⟨0, by simp⟩

theorem prefixEnvelope_nonneg (c : ℕ → ℂ) (N : ℕ) :
    0 ≤ prefixEnvelope c N :=
  Finset.le_max' _ _ (by simp)

theorem prefix_le_envelope (c : ℕ → ℂ) {N i : ℕ} (hi : i ≤ N) :
    ‖prefix c i‖ ≤ prefixEnvelope c N := by
  apply Finset.le_max'
  apply mem_insert.mpr
  exact Or.inr (mem_image.mpr ⟨i, mem_range.mpr (by omega), rfl⟩)

private theorem sum_forward_drop (w : ℕ → ℝ) (N : ℕ) :
    w N + ∑ i ∈ range N, (w i - w (i+1)) = w 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    linarith

/-- The weight variation is evaluated, not postulated. For a positive
decreasing weight, endpoint plus total variation is exactly w(0). -/
theorem antitone_weight_variation (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ i, 0 ≤ w i) (hmono : Antitone w) :
    ‖(w N : ℂ)‖ + ∑ i ∈ range N,
      ‖((w (i+1) : ℂ) - (w i : ℂ))‖ = w 0 := by
  have hn : ‖(w N : ℂ)‖ = w N := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw N)]
  have hd (i : ℕ) : ‖((w (i+1) : ℂ) - (w i : ℂ))‖ = w i - w (i+1) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (hmono (by omega : i ≤ i+1)))]
    ring
  rw [hn]
  simp_rw [hd]
  exact sum_forward_drop w N

theorem antitone_weighted_norm (c : ℕ → ℂ) (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ i, 0 ≤ w i) (hmono : Antitone w) :
    ‖∑ i ∈ range (N+1), c i * (w i : ℂ)‖ ≤
      prefixEnvelope c N * w 0 := by
  have hp := prefixEnvelope_nonneg c N
  calc
    _ ≤ ‖prefix c N‖ * ‖(w N : ℂ)‖ +
        ∑ i ∈ range N, ‖prefix c i‖ *
          ‖((w (i+1) : ℂ) - (w i : ℂ))‖ :=
      abel_once_norm c (fun i => (w i : ℂ)) N
    _ ≤ prefixEnvelope c N * ‖(w N : ℂ)‖ +
        ∑ i ∈ range N, prefixEnvelope c N *
          ‖((w (i+1) : ℂ) - (w i : ℂ))‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (prefix_le_envelope c le_rfl) (norm_nonneg _)
      · apply sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right
          (prefix_le_envelope c (by have := mem_range.mp hi; omega)) (norm_nonneg _)
    _ = prefixEnvelope c N * w 0 := by
      rw [← mul_sum, ← mul_add, antitone_weight_variation w N hw hmono]

/-- A product upper cutoff, with its ORIGINAL reciprocal s weight. -/
def upperWeight (S r cutoff i : ℕ) : ℝ :=
  if (S+i)*r ≤ cutoff then ((S+i : ℕ) : ℝ)⁻¹ else 0

theorem upperWeight_nonneg (S r cutoff i : ℕ) :
    0 ≤ upperWeight S r cutoff i := by
  unfold upperWeight
  split_ifs <;> positivity

theorem upperWeight_antitone {S : ℕ} (hS : 0 < S) (r cutoff : ℕ) :
    Antitone (upperWeight S r cutoff) := by
  intro i j hij
  have hi : (0 : ℝ) < (S+i : ℕ) := by exact_mod_cast (by omega : 0 < S+i)
  have hijR : ((S+i : ℕ) : ℝ) ≤ (S+j : ℕ) := by exact_mod_cast Nat.add_le_add_left hij S
  by_cases hj : (S+j)*r ≤ cutoff
  · have hicut : (S+i)*r ≤ cutoff :=
      (Nat.mul_le_mul_right r (Nat.add_le_add_left hij S)).trans hj
    simp only [upperWeight, if_pos hj, if_pos hicut]
    simpa only [one_div] using one_div_le_one_div_of_le hi hijR
  · simp only [upperWeight, if_neg hj]
    exact upperWeight_nonneg S r cutoff i

theorem upperWeight_variation_le {S : ℕ} (hS : 0 < S)
    (r cutoff N : ℕ) :
    ‖(upperWeight S r cutoff N : ℂ)‖ + ∑ i ∈ range N,
      ‖((upperWeight S r cutoff (i+1) : ℂ) -
        (upperWeight S r cutoff i : ℂ))‖ ≤ (S : ℝ)⁻¹ := by
  rw [antitone_weight_variation _ _ (upperWeight_nonneg S r cutoff)
    (upperWeight_antitone hS r cutoff)]
  unfold upperWeight
  split_ifs <;> simp <;> positivity

theorem upper_weighted_norm {S : ℕ} (hS : 0 < S)
    (c : ℕ → ℂ) (r cutoff : ℕ) :
    ‖∑ i ∈ range S, c i * (upperWeight S r cutoff i : ℂ)‖ ≤
      prefixEnvelope c (S-1) / (S : ℝ) := by
  have hlen : S-1+1 = S := by omega
  have h := antitone_weighted_norm c (upperWeight S r cutoff) (S-1)
    (upperWeight_nonneg S r cutoff) (upperWeight_antitone hS r cutoff)
  rw [hlen] at h
  apply h.trans
  have h0 : upperWeight S r cutoff 0 ≤ (S : ℝ)⁻¹ := by
    unfold upperWeight
    split_ifs <;> simp <;> positivity
  simpa only [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_left h0 (prefixEnvelope_nonneg c (S-1))

private theorem clipped_product_window (L U v : ℕ) (hL : 0 < L) (Z : ℂ) :
    (if L ≤ v ∧ v ≤ U then Z else 0) =
      (if v ≤ U then Z else 0) - (if v ≤ min U (L-1) then Z else 0) := by
  by_cases hU : v ≤ U
  · by_cases hLo : L ≤ v
    · have hn : ¬ v ≤ min U (L-1) := by omega
      simp [hU, hLo, hn]
    · have hmin : v ≤ min U (L-1) := by omega
      simp [hU, hLo, hmin]
  · have hn : ¬ v ≤ min U (L-1) := by omega
    simp [hU, hn]

/-- Original coefficients and common h interval. The only arithmetic
gate is the required (s,|a|c)=1. There is no product or rectangle-w1
endpoint, no r1-dependent coefficient, and no future m dependence. -/
def bareSAtom (B : FixedBlock) (atom : MediumAtom) (z : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ) (e : Fin 4)
    (o : Outer) (s : ℕ) : ℂ :=
  if s ∈ commonS atom z k small st ∧
      s.Coprime (B.atom.residue.natAbs * packetC o) then
    lambdaS atom st st' e s * ∑ h ∈ commonH B R,
      ActualReciprocalSquarePoissonSourceOnly.phase B.atom.residue o.f
        (packetB o) (packetC o) (s,h)
  else 0

def shiftedBare (B : FixedBlock) (atom : MediumAtom) (z : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ) (e : Fin 4)
    (o : Outer) (i : ℕ) : ℂ :=
  bareSAtom B atom z k small R st st' e o (2 ^ k.u + i)

def upperWeightedRow (B : FixedBlock) (atom : MediumAtom) (z : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ) (e : Fin 4)
    (o : Outer) (cutoff : ℕ) : ℂ :=
  ∑ i ∈ range (2 ^ k.u), shiftedBare B atom z k small R st st' e o i *
    (upperWeight (2 ^ k.u) o.r1 cutoff i : ℂ)

theorem commonS_sum_shift (atom : MediumAtom) (z : ℝ) (k : Key)
    (small : ℕ) (st : ℕ × ℕ) (f : ℕ → ℂ) :
    (∑ s ∈ commonS atom z k small st, f s) =
      ∑ i ∈ range (2 ^ k.u),
        if 2 ^ k.u + i ∈ commonS atom z k small st then f (2 ^ k.u + i) else 0 := by
  rw [← sum_filter]
  symm
  apply Finset.sum_bij (fun i _ => 2 ^ k.u + i)
  · intro i hi
    exact (mem_filter.mp hi).2
  · intro i hi j hj he
    omega
  · intro s hs
    obtain ⟨hlo, hhi⟩ := commonS_window atom z k small st hs
    refine ⟨s - 2 ^ k.u, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, ?_⟩
    · have he : 2 ^ k.u + (s - 2 ^ k.u) = s := by omega
      simpa only [he] using hs
    · omega
  · intro i hi
    rfl

/-- Exact product-cutoff removal, including empty/reversed original
rectangles. Clipping the lower upper-cutoff handles those cases without
assuming a nonempty interval or discarding an endpoint. -/
theorem separatedRow_eq_two_upperWeighted (B : FixedBlock) (atom : MediumAtom)
    (z : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br : ℕ)
    (st st' : ℕ × ℕ) (e : Fin 4) (o : Outer) :
    separatedRow B atom z k small R Br st st' e o =
      upperWeightedRow B atom z k small R st st' e o (productHi B R Br) -
      upperWeightedRow B atom z k small R st st' e o
        (min (productHi B R Br) (productLo B R - 1)) := by
  unfold separatedRow
  rw [commonS_sum_shift]
  unfold upperWeightedRow
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  let s := 2 ^ k.u + i
  have hgate := clipped_product_window (productLo B R) (productHi B R Br)
    (s * o.r1) (productLo_pos B R)
    ((lambdaS atom st st' e s / (s : ℂ)) *
      ∑ h ∈ commonH B R, ActualReciprocalSquarePoissonSourceOnly.phase
        B.atom.residue o.f (packetB o) (packetC o) (s,h))
  by_cases hs : s ∈ commonS atom z k small st
  · by_cases hu : s.Coprime (B.atom.residue.natAbs * packetC o)
    · simpa only [shiftedBare, bareSAtom, upperWeight, innerAtom,
        ← mul_sum, div_eq_mul_inv, Complex.ofReal_inv, Complex.ofReal_natCast,
        apply_ite, mul_ite, Complex.ofReal_zero, mul_zero,
        hs, hu, true_and, and_true, if_true, mul_assoc, mul_left_comm, mul_comm]
        using hgate
    · simp only [shiftedBare, bareSAtom, innerAtom, hs, hu, and_false,
        false_and, if_true, if_false, zero_mul, sub_self]
  · simp only [shiftedBare, bareSAtom, hs, false_and, if_false,
      zero_mul, sub_self]

def rowEnvelope (B : FixedBlock) (atom : MediumAtom) (z : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ) (e : Fin 4) (o : Outer) : ℝ :=
  prefixEnvelope (shiftedBare B atom z k small R st st' e o) (2 ^ k.u - 1)

theorem rowEnvelope_nonneg (B : FixedBlock) (atom : MediumAtom) (z : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ) (e : Fin 4) (o : Outer) :
    0 ≤ rowEnvelope B atom z k small R st st' e o :=
  prefixEnvelope_nonneg _ _

theorem separatedRow_norm_le (B : FixedBlock) (atom : MediumAtom)
    (z : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br : ℕ)
    (st st' : ℕ × ℕ) (e : Fin 4) (o : Outer) :
    ‖separatedRow B atom z k small R Br st st' e o‖ ≤
      2 * rowEnvelope B atom z k small R st st' e o / (2 ^ k.u : ℕ) := by
  rw [separatedRow_eq_two_upperWeighted]
  have hS : 0 < (2 : ℕ) ^ k.u := pow_pos (by omega) _
  have h1 := upper_weighted_norm hS (shiftedBare B atom z k small R st st' e o)
    o.r1 (productHi B R Br)
  have h2 := upper_weighted_norm hS (shiftedBare B atom z k small R st st' e o)
    o.r1 (min (productHi B R Br) (productLo B R - 1))
  change ‖upperWeightedRow B atom z k small R st st' e o (productHi B R Br)‖ ≤
    rowEnvelope B atom z k small R st st' e o / (2 ^ k.u : ℕ) at h1
  change ‖upperWeightedRow B atom z k small R st st' e o
    (min (productHi B R Br) (productLo B R - 1))‖ ≤
      rowEnvelope B atom z k small R st st' e o / (2 ^ k.u : ℕ) at h2
  exact (norm_sub_le _ _).trans (by linarith)

/-- Actual J source, not an equality hypothesis: the entire w1
rectangle/product mask and reciprocal weight have now been paid by 2/S.
The true prefix norms remain explicit and are not assumed small. -/
theorem original_row_norm_le_product_Abel (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e : Fin 4) (o : Outer) :
    ‖row B atom z y k small R Br Bs st st' e o‖ ≤
      2 * rowEnvelope B atom z k small R st st' e o / (2 ^ k.u : ℕ) := by
  rw [original_row_eq_separated]
  split_ifs
  · exact separatedRow_norm_le B atom z k small R Br st st' e o
  · rw [norm_zero]
    exact div_nonneg (mul_nonneg (by norm_num) (rowEnvelope_nonneg _ _ _ _ _ _ _ _ _ _))
      (Nat.cast_nonneg _)

end ImbalancedChen.Part3.OriginalReciprocalProductAbel20261102
