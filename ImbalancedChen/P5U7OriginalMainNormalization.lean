import ImbalancedChen.P5U7InteriorPairWeightCorrection

/-!
SOURCE_ONLY / UNCOMPILED. Exact finite normalization of the original U7
Buchstab rough-mother main. The original labelled pair, target-N carrier,
rho=59/250, and the second logarithmic denominator are preserved. The
fixed-eta interior identity is then linked to the raw-to-shifted correction.
-/

namespace ImbalancedChen

noncomputable section

open LiLiuPrereqBuchstab
open scoped BigOperators
open Classical

def p5U7MassRawFullTestSum (N : ℕ) : ℝ :=
  ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
    (1 / ((t.1 : ℝ) * (t.2 : ℝ))) *
      p5U7InteriorTest (actualPrimeTupleLog N ![t.1, t.2])

def p5U7MassBuchstabInteriorMain (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7InteriorSelector N eta,
    let x := (N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)
    x * buchstab (Real.log x / Real.log (t.2 : ℝ)) / Real.log (t.2 : ℝ)

/-- The logarithmic Buchstab argument is literally the original Omega
argument in logarithmic prime coordinates. -/
theorem p5U7_original_log_argument {N p q : ℕ}
    (hN : 2 ≤ N) (hp : 0 < p) (hq : 2 ≤ q) :
    Real.log ((N : ℝ) / ((p * q : ℕ) : ℝ)) / Real.log (q : ℝ) =
      (1 - (Real.log (p : ℝ) / Real.log (N : ℝ)) -
        (Real.log (q : ℝ) / Real.log (N : ℝ))) /
        (Real.log (q : ℝ) / Real.log (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hNlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hqlog : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  rw [Nat.cast_mul, Real.log_div hNpos.ne' (mul_ne_zero hppos.ne' hqpos.ne'),
    Real.log_mul hppos.ne' hqpos.ne']
  field_simp [hNlog.ne', hqlog.ne']
  <;> ring

/-- One original rough-mother summand, divided by N/log N. The extra /u
is retained; it comes from the original /log p2. -/
theorem p5U7_original_main_row_normalized {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) :
    (Real.log (N : ℝ) / (N : ℝ)) *
      (((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) *
        buchstab (Real.log ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) /
          Real.log (t.2 : ℝ)) / Real.log (t.2 : ℝ)) =
      (1 / ((t.1 : ℝ) * (t.2 : ℝ))) *
        p5U7InteriorTest (actualPrimeTupleLog N ![t.1, t.2]) := by
  obtain ⟨hc, _, _, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc1, hc2⟩ := Finset.mem_product.mp hc
  have hp := (mem_chenAdditivePrimeCarrier.mp hc1).2.1
  have hq := (mem_chenAdditivePrimeCarrier.mp hc2).2.1
  have hpR : (0 : ℝ) < t.1 := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < t.2 := by exact_mod_cast hq.pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hqlog : 0 < Real.log (t.2 : ℝ) :=
    Real.log_pos (by exact_mod_cast hq.one_lt)
  have harg := p5U7_original_log_argument hN hp.pos hq.two_le
  simp only [Nat.cast_mul] at harg
  simp only [p5U7InteriorTest, actualPrimeTupleLog,
    Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_mul]
  rw [harg]
  field_simp [hNR.ne', hpR.ne', hqR.ne', hNlog.ne', hqlog.ne']
  <;> ring

/-- The entire original Buchstab main is exactly a raw labelled
double-prime test after normalization. -/
theorem p5U7MassBuchstabMain_normalized_eq_raw_full {N : ℕ} (hN : 2 ≤ N) :
    (Real.log (N : ℝ) / (N : ℝ)) * p5U7MassBuchstabMain N =
      p5U7MassRawFullTestSum N := by
  unfold p5U7MassBuchstabMain p5U7MassRawFullTestSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact p5U7_original_main_row_normalized hN ht

/-- Restricting the same original source to the fixed-eta strict interior
commutes exactly with normalization. -/
theorem p5U7MassBuchstabInteriorMain_normalized_eq_raw {N : ℕ}
    (hN : 2 ≤ N) (eta : ℝ) :
    (Real.log (N : ℝ) / (N : ℝ)) * p5U7MassBuchstabInteriorMain N eta =
      p5U7InteriorRawTestSum N eta := by
  unfold p5U7MassBuchstabInteriorMain p5U7InteriorRawTestSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact p5U7_original_main_row_normalized hN (Finset.mem_filter.mp ht).1

/-- Literal inverse-of-N-over-log-N formulation for the original full
source main. -/
theorem p5U7MassBuchstabMain_inv_scale_eq_raw_full {N : ℕ} (hN : 2 ≤ N) :
    ((N : ℝ) / Real.log (N : ℝ))⁻¹ * p5U7MassBuchstabMain N =
      p5U7MassRawFullTestSum N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    _ = (Real.log (N : ℝ) / (N : ℝ)) * p5U7MassBuchstabMain N := by
      congr 1
      field_simp [hNR.ne', hNlog.ne']
    _ = p5U7MassRawFullTestSum N :=
      p5U7MassBuchstabMain_normalized_eq_raw_full hN

/-- The exact normalization feeds the finite denominator correction on
the original fixed-eta interior, without an assumed source-mass limit. -/
theorem p5U7MassBuchstabInteriorMain_shifted_correction {N : ℕ}
    (hN : 2 ≤ N) {eta : ℝ} (heta : 0 ≤ eta) :
    0 ≤ p5U7InteriorLabelledTestSum N eta -
      (Real.log (N : ℝ) / (N : ℝ)) * p5U7MassBuchstabInteriorMain N eta ∧
      p5U7InteriorLabelledTestSum N eta -
        (Real.log (N : ℝ) / (N : ℝ)) * p5U7MassBuchstabInteriorMain N eta ≤
          (8 / ((N : ℝ) ^ (59 / 250 : ℝ))) *
            ((Real.log (N : ℝ) / (N : ℝ)) *
              p5U7MassBuchstabInteriorMain N eta) := by
  rw [p5U7MassBuchstabInteriorMain_normalized_eq_raw hN eta]
  exact ⟨(p5U7Interior_raw_to_shifted_bound hN heta).1,
    p5U7Interior_raw_to_shifted_bound_by_raw hN heta⟩

end

end ImbalancedChen
