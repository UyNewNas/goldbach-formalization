import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-! Explicit common-denominator encoding for nonnegative rational vectors.
All literals are derived from the rationals' own numerator and denominator;
no host-generated numerical witness is required. -/
namespace ImbalancedChen.P2OriginalSaving19NonnegativeRationalEncoding
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

def denominator (q : ι → ℚ) : ℕ := ∏ i, (q i).den
def numerator (q : ι → ℚ) (i : ι) : ℕ :=
  (q i).num.toNat * (denominator q / (q i).den)

theorem denominator_pos (q : ι → ℚ) : 0 < denominator q :=
  Finset.prod_pos (fun i _ => (q i).den_pos)

theorem numerator_cast (q : ι → ℚ) (hq : ∀ i, 0 ≤ q i) (i : ι) :
    (numerator q i : ℚ) = q i * (denominator q : ℚ) := by
  classical
  have hd : (q i).den ∣ denominator q := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have he := Nat.div_mul_cancel hd
  have hden : ((q i).den : ℚ) ≠ 0 := by exact_mod_cast (q i).den_pos.ne'
  have hnum : ((q i).num.toNat : ℚ) = ((q i).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hq i))
  have hqnum : ((q i).num : ℚ) = q i * ((q i).den : ℚ) :=
    (div_eq_iff hden).mp (Rat.num_div_den (q i))
  have hscale : ((q i).den : ℚ) * ((denominator q / (q i).den : ℕ) : ℚ) =
      (denominator q : ℚ) := by
    exact_mod_cast (Nat.mul_comm (q i).den (denominator q / (q i).den)).trans he
  unfold numerator
  rw [Nat.cast_mul, hnum, hqnum, mul_assoc, hscale]

theorem encoding (q : ι → ℚ) (hq : ∀ i, 0 ≤ q i) (i : ι) :
    q i = (numerator q i : ℚ) / (denominator q : ℚ) := by
  apply (eq_div_iff (by exact_mod_cast (denominator_pos q).ne')).2
  exact (numerator_cast q hq i).symm

theorem numerator_sum_pos (q : ι → ℚ) (hq : ∀ i, 0 ≤ q i)
    (hpos : 0 < ∑ i, q i) : 0 < ∑ i, numerator q i := by
  have h : ((∑ i, numerator q i : ℕ) : ℚ) = (∑ i, q i) * (denominator q : ℚ) := by
    simp only [Nat.cast_sum, numerator_cast q hq, Finset.sum_mul]
  have hp : (0 : ℚ) < ((∑ i, numerator q i : ℕ) : ℚ) := by
    rw [h]
    exact mul_pos hpos (by exact_mod_cast denominator_pos q)
  exact_mod_cast hp

#print axioms numerator_cast
#print axioms encoding
#print axioms numerator_sum_pos
end ImbalancedChen.P2OriginalSaving19NonnegativeRationalEncoding
