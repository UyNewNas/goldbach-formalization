import ImbalancedChen.ActualRoughVectorEndpointBudget

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

The missing SELECTED endpoint budget: both the selected natural product
and every chronological complementary square are inflated. At remainder
index i the full cost is (selected.length+i+2)*tau, not (i+2)*tau.
Consequently the complete rank budget pays the quotient by B_UPPER.

The input is primitive support at ORIGINAL B. No upper-endpoint quotient
support, allocation, capacity lower bound or distribution estimate is an
assumption. Positivity of B_upper is derived from original positive slots
and natural lower endpoint containment. The native fifth instance supplies
the original quotient support from its actual winner gates and true leaf.
-/

namespace ImbalancedChen.OriginalSelectedEndpointQuotientInflation20261026b

noncomputable section
open scoped Classical

private theorem endpoint_product_bound (x tau : ℝ) (hx : 0 < x) (upper : ℕ → ℕ)
    (input : List ℕ) (hsize : ∀ p ∈ input, (upper p : ℝ) ≤ x ^ tau * (p : ℝ)) :
    ((input.map upper).prod : ℝ) ≤ (x ^ tau) ^ input.length * (input.prod : ℝ) := by
  have h := List.prod_map_le_prod_map₀ (fun p : ℕ => (upper p : ℝ))
    (fun p : ℕ => x ^ tau * (p : ℝ)) (fun p _ => Nat.cast_nonneg _) hsize
  simpa only [List.prod_map_mul, List.map_const', List.prod_replicate,
    ← actualNatList_cast_prod, List.map_map, Function.comp_def] using h

/-- Selected factors are INCLUDED in the endpoint exponent cost. -/
theorem selected_endpoint_quotient_support
    {x tau lam cover : ℝ} {R : ℕ} (hx : 1 < x) (htau : 0 ≤ tau)
    (selected remainder : List ℕ) (upper : ℕ → ℕ)
    (hpositive : ∀ p ∈ selected, 0 < p)
    (hlower : ∀ p ∈ selected, p ≤ upper p)
    (hsize : ∀ p ∈ selected ++ remainder, (upper p : ℝ) ≤ x ^ tau * (p : ℝ))
    (hrank : selected.length + remainder.length ≤ R)
    (hactual : actualDwellSupport (x ^ lam / (selected.prod : ℝ)) remainder)
    (hbudget : lam + tau * ((R : ℝ) + 1) ≤ cover) :
    selected.prod ≤ (selected.map upper).prod ∧ 0 < (selected.map upper).prod ∧
      actualDwellSupport (x ^ cover / ((selected.map upper).prod : ℝ)) (remainder.map upper) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hbNat : 0 < selected.prod := List.prod_pos hpositive
  have hb : (0 : ℝ) < selected.prod := by exact_mod_cast hbNat
  have hbuNat : 0 < (selected.map upper).prod := by
    apply List.prod_pos
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (hpositive q hq).trans_le (hlower q hq)
  have hbu : (0 : ℝ) < (selected.map upper).prod := by exact_mod_cast hbuNat
  have hlowerProd : selected.prod ≤ (selected.map upper).prod := by
    have h := List.prod_map_le_prod_map₀ (fun p : ℕ => (p : ℝ)) (fun p => (upper p : ℝ))
      (fun p _ => Nat.cast_nonneg _) (fun p hp => by exact_mod_cast hlower p hp)
    have h' : (selected.prod : ℝ) ≤ ((selected.map upper).prod : ℝ) := by
      simpa only [← actualNatList_cast_prod, List.map_map, Function.comp_def] using h
    exact_mod_cast h'
  refine ⟨hlowerProd, hbuNat, ?_⟩
  intro i hi
  have hi' : i < remainder.length := by simpa only [List.length_map] using hi
  have hsel := endpoint_product_bound x tau hx0 upper selected
    (fun p hp => hsize p (List.mem_append_left _ hp))
  have hpre := endpoint_product_bound x tau hx0 upper (remainder.take i)
    (fun p hp => hsize p (List.mem_append_right _ (List.mem_of_mem_take hp)))
  rw [List.length_take, Nat.min_eq_left hi'.le] at hpre
  have hq := hsize remainder[i] (List.mem_append_right _ (List.getElem_mem hi'))
  have hq2 := pow_le_pow_left₀ (Nat.cast_nonneg (upper remainder[i])) hq 2
  have hs := (le_div_iff₀ hb).mp (hactual i hi')
  have hbase : (selected.prod : ℝ) * ((remainder.take i).prod : ℝ) * (remainder[i] : ℝ) ^ 2 ≤ x ^ lam := by
    simpa only [actualNatList_cast_prod, mul_assoc, mul_comm, mul_left_comm] using hs
  have htest : ((selected.map upper).prod : ℝ) * (((remainder.take i).map upper).prod : ℝ) *
      (upper remainder[i] : ℝ) ^ 2 ≤ x ^ cover := by
    calc
      _ ≤ ((x ^ tau) ^ selected.length * (selected.prod : ℝ)) *
          ((x ^ tau) ^ i * ((remainder.take i).prod : ℝ)) *
          (x ^ tau * (remainder[i] : ℝ)) ^ 2 := by
        have hm := mul_le_mul hsel hpre (by positivity) (by positivity)
        exact mul_le_mul hm hq2 (by positivity) (by positivity)
      _ = (x ^ tau) ^ (selected.length + i + 2) *
          ((selected.prod : ℝ) * ((remainder.take i).prod : ℝ) * (remainder[i] : ℝ) ^ 2) := by
        rw [pow_add, pow_add]
        ring
      _ ≤ (x ^ tau) ^ (selected.length + i + 2) * x ^ lam :=
        mul_le_mul_of_nonneg_left hbase (pow_nonneg (Real.rpow_nonneg hx0.le _) _)
      _ = x ^ (tau * (selected.length + i + 2 : ℕ) + lam) := by
        rw [Real.rpow_add hx0, Real.rpow_mul_natCast hx0.le]
      _ ≤ x ^ cover := by
        apply Real.rpow_le_rpow_of_exponent_le hx.le
        have hcount : ((selected.length + i + 2 : ℕ) : ℝ) ≤ (R : ℝ) + 1 := by
          exact_mod_cast (show selected.length + i + 2 ≤ R + 1 by omega)
        nlinarith
  apply (le_div_iff₀ hbu).mpr
  simp only [← List.map_take, List.getElem_map, actualNatList_cast_prod]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using htest

end
end ImbalancedChen.OriginalSelectedEndpointQuotientInflation20261026b
