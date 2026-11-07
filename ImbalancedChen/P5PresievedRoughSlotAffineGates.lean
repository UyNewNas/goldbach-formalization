import ImbalancedChen.P5OriginalPresievedRoughSlotCoefficient
import ImbalancedChen.Part3ActualCompactAllRankSupport

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact affine logarithmic gates at EVERY fixed rough rank, including zero.
The odd-cardinality original upper Rosser tests are exactly the even
zero-based cubic-prefix rows. Total product and all endpoints stay strict.
Whole fine boxes are certified by their actual upper endpoints, before
any arithmetic discrepancy or group assignment is inspected.
-/
namespace ImbalancedChen.P5Z.PresievedRoughSlotAffineGates
noncomputable section
open Classical
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
open Part3.ActualCompactAllRankSupport

def prefix {r : ℕ} (v : Fin r → ℝ) (i : Fin r) : ℝ := ∑ j : Fin r with j.val < i.val, v j

def cube {r : ℕ} (v : Fin r → ℝ) (i : Fin r) : ℝ := prefix v i + 3 * v i

def totalRow (r : ℕ) : (Fin r → ℝ) →L[ℝ] ℝ := ∑ i : Fin r, ContinuousLinearMap.proj i

def cubeRow {r : ℕ} (i : Fin r) : (Fin r → ℝ) →L[ℝ] ℝ :=
  (∑ j : Fin r with j.val < i.val, ContinuousLinearMap.proj j) + (3 : ℝ) • ContinuousLinearMap.proj i

theorem cubeRow_apply {r : ℕ} (i : Fin r) (v : Fin r → ℝ) : cubeRow i v = cube v i := by
  simp [cubeRow, cube, prefix, ContinuousLinearMap.sum_apply, smul_eq_mul]

def region (r : ℕ) (ell : ℝ) : Set (Fin r → ℝ) :=
  {v | (∑ i : Fin r, v i) < ell ∧ ∀ i : Fin r, Even i.val → cube v i < ell}

/-- Exact arithmetic index dictionary for the original odd-cardinality
set filter, with no parity test removed and no full-square substitution. -/
theorem original_upper_iff_indexed {r : ℕ} (L : ℝ) (p : Fin r → ℕ) (hdesc : StrictAnti p) :
    UpperAdmissibleSet L (List.ofFn p).toFinset ↔
      ∀ i : Fin r, Even i.val →
        (∏ j : Fin r with j.val < i.val, (p j : ℝ)) * (p i : ℝ) ^ 3 < L := by
  have hsort : (List.ofFn p).Pairwise (· > ·) := List.pairwise_ofFn.mpr hdesc
  constructor
  · intro h i hi
    have hc := upper_set_indexed_cubes (List.ofFn p) hsort h i.val
      (by simpa using i.isLt) (by simpa only [Nat.even_iff] using hi)
    simpa only [List.prod_take_ofFn, List.getElem_ofFn, actualNatList_cast_prod,
      Nat.cast_prod, List.length_ofFn] using hc
  · intro h q hq hodd
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hq)
    have hi : i.val < (List.ofFn p).length := by simpa using i.isLt
    have hf := decreasing_filter_eq_take (List.ofFn p) hsort i.val hi
    have hnd : ((List.ofFn p).take (i.val + 1)).Nodup :=
      hsort.nodup.sublist (List.take_sublist _ _)
    have hcard : (((List.ofFn p).toFinset).filter (fun q => p i ≤ q)).card = i.val + 1 := by
      simpa only [List.getElem_ofFn] using congrArg Finset.card hf |>.trans
        (by rw [List.toFinset_card_of_nodup hnd, List.length_take, List.length_ofFn,
          Nat.min_eq_left (by omega)])
    have heven : Even i.val := by
      rw [hcard, Nat.even_iff] at hodd
      rw [Nat.even_iff]
      omega
    have hp : ((List.ofFn p).take (i.val + 1)).toFinset.prod id =
        ((List.ofFn p).take (i.val + 1)).prod := by
      simpa using List.prod_toFinset (fun q : ℕ => q) hnd
    have hf' : (((List.ofFn p).toFinset).filter (fun q => p i ≤ q)) =
        ((List.ofFn p).take (i.val + 1)).toFinset := by simpa only [List.getElem_ofFn] using hf
    rw [hf', hp, List.take_succ_eq_append_getElem hi]
    simpa only [List.prod_append, List.prod_singleton, List.prod_take_ofFn,
      List.getElem_ofFn, Nat.cast_mul, Nat.cast_prod, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h i heven

theorem total_rpow {r N : ℕ} (hN : 1 < N) (p : Fin r → ℕ) (hp : ∀ i, 0 < p i) :
    (N : ℝ) ^ (∑ i : Fin r, actualPrimeTupleLog N p i) = ((List.ofFn p).prod : ℝ) := by
  rw [Real.rpow_sum_of_pos (by exact_mod_cast (zero_lt_one.trans hN)), List.prod_ofFn, Nat.cast_prod]
  exact Finset.prod_congr rfl (fun i hi => actualPrimeTupleLog_rpow hN p hp i)

theorem cube_rpow {r N : ℕ} (hN : 1 < N) (p : Fin r → ℕ) (hp : ∀ i, 0 < p i) (i : Fin r) :
    (N : ℝ) ^ cube (actualPrimeTupleLog N p) i =
      (∏ j : Fin r with j.val < i.val, (p j : ℝ)) * (p i : ℝ) ^ 3 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans hN)
  have h3 : (N : ℝ) ^ (3 * actualPrimeTupleLog N p i) = (p i : ℝ) ^ 3 := by
    rw [mul_comm (3 : ℝ), Real.rpow_mul hn.le, Real.rpow_natCast,
      actualPrimeTupleLog_rpow hN p hp i]
  rw [cube, Real.rpow_add hn, prefix, Real.rpow_sum_of_pos hn, h3]
  congr 1
  exact Finset.prod_congr rfl (fun j hj => actualPrimeTupleLog_rpow hN p hp j)

/-- Literal original upper predicate at the SAME scale N is equivalent
to this finite strict affine gate region; every rank is covered. -/
theorem original_upper_prefix_iff_log {r N : ℕ} (hN : 1 < N) (ell : ℝ)
    (p : Fin r → ℕ) (hp : ∀ i, 0 < p i) (hdesc : StrictAnti p) :
    ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ ell) (List.ofFn p).reverse ↔
      actualPrimeTupleLog N p ∈ region r ell := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  simp only [ordinaryRosserPrefixAdmissible, Bool.false_eq_true, if_false,
    List.prod_reverse, List.toFinset_reverse, original_upper_iff_indexed _ _ hdesc]
  change (((List.ofFn p).prod : ℝ) < (N : ℝ) ^ ell ∧ _) ↔ _
  rw [← total_rpow hN p hp, Real.rpow_lt_rpow_left_iff hn]
  apply and_congr_right
  intro htotal
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro hi
  rw [← cube_rpow hN p hp i, Real.rpow_lt_rpow_left_iff hn]

/-- An actual fine-label box is certified at its upper corner. Positive
coefficients of every ORIGINAL cube row make this a whole-box assertion. -/
theorem fine_box_region {r : ℕ} (ell : ℝ) (a b : Fin r → ℝ)
    (htotal : (∑ i : Fin r, b i) < ell)
    (hcubes : ∀ i : Fin r, Even i.val → cube b i < ell) :
    logPrimeBox a b ⊆ region r ell := by
  intro v hv
  have hb : ∀ i, v i ≤ b i := fun i => (mem_logPrimeBox.mp hv i).2.le
  refine ⟨(Finset.sum_le_sum (fun i hi => hb i)).trans_lt htotal, ?_⟩
  intro i hi
  apply lt_of_le_of_lt ?_ (hcubes i hi)
  unfold cube prefix
  exact add_le_add (Finset.sum_le_sum (fun j hj => hb j)) (mul_le_mul_of_nonneg_left (hb i) (by norm_num))

end
end ImbalancedChen.P5Z.PresievedRoughSlotAffineGates
