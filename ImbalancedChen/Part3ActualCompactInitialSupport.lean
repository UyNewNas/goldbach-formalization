import ImbalancedChen.ActualExtendedThirdCompactUpperRho
import ImbalancedChen.ActualRoughVectorEndpointBudget
import Mathlib.Tactic

/-!
# Full original square support from actual third admission

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The full-square hypothesis in the endpoint allocator is discharged here
for an actual retained third history and its fourth successor.  The
initial cube comes from the same physical compact cell; the third cube
comes from the literal policy's retention test.  The fourth prime needs
only its original decreasing order.  No square-support, branch license,
spectral estimate, or replacement arithmetic coefficient is assumed.

The endpoint theorem uses the complete local scale x and the exact
log(N)/log(x) exponent.  Its five-slot-charge is four original factors
plus the additional occurrence in a square.  Longer histories, the
small attachment, all whole-box tensors, and the signed spectral estimate
are still separate obligations.
-/

namespace ImbalancedChen.Part3.ActualCompactInitialSupport

noncomputable section

open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

/-- The odd first and third cubes pay every original square through rank
three.  The second square uses the preceding cube and decreasing order. -/
theorem triple_support_of_cubes {D : ℝ} (p0 p1 p2 : ℕ)
    (hp2 : 0 < p2) (h21 : p2 ≤ p1) (h10 : p1 ≤ p0)
    (hfirst : (p0 : ℝ) ^ 3 < D)
    (hthird : (p0 : ℝ) * p1 * p2 ^ 3 < D) :
    actualDwellSupport D [p0, p1, p2] := by
  have hp0 : (1 : ℝ) ≤ p0 := by exact_mod_cast (show 1 ≤ p0 by omega)
  have hp2r : (1 : ℝ) ≤ p2 := by exact_mod_cast (show 1 ≤ p2 from hp2)
  have h10r : (p1 : ℝ) ≤ p0 := by exact_mod_cast h10
  have hs0 : (p0 : ℝ) ^ 2 ≤ D :=
    (pow_le_pow_right₀ hp0 (by norm_num : 2 ≤ 3)).trans hfirst.le
  have hs1 : (p0 : ℝ) * p1 ^ 2 ≤ D := by
    calc
      (p0 : ℝ) * p1 ^ 2 ≤ (p0 : ℝ) * p0 ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg p1) h10r 2)
          (Nat.cast_nonneg p0)
      _ = (p0 : ℝ) ^ 3 := by ring
      _ ≤ D := hfirst.le
  have hs2 : (p0 : ℝ) * p1 * p2 ^ 2 ≤ D :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hp2r (by norm_num : 2 ≤ 3))
      (mul_nonneg (Nat.cast_nonneg p0) (Nat.cast_nonneg p1))).trans hthird.le
  intro i hi
  have hi3 : i < 3 := by simpa using hi
  interval_cases i
  · simpa using hs0
  · simpa using hs1
  · simpa [mul_assoc] using hs2

/-- The automatically retained fourth selection needs no new cubic test:
its square is paid by the already admitted third cube. -/
theorem fourth_support_of_cubes {D : ℝ} (p0 p1 p2 p3 : ℕ)
    (hp2 : 0 < p2) (h32 : p3 ≤ p2) (h21 : p2 ≤ p1) (h10 : p1 ≤ p0)
    (hfirst : (p0 : ℝ) ^ 3 < D)
    (hthird : (p0 : ℝ) * p1 * p2 ^ 3 < D) :
    actualDwellSupport D [p0, p1, p2, p3] := by
  have h32r : (p3 : ℝ) ≤ p2 := by exact_mod_cast h32
  have hs3 : (p0 : ℝ) * p1 * p2 * p3 ^ 2 ≤ D := by
    calc
      (p0 : ℝ) * p1 * p2 * p3 ^ 2 ≤ (p0 : ℝ) * p1 * p2 * p2 ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg p3) h32r 2)
          (by positivity)
      _ = (p0 : ℝ) * p1 * p2 ^ 3 := by ring
      _ ≤ D := hthird.le
  apply (prefixSquareBound_append_singleton_iff
    (fun p : ℕ => (p : ℝ)) D [p0, p1, p2] p3).2
  exact ⟨triple_support_of_cubes p0 p1 p2 hp2 h21 h10 hfirst hthird,
    by simpa [mul_assoc] using hs3⟩

/-- Actual membership and actual retention, not a supplied license, yield
the original support required by the deterministic factor allocator. -/
theorem actual_compact_retained_third_support {e h : ℝ} {m N : ℕ}
    (hN : 1 < N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (p0 p1 p2 : ℕ) (hp2 : 0 < p2) (h21 : p2 < p1) (h10 : p1 < p0)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (ht : primeHistoryLogCoordinates (N : ℝ) 3 [p2, p1, p0] ∈
      actualExtendedThirdOwnedCell m j)
    (hret : actualExtendedThirdCompactUpperPolicy e h m N false [p2, p1, p0] = true) :
    actualDwellSupport ((N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j)
      [p0, p1, p2] := by
  have hfirst := actualExtendedThirdCompactCell_prime_firstCube hN he0 he hmesh
    p0 p1 p2 (by omega) hj ht
  have hthird := (actualExtendedThirdCompactUpperPolicy_third_iff hN he0 he hmesh
    p0 p1 p2 hp2 h21 h10 hj ht).mp hret
  exact triple_support_of_cubes p0 p1 p2 hp2 h21.le h10.le hfirst hthird

/-- The fourth-prime path has exactly the same compact ancestor and level.
Its even retention is unconditional, whereas all its square bounds are
proved from the actual preceding odd retention. -/
theorem actual_compact_retained_fourth_support {e h : ℝ} {m N : ℕ}
    (hN : 1 < N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (p0 p1 p2 p3 : ℕ) (hp2 : 0 < p2)
    (h32 : p3 ≤ p2) (h21 : p2 < p1) (h10 : p1 < p0)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (ht : primeHistoryLogCoordinates (N : ℝ) 3 [p2, p1, p0] ∈
      actualExtendedThirdOwnedCell m j)
    (hret : actualExtendedThirdCompactUpperPolicy e h m N false [p2, p1, p0] = true) :
    actualExtendedThirdCompactUpperPolicy e h m N true [p3, p2, p1, p0] = true ∧
      actualDwellSupport ((N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j)
        [p0, p1, p2, p3] := by
  have hfirst := actualExtendedThirdCompactCell_prime_firstCube hN he0 he hmesh
    p0 p1 p2 (by omega) hj ht
  have hthird := (actualExtendedThirdCompactUpperPolicy_third_iff hN he0 he hmesh
    p0 p1 p2 hp2 h21 h10 hj ht).mp hret
  exact ⟨actualExtendedThirdCompactUpperPolicy_even e h m N _,
    fourth_support_of_cubes p0 p1 p2 p3 hp2 h32 h21.le h10.le hfirst hthird⟩

/-- Exact exponent transport, including arbitrary signed levels. -/
theorem physical_power_eq_local {N x : ℝ} (hN : 0 < N) (hx : 1 < x) (lam : ℝ) :
    N ^ lam = x ^ ((Real.log N / Real.log x) * lam) := by
  rw [Real.rpow_def_of_pos hN, Real.rpow_def_of_pos (zero_lt_one.trans hx)]
  congr 1
  field_simp [(Real.log_pos hx).ne']
  <;> ring

/-- The generic endpoint inflation theorem is applied after exact
physical-to-complete-local scale conversion, with the original list intact. -/
theorem physical_support_upper_local {ι : Type*} {N x tau lam theta : ℝ} {R : ℕ}
    (hN : 0 < N) (hx : 1 < x) (htau : 0 ≤ tau)
    (actual upper : ι → ℕ) (input : List ι) (hlen : input.length ≤ R)
    (hsize : ∀ i ∈ input, (upper i : ℝ) ≤ x ^ tau * (actual i : ℝ))
    (hphysical : actualDwellSupport (N ^ lam) (input.map actual))
    (hbudget : (Real.log N / Real.log x) * lam + tau * (R + 1) ≤ theta) :
    actualDwellSupport (x ^ theta) (input.map upper) := by
  rw [physical_power_eq_local hN hx lam] at hphysical
  exact actualDwellSupport_upper_inflation hx htau actual upper input hlen hsize
    hphysical hbudget

/-- Concrete rank-four whole-box endpoint support.  Its assumptions are
literal policy retention, original ordering, endpoint inflation, and an
explicit exponent budget.  In particular there is no hsupport premise. -/
theorem actual_compact_fourth_upper_local {e h x tau theta : ℝ} {m N : ℕ}
    (hN : 1 < N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (p upper : Fin 4 → ℕ) (hp2 : 0 < p 2)
    (h32 : p 3 ≤ p 2) (h21 : p 2 < p 1) (h10 : p 1 < p 0)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (ht : primeHistoryLogCoordinates (N : ℝ) 3 [p 2, p 1, p 0] ∈
      actualExtendedThirdOwnedCell m j)
    (hret : actualExtendedThirdCompactUpperPolicy e h m N false [p 2, p 1, p 0] = true)
    (hx : 1 < x) (htau : 0 ≤ tau)
    (hsize : ∀ i, (upper i : ℝ) ≤ x ^ tau * (p i : ℝ))
    (hbudget : (Real.log (N : ℝ) / Real.log x) *
      actualExtendedThirdPhysicalLevel e m j + 5 * tau ≤ theta) :
    actualDwellSupport (x ^ theta) [upper 0, upper 1, upper 2, upper 3] := by
  have hs := (actual_compact_retained_fourth_support hN he0 he hmesh
    (p 0) (p 1) (p 2) (p 3) hp2 h32 h21 h10 hj ht hret).2
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hphys : actualDwellSupport ((N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j)
      (([0, 1, 2, 3] : List (Fin 4)).map p) := by simpa using hs
  have hlocal := physical_support_upper_local (R := 4) (theta := theta) hNr hx htau p upper
    ([0, 1, 2, 3] : List (Fin 4)) (by simp) (fun i _ => hsize i) hphys
    (by simpa [mul_comm] using hbudget)
  simpa using hlocal

end

end ImbalancedChen.Part3.ActualCompactInitialSupport
