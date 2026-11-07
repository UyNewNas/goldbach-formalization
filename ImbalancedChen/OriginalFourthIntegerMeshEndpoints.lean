import ImbalancedChen.OriginalFourthOwnedEndpointBuffer
import ImbalancedChen.LogPrimeBoxMesh

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

Natural endpoints for the actual original endpoint-vector construction.
One half of tau pays logarithmic cell width; the other half pays ceiling
rounding. A single finite mesh is chosen before N and before any source
point, dimension or cell label. The eventual threshold is also uniform
over every cell, occurrence and natural prime label. Half-open ownership
and its strict upper endpoint are retained.

This supplies the endpoint-size primitive used by the original causal
buffer theorem, rather than assuming a natural endpoint inflation bound.
No archived certificate is executed or claimed to pass.
-/

namespace ImbalancedChen.OriginalFourthIntegerMeshEndpoints20261026b

noncomputable section
open Filter Topology
open scoped Classical

/-- The real upper endpoint and its exact natural ceiling both contain
the original integer. Cell width and integer rounding each use tau/2. -/
theorem ceil_endpoint_inflation (x tau l u : ℝ) (hx : 1 < x)
    (hround : 2 ≤ x ^ (tau / 2)) (hu0 : 0 ≤ u)
    (hwidth : u - l ≤ tau / 2) (p : ℕ)
    (hlo : x ^ l ≤ (p : ℝ)) (hhi : (p : ℝ) < x ^ u) :
    p ≤ Nat.ceil (x ^ u) ∧ (Nat.ceil (x ^ u) : ℝ) ≤ x ^ tau * (p : ℝ) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hupper1 : (1 : ℝ) ≤ x ^ u := Real.one_le_rpow hx.le hu0
  have hupper0 : 0 ≤ x ^ u := Real.rpow_nonneg hx0.le u
  have hcell : x ^ u ≤ x ^ (tau / 2) * (p : ℝ) := by
    calc
      x ^ u ≤ x ^ (l + tau / 2) :=
        Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
      _ = x ^ (tau / 2) * x ^ l := by rw [Real.rpow_add hx0]; ring
      _ ≤ x ^ (tau / 2) * (p : ℝ) :=
        mul_le_mul_of_nonneg_left hlo (Real.rpow_nonneg hx0.le _)
  have hdouble : x ^ (tau / 2) * x ^ (tau / 2) = x ^ tau := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  constructor
  · exact_mod_cast hhi.le.trans (Nat.le_ceil (x ^ u))
  · calc
      (Nat.ceil (x ^ u) : ℝ) ≤ x ^ u + 1 := (Nat.ceil_lt_add_one hupper0).le
      _ ≤ 2 * x ^ u := by linarith
      _ ≤ 2 * (x ^ (tau / 2) * (p : ℝ)) := mul_le_mul_of_nonneg_left hcell (by norm_num)
      _ ≤ x ^ (tau / 2) * (x ^ (tau / 2) * (p : ℝ)) :=
        mul_le_mul_of_nonneg_right hround
          (mul_nonneg (Real.rpow_nonneg hx0.le _) (Nat.cast_nonneg p))
      _ = x ^ tau * (p : ℝ) := by rw [← mul_assoc, hdouble]

/-- The rounding threshold depends only on tau and precedes all cells
and source points. The mesh has already been fixed. -/
theorem eventually_all_mesh_integer_endpoints (tau : ℝ) (htau : 0 < tau)
    (n : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96 : ℝ) n ≤ tau / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ (d : ℕ) (j : Fin d → Fin (n + 1)) (p : Fin d → ℕ),
      (∀ i, (N : ℝ) ^ logPrimeMeshLo 0 (19 / 96 : ℝ) n j i ≤ (p i : ℝ) ∧
        (p i : ℝ) < (N : ℝ) ^ logPrimeMeshHi 0 (19 / 96 : ℝ) n j i) →
      ∀ i, p i ≤ Nat.ceil ((N : ℝ) ^ logPrimeMeshHi 0 (19 / 96 : ℝ) n j i) ∧
        (Nat.ceil ((N : ℝ) ^ logPrimeMeshHi 0 (19 / 96 : ℝ) n j i) : ℝ) ≤
          (N : ℝ) ^ tau * (p i : ℝ) := by
  have hlarge : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (tau / 2) :=
    ((tendsto_rpow_atTop (half_pos htau)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hlarge, eventually_ge_atTop (2 : ℕ)] with N hround hN
  intro d j p hp i
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hb := logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 19 / 96) n j i
  apply ceil_endpoint_inflation (N : ℝ) tau
    (logPrimeMeshLo 0 (19 / 96 : ℝ) n j i)
    (logPrimeMeshHi 0 (19 / 96 : ℝ) n j i) hNr hround
    (le_trans hb.1 hb.2.1.le) ?_ (p i) (hp i).1 (hp i).2
  rw [logPrimeMeshHi_eq_lo_add_step]
  linarith

/-- A SINGLE finite logarithmic mesh works before the arithmetic scale,
all dimensions, every original raw occurrence, and all half-open cells. -/
theorem exists_uniform_integer_mesh (tau : ℝ) (htau : 0 < tau) :
    ∃ n : ℕ, logPrimeMeshStep 0 (19 / 96 : ℝ) n ≤ tau / 2 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (d : ℕ) (j : Fin d → Fin (n + 1)) (p : Fin d → ℕ),
        (∀ i, (N : ℝ) ^ logPrimeMeshLo 0 (19 / 96 : ℝ) n j i ≤ (p i : ℝ) ∧
          (p i : ℝ) < (N : ℝ) ^ logPrimeMeshHi 0 (19 / 96 : ℝ) n j i) →
        ∀ i, p i ≤ Nat.ceil ((N : ℝ) ^ logPrimeMeshHi 0 (19 / 96 : ℝ) n j i) ∧
          (Nat.ceil ((N : ℝ) ^ logPrimeMeshHi 0 (19 / 96 : ℝ) n j i) : ℝ) ≤
            (N : ℝ) ^ tau * (p i : ℝ) := by
  obtain ⟨n, hn⟩ := ((tendsto_logPrimeMeshStep 0 (19 / 96 : ℝ)).eventually
    (gt_mem_nhds (half_pos htau))).exists
  exact ⟨n, hn.le, eventually_all_mesh_integer_endpoints tau htau n hn.le⟩

end
end ImbalancedChen.OriginalFourthIntegerMeshEndpoints20261026b
