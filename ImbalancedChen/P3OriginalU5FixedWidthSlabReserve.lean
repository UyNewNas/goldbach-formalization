import ImbalancedChen.P1ActualMovingAffineSlab

/-!
# A fixed fine width for the actual warm-cap wall supplier

SOURCE ONLY / UNCOMPILED / NO FORMAL ACCEPTANCE.

This is the fixed-width consequence of the already existing arithmetic
slab envelope. The positive width is chosen before N and every real wall
center. It therefore also applies to the incoming cap of a warm pair run,
even when that cap depends on the external pair and on N.

The target-deleted prime carrier and the closed prime endpoint atom are
inherited from the existing envelope. No shrinking N-dependent mesh is
substituted for a fixed mesh. No actual mixed-fibre coverage, finite union
payment, density convergence, or P3.6 conclusion is asserted here.

Manuscript: release-20261106/en/coefficient-appendix.tex, "Finite
approximation and strict margins"; sieve-appendix.tex, the lower
coefficient realization. The quantitative envelope itself is reused from
the fixed P15 source, not reproved here.
-/

namespace ImbalancedChen.P3OriginalU5FixedWidthSlabReserve

noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P1ActualMovingPrimeIntervalEnvelope
open P1ActualMovingCoordinateSlab
open P1ActualMovingAffineSlab
open P1OriginalFourthMovingPrimeIntervalBound

/-- Reserve, then a positive fixed width, then a common threshold; every
real center is quantified after both choices. This includes moving warm
caps without assuming that those caps have a limit. -/
theorem exists_fixed_width_uniform_center_reserve {k : ℕ}
    (a b v : Fin (k + 1) → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (j : Fin (k + 1)) (hv : v j ≠ 0)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ center : ℝ,
        affineSlabMass N a b v center delta < eta := by
  obtain ⟨K, hK, hinterval⟩ := exists_uniform_reciprocal_interval_bound
  have hK0 : 0 ≤ K := by linarith
  let tailLimit : ℝ :=
    ∏ i : Fin k, Real.log ((j.removeNth b) i / (j.removeNth a) i)
  let C : ℝ := |tailLimit| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have htailLimit : tailLimit < C := by
    dsimp [C]
    linarith [le_abs_self tailLimit]
  let delta : ℝ := eta * |v j| * a j / (8 * C)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact div_pos (mul_pos (mul_pos heta (abs_pos.mpr hv)) (ha j)) (by positivity)
  have htail :=
    (tendsto_actualPrimeBoxMass (j.removeNth a) (j.removeNth b)
      (fun i => ha (j.succAbove i)) (fun i => hab (j.succAbove i))).eventually
      (gt_mem_nhds htailLimit)
  have hzero :=
    (tendsto_envelope_zero K (a j) (b j) (ha j) (hab j)
      (fun _ : ℕ => (0 : ℝ)) tendsto_const_nhds).eventually
      (gt_mem_nhds (show (0 : ℝ) < eta / (4 * C) by positivity))
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ a j) atTop atTop :=
    (tendsto_rpow_atTop (ha j)).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧ 3 ≤ (N : ℝ) ^ a j ∧
        actualPrimeBoxMass N (j.removeNth a) (j.removeNth b) < C ∧
          envelope K (a j) (b j) 0 N < eta / (4 * C) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ),
      hp.eventually (eventually_ge_atTop (3 : ℝ)), htail, hzero]
      with N hN hA ht hz
    exact ⟨hN, hA, ht, hz⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
  refine ⟨delta, hdelta, max 2 M, le_max_left _ _, ?_⟩
  intro N hN center
  obtain ⟨hN2, hA, htail, hzero⟩ := hM N ((le_max_right _ _).trans hN)
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  have hb : 0 < b j := (ha j).trans (hab j)
  have hden : 0 < (N : ℝ) ^ a j - 1 := by linarith
  have hwidth : 0 < delta / |v j| := div_pos hdelta (abs_pos.mpr hv)
  have haj : 0 < a j := ha j
  have hE0 : 0 ≤ envelope K (a j) (b j) (delta / |v j|) N := by
    unfold envelope
    positivity
  have hmain : 2 * (delta / |v j|) / a j = eta / (4 * C) := by
    dsimp [delta]
    field_simp [(abs_pos.mpr hv).ne', (ha j).ne', hC.ne']
    <;> ring
  have hsplit : envelope K (a j) (b j) (delta / |v j|) N =
      eta / (4 * C) + envelope K (a j) (b j) 0 N := by
    unfold envelope
    rw [hmain]
    ring
  have htwice : eta / (4 * C) + eta / (4 * C) = eta / (2 * C) := by
    field_simp [hC.ne']
    <;> ring
  have hsmall : envelope K (a j) (b j) (delta / |v j|) N < eta / (2 * C) := by
    rw [hsplit, ← htwice]
    exact add_lt_add_left hzero _
  have hpaid : envelope K (a j) (b j) (delta / |v j|) N * C < eta := by
    have h := (lt_div_iff₀ (show (0 : ℝ) < 2 * C by positivity)).mp hsmall
    nlinarith
  have hbound := affineSlabMass_le_envelope K hK0 hinterval N (by omega)
    a b v j hv (ha j) (hab j) center delta hdelta.le hA
  exact hbound.trans_lt
    ((mul_le_mul_of_nonneg_left htail.le hE0).trans_lt hpaid)

end
end ImbalancedChen.P3OriginalU5FixedWidthSlabReserve
