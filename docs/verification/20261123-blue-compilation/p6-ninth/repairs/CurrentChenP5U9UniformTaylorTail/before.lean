import ImbalancedChen.CurrentChenP5U9DirectedLowerCertificate

/-!
# Uniform logarithm truncation error on the literal original U9 interval

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

This isolates the power-series error from the mesh error. The exact
logarithm variable is at most 47/106 on the entire original interval.
Consequently every rational density node has Taylor uncertainty at most
32*(47/106)^(2*n+1), and replacing all upper logarithms in ANY complete
mesh by lower logarithms loses at most (672/125)*(47/106)^(2*n+1).

The latter lower-logarithm LEFT sum is not claimed to bound J below:
the separate right-endpoint lower certificate does that. In particular
no original endpoint check, mesh-error estimate, PP supplier, or mean is
smuggled into this logarithm truncation result.
-/

namespace ImbalancedChen.P5U9UniformTaylorTail

noncomputable section

open scoped BigOperators
open P2U9DirectedRationalCover P2ContinuousSieveRational
open P5U9DirectedLowerCertificate

def nodeRatio (l : ℚ) : ℚ := (logQuery l - 2) / logQuery l

def geometricTail (n : ℕ) : ℚ := (47 / 106) ^ (2 * n + 1)

theorem nodeRatio_bounds (l : ℚ) (hl : a ≤ l) (hu : l ≤ b) :
    0 ≤ nodeRatio l ∧ nodeRatio l ≤ 47 / 106 := by
  have hqlo : 2 ≤ logQuery l := by
    norm_num [logQuery, d, a, b] at hl hu ⊢
    linarith
  have hqhi : logQuery l ≤ 212 / 59 := by
    norm_num [logQuery, d, a, b] at hl hu ⊢
    linarith
  have hqp : 0 < logQuery l := by linarith only [hqlo]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hqlo) hqp.le
  · apply (div_le_iff₀ hqp).2
    nlinarith only [hqhi]

theorem node_denominator_ge_one_eighth (l : ℚ) (hl : a ≤ l) (hu : l ≤ b) :
    (1 / 8 : ℚ) ≤ l * (1 - l) := by
  have hfactor : 0 ≤ 1 - l - a := by norm_num [a, b] at hl hu ⊢; linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hl) hfactor
  norm_num [a, b] at hl hu hprod
  nlinarith only [hprod]

/-- Exact geometric remainder, bounded uniformly without evaluating any
Taylor polynomial or choosing an integration mesh. -/
theorem node_logarithm_tail_bounds (n : ℕ) (l : ℚ) (hl : a ≤ l) (hu : l ≤ b) :
    0 ≤ logUpper n (logQuery l) - logLower n (logQuery l) ∧
      logUpper n (logQuery l) - logLower n (logQuery l) ≤ 4 * geometricTail n := by
  obtain ⟨hz0, hzb⟩ := nodeRatio_bounds l hl hu
  have hzhalf : nodeRatio l ≤ 1 / 2 := hzb.trans (by norm_num)
  have hzsq : nodeRatio l ^ 2 ≤ 1 / 4 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hzhalf) (add_nonneg hz0 (by norm_num : (0 : ℚ) ≤ 1 / 2))
    nlinarith only [hprod]
  have hden : (1 / 2 : ℚ) ≤ 1 - nodeRatio l ^ 2 := by linarith only [hzsq]
  have hdenp : 0 < 1 - nodeRatio l ^ 2 := lt_of_lt_of_le (by norm_num) hden
  have hp0 : 0 ≤ nodeRatio l ^ (2 * n + 1) := pow_nonneg hz0 _
  have hpower : nodeRatio l ^ (2 * n + 1) ≤ geometricTail n := by
    dsimp only [geometricTail]
    gcongr <;> assumption
  have hexact : logUpper n (logQuery l) - logLower n (logQuery l) =
      2 * nodeRatio l ^ (2 * n + 1) / (1 - nodeRatio l ^ 2) := by
    simp only [logUpper, nodeRatio, add_sub_cancel_left]
  rw [hexact]
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) hp0) hdenp.le
  · calc
      _ ≤ 4 * nodeRatio l ^ (2 * n + 1) := by
        apply (div_le_iff₀ hdenp).2
        have hprod := mul_nonneg hp0 (sub_nonneg.mpr hden)
        nlinarith only [hprod]
      _ ≤ 4 * geometricTail n := mul_le_mul_of_nonneg_left hpower (by norm_num)

/-- The positive original density denominator pays at most a factor eight.
This bound concerns both directed logarithm approximations at one node. -/
theorem node_density_tail_bounds (n : ℕ) (l : ℚ) (hl : a ≤ l) (hu : l ≤ b) :
    0 ≤ cellUpper n l - cellLower n l ∧
      cellUpper n l - cellLower n l ≤ 32 * geometricTail n := by
  obtain ⟨ht0, ht⟩ := node_logarithm_tail_bounds n l hl hu
  have hd := node_denominator_ge_one_eighth l hl hu
  have hdp : 0 < l * (1 - l) := lt_of_lt_of_le (by norm_num) hd
  have hG : 0 ≤ geometricTail n := pow_nonneg (by norm_num) _
  have hexact : cellUpper n l - cellLower n l =
      (logUpper n (logQuery l) - logLower n (logQuery l)) / (l * (1 - l)) := by
    unfold cellUpper cellLower
    ring
  rw [hexact]
  constructor
  · exact div_nonneg ht0 hdp.le
  · apply (div_le_iff₀ hdp).2
    have hprod := mul_nonneg hG (sub_nonneg.mpr hd)
    nlinarith only [ht, hprod]

/-- The exact ORIGINAL logDensity at a rational node has the signed lower
error asserted here, not merely an enclosure of an auxiliary function. -/
theorem literal_node_lower_error (n : ℕ) (l : ℚ) (hl : a ≤ l) (hu : l ≤ b) :
    0 ≤ logDensity (l : ℝ) - (cellLower n l : ℝ) ∧
      logDensity (l : ℝ) - (cellLower n l : ℝ) ≤
        ((32 * geometricTail n : ℚ) : ℝ) := by
  have hlR : (a : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have huR : (l : ℝ) ≤ (b : ℝ) := by exact_mod_cast hu
  have hlo := cellLower_le_logDensity n l hlR le_rfl hu
  have hup := logDensity_le_cellUpper n l hl le_rfl huR
  have htail : (cellUpper n l : ℝ) - (cellLower n l : ℝ) ≤
      ((32 * geometricTail n : ℚ) : ℝ) := by
    exact_mod_cast (node_density_tail_bounds n l hl hu).2
  exact ⟨sub_nonneg.mpr hlo, (sub_le_sub_right hup _).trans htail⟩

/-- Same left mesh as rationalUpper, replacing ONLY its logarithm upper
approximation. This has no asserted lower-integral orientation. -/
def rationalLeftLowerLog (n m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range m,
    (mesh m (k + 1) - mesh m k) * cellLower n (mesh m k)

private theorem mesh_length_sum (m k : ℕ) :
    (∑ i ∈ Finset.range k, (mesh m (i + 1) - mesh m i)) = mesh m k - mesh m 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Any full original partition inherits the same uniform Taylor budget.
The mesh may be chosen independently of the logarithm precision. -/
theorem rational_mesh_logarithm_tail (n m : ℕ) (hm : 0 < m) :
    0 ≤ P2U9DirectedRationalCover.rationalUpper n m - rationalLeftLowerLog n m ∧
      P2U9DirectedRationalCover.rationalUpper n m - rationalLeftLowerLog n m ≤
        (672 / 125 : ℚ) * geometricTail n := by
  have hcell (k : ℕ) (hk : k ∈ Finset.range m) :
      0 ≤ (mesh m (k + 1) - mesh m k) * (cellUpper n (mesh m k) - cellLower n (mesh m k)) ∧
        (mesh m (k + 1) - mesh m k) * (cellUpper n (mesh m k) - cellLower n (mesh m k)) ≤
          (mesh m (k + 1) - mesh m k) * (32 * geometricTail n) := by
    have hk' := Finset.mem_range.mp hk
    have hbounds := mesh_bounds m hm k hk'.le
    have hwidth := sub_nonneg.mpr (mesh_monotone m hm (Nat.le_succ k))
    have htail := node_density_tail_bounds n (mesh m k) hbounds.1 hbounds.2
    exact ⟨mul_nonneg hwidth htail.1, mul_le_mul_of_nonneg_left htail.2 hwidth⟩
  have hexact : P2U9DirectedRationalCover.rationalUpper n m - rationalLeftLowerLog n m =
      ∑ k ∈ Finset.range m,
        (mesh m (k + 1) - mesh m k) * (cellUpper n (mesh m k) - cellLower n (mesh m k)) := by
    simp only [P2U9DirectedRationalCover.rationalUpper, rationalLeftLowerLog,
      Finset.sum_sub_distrib, mul_sub]
  rw [hexact]
  constructor
  · exact Finset.sum_nonneg (fun k hk => (hcell k hk).1)
  · calc
      _ ≤ ∑ k ∈ Finset.range m,
          (mesh m (k + 1) - mesh m k) * (32 * geometricTail n) :=
        Finset.sum_le_sum (fun k hk => (hcell k hk).2)
      _ = (672 / 125 : ℚ) * geometricTail n := by
        rw [← Finset.sum_mul, mesh_length_sum m m, mesh_zero, mesh_last m hm]
        norm_num [a, b]
        <;> ring

end

end ImbalancedChen.P5U9UniformTaylorTail
