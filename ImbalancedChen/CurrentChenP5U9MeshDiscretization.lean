import ImbalancedChen.CurrentChenP5U9UniformTaylorTail

/-!
# Mesh error for the literal original ninth integral

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The genuine logDensity is antitone on the entire original interval.
Its equally spaced left/right sums have the exact telescoping gap
((b-a)/m)*(logDensity a-logDensity b).

For the actual directed rational sums a stronger algebraic decomposition
pays the uniform Taylor error only once: compare the upper sum first to
the lower-logarithm LEFT sum, then telescope the latter against the
lower-logarithm RIGHT sum. This proves the fully explicit enclosure width
  (189/250)/m + (672/125)*(47/106)^(2*n+1).
The genuine integral lies inside this enclosure by the existing proved
suppliers. No original endpoint Boolean is evaluated or asserted true.
-/

namespace ImbalancedChen.P5U9MeshDiscretization

noncomputable section

open Set
open scoped BigOperators
open P2U9DirectedRationalCover P2ContinuousSieveRational
open P5U9DirectedLowerCertificate P5U9UniformTaylorTail

/-- Both factors have the required orientation on the full original
closed interval, including its arithmetic half-open boundary owners. -/
theorem antitoneOn_logDensity :
    AntitoneOn logDensity (Icc (a : ℝ) (b : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by norm_num [a, b] at hx; linarith only [hx.1]
  have hy0 : 0 < y := hx0.trans_le hxy
  have hy1 : y < 1 := by norm_num [a, b] at hy; linarith only [hy.2]
  have hx1 : x < 1 := hxy.trans_lt hy1
  have hdx : 0 < x * (1 - x) := mul_pos hx0 (sub_pos.mpr hx1)
  have hdy : 0 < y * (1 - y) := mul_pos hy0 (sub_pos.mpr hy1)
  have hargy : 1 ≤ (1 - y - (d : ℝ)) / (d : ℝ) := by
    apply (le_div_iff₀ (by norm_num [d] : (0 : ℝ) < (d : ℝ))).2
    norm_num [a, b, d] at hy ⊢
    linarith only [hy.2]
  have hratio : (1 - y - (d : ℝ)) / (d : ℝ) ≤
      (1 - x - (d : ℝ)) / (d : ℝ) :=
    div_le_div_of_nonneg_right (by linarith only [hxy]) (by norm_num [d])
  have hlog := Real.log_le_log (by linarith only [hargy] :
    0 < (1 - y - (d : ℝ)) / (d : ℝ)) hratio
  have hlog0 := Real.log_nonneg hargy
  have hden : x * (1 - x) ≤ y * (1 - y) := by
    have hfactor : 0 ≤ 1 - y - x := by
      norm_num [a, b] at hy
      linarith only [hy.2, hxy]
    have hprod := mul_nonneg (sub_nonneg.mpr hxy) hfactor
    nlinarith only [hprod]
  calc
    logDensity y ≤ Real.log ((1 - y - (d : ℝ)) / (d : ℝ)) / (x * (1 - x)) :=
      div_le_div_of_nonneg_left hlog0 hdx hden
    _ ≤ logDensity x := div_le_div_of_nonneg_right hlog hdx.le

private theorem sum_adjacent_sub {A : Type*} [AddCommGroup A] (f : ℕ → A) (m : ℕ) :
    (∑ k ∈ Finset.range m, (f k - f (k + 1))) = f 0 - f m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    abel

/-- The actual rational mesh has exactly equal widths. -/
theorem mesh_step (m k : ℕ) :
    mesh m (k + 1) - mesh m k = (b - a) / (m : ℚ) := by
  simp only [mesh, Nat.cast_add, Nat.cast_one]
  ring

def trueLeftSum (m : ℕ) : ℝ :=
  (((b - a) / (m : ℚ) : ℚ) : ℝ) *
    ∑ k ∈ Finset.range m, logDensity (mesh m k : ℝ)

def trueRightSum (m : ℕ) : ℝ :=
  (((b - a) / (m : ℚ) : ℚ) : ℝ) *
    ∑ k ∈ Finset.range m, logDensity (mesh m (k + 1) : ℝ)

/-- Exact full-density mesh error; no pointwise derivative bound or
numerical integration is needed. -/
theorem true_mesh_gap_exact (m : ℕ) (hm : 0 < m) :
    trueLeftSum m - trueRightSum m =
      (((b - a) / (m : ℚ) : ℚ) : ℝ) *
        (logDensity (a : ℝ) - logDensity (b : ℝ)) := by
  unfold trueLeftSum trueRightSum
  rw [← mul_sub, ← Finset.sum_sub_distrib, sum_adjacent_sub,
    mesh_zero, mesh_last m hm]

theorem true_mesh_gap_nonneg (m : ℕ) (hm : 0 < m) :
    0 ≤ trueLeftSum m - trueRightSum m := by
  rw [true_mesh_gap_exact m hm]
  have hab : (a : ℝ) ≤ (b : ℝ) := by norm_num [a, b]
  have hanti := antitoneOn_logDensity ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  apply mul_nonneg
  · exact_mod_cast (div_nonneg (by norm_num [a, b] : (0 : ℚ) ≤ b - a)
      (Nat.cast_nonneg m : (0 : ℚ) ≤ m))
  · exact sub_nonneg.mpr hanti

/-- The directed lower logarithm is nonnegative at every actual node. -/
theorem cellLower_nonneg (n : ℕ) (l : ℚ) (hl : a ≤ l) (hu : l ≤ b) :
    0 ≤ cellLower n l := by
  have hz := (nodeRatio_bounds l hl hu).1
  have hlog : 0 ≤ logLower n (logQuery l) := by
    unfold logLower
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro k hk
    apply div_nonneg
    · change 0 ≤ nodeRatio l ^ (2 * k + 1)
      exact pow_nonneg hz _
    · positivity
  exact div_nonneg hlog (le_trans (by norm_num : (0 : ℚ) ≤ 1 / 8)
    (node_denominator_ge_one_eighth l hl hu))

/-- A fixed one-term rational upper node bounds all lower Taylor orders
at the left endpoint. This is a proof expression, not an executed check. -/
theorem cellLower_left_le_nine (n : ℕ) : cellLower n a ≤ 9 := by
  have hlo := cellLower_le_logDensity n a le_rfl le_rfl (by norm_num [a, b])
  have hup := logDensity_le_cellUpper 1 a le_rfl le_rfl (by norm_num [a, b])
  have hrat : cellUpper 1 a ≤ 9 := by
    norm_num [cellUpper, logUpper, logLower, logQuery, a, d, Finset.sum_range_succ]
  have hreal : (cellUpper 1 a : ℝ) ≤ 9 := by exact_mod_cast hrat
  have h := hlo.trans (hup.trans hreal)
  exact_mod_cast h

/-- Exact telescoping for the SAME lower logarithm approximation at both
sides of every cell. Thus no second uniform Taylor budget is necessary. -/
theorem lowerLog_mesh_gap_exact (n m : ℕ) (hm : 0 < m) :
    rationalLeftLowerLog n m - rationalLower n m =
      ((b - a) / (m : ℚ)) * (cellLower n a - cellLower n b) := by
  have hleft : rationalLeftLowerLog n m =
      ((b - a) / (m : ℚ)) * ∑ k ∈ Finset.range m, cellLower n (mesh m k) := by
    simp only [rationalLeftLowerLog, mesh_step, Finset.mul_sum]
  have hright : rationalLower n m =
      ((b - a) / (m : ℚ)) * ∑ k ∈ Finset.range m, cellLower n (mesh m (k + 1)) := by
    simp only [rationalLower, mesh_step, Finset.mul_sum]
  rw [hleft, hright, ← mul_sub, ← Finset.sum_sub_distrib, sum_adjacent_sub,
    mesh_zero, mesh_last m hm]

def enclosureRate (n m : ℕ) : ℚ :=
  (189 / 250) / (m : ℚ) + (672 / 125) * geometricTail n

/-- A fully explicit rational enclosure width for the genuine original J.
Both error sources are now paid: mesh discretization and logarithm tail. -/
theorem rational_enclosure_width (n m : ℕ) (hm : 0 < m) :
    0 ≤ P2U9DirectedRationalCover.rationalUpper n m - rationalLower n m ∧
      P2U9DirectedRationalCover.rationalUpper n m - rationalLower n m ≤
        enclosureRate n m := by
  have horderR : (rationalLower n m : ℝ) ≤
      (P2U9DirectedRationalCover.rationalUpper n m : ℝ) :=
    (rationalLower_le_actual_integral n m hm).trans
      (actual_integral_le_rationalUpper n m hm)
  have horder : rationalLower n m ≤ P2U9DirectedRationalCover.rationalUpper n m := by
    exact_mod_cast horderR
  have htail := (rational_mesh_logarithm_tail n m hm).2
  have hgap := lowerLog_mesh_gap_exact n m hm
  have hnonneg := cellLower_nonneg n b (by norm_num [a, b]) le_rfl
  have hleft := cellLower_left_le_nine n
  have hend : cellLower n a - cellLower n b ≤ 9 := by linarith only [hnonneg, hleft]
  have hwidth : 0 ≤ (b - a) / (m : ℚ) :=
    div_nonneg (by norm_num [a, b]) (Nat.cast_nonneg m)
  have hmesh := mul_le_mul_of_nonneg_left hend hwidth
  have hscale : ((b - a) / (m : ℚ)) * 9 = (189 / 250 : ℚ) / (m : ℚ) := by
    norm_num [a, b]
    <;> ring
  rw [hscale] at hmesh
  constructor
  · exact sub_nonneg.mpr horder
  · dsimp only [enclosureRate]
    linarith only [htail, hgap, hmesh]

/-- The explicit rate bounds BOTH signed errors around the literal J,
using its actual existing upper and lower integral suppliers. -/
theorem actual_integral_errors_le_rate (n m : ℕ) (hm : 0 < m) :
    |currentChenUpsilon9HarmonicIntegral - (rationalLower n m : ℝ)| ≤
        (enclosureRate n m : ℝ) ∧
      |(P2U9DirectedRationalCover.rationalUpper n m : ℝ) -
        currentChenUpsilon9HarmonicIntegral| ≤ (enclosureRate n m : ℝ) := by
  have hlo := rationalLower_le_actual_integral n m hm
  have hup := actual_integral_le_rationalUpper n m hm
  have hwidth : (P2U9DirectedRationalCover.rationalUpper n m : ℝ) -
      (rationalLower n m : ℝ) ≤ (enclosureRate n m : ℝ) := by
    exact_mod_cast (rational_enclosure_width n m hm).2
  rw [abs_of_nonneg (sub_nonneg.mpr hlo), abs_of_nonneg (sub_nonneg.mpr hup)]
  constructor <;> linarith only [hlo, hup, hwidth]

end

end ImbalancedChen.P5U9MeshDiscretization
