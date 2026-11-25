import ImbalancedChen.ActualGridEnvelopes
import ImbalancedChen.PowerErrorBudget
import ImbalancedChen.TotientReciprocalBudget

/-!
# A logarithmic mesh makes the actual geometric boundary negligible

The mesh is the literal `delta(N) = 1 / (log N)^k`, with any fixed natural
`k > 4`. The complete geometric budget retains its sublinear term
`14 * N^(1/(1+b))`, including the integer-rounding losses already proved in
`ActualGridEnvelopes`. Multiplication by the reciprocal-totient budget costs
one additional logarithm. All comparison is with the genuine manuscript
normalization `singularSeries N * N / (log N)^2`.

The final statement is uniform in the real cutoff `0 <= T <= N` and every
natural modulus cap `D <= N`. This is only the geometric boundary cost;
no prime-rectangle distribution estimate is asserted or assumed.
-/

namespace ImbalancedChen

open Filter Topology
open scoped BigOperators

noncomputable section

/-- The actual mesh size; its exceptional totalized values at zero and one
are irrelevant to the eventual statements. -/
def boundaryLogMesh (k N : ℕ) : ℝ :=
  1 / (Real.log (N : ℝ)) ^ k

/-- Reciprocal positive natural powers of the natural logarithm decay. -/
theorem tendsto_boundaryLogMesh {k : ℕ} (hk : 0 < k) :
    Tendsto (boundaryLogMesh k) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact ((tendsto_pow_atTop (α := ℝ) (n := k) hk.ne').comp hlog).const_div_atTop 1

/-- The logarithm is at least one on all sufficiently large natural inputs. -/
theorem eventually_one_le_nat_log :
    ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop 1)

/-- A logarithmic mesh is positive and at most one on large inputs. -/
theorem eventually_boundaryLogMesh_mem (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, 0 < boundaryLogMesh k N ∧ boundaryLogMesh k N ≤ 1 := by
  filter_upwards [eventually_one_le_nat_log] with N hlog
  have hp : 0 < (Real.log (N : ℝ)) ^ k := pow_pos (by linarith) k
  exact ⟨div_pos zero_lt_one hp, (div_le_one hp).mpr (one_le_pow₀ hlog)⟩

/-- After paying two logarithms, the mesh part of the boundary budget is
still arbitrarily small in the actual singular normalization when `k > 4`. -/
theorem eventually_boundaryLogMesh_main_le_singularNormalization
    (c : ℝ) {k : ℕ} (hk : 4 < k) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        c * boundaryLogMesh k N * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 ≤
          epsilon * singularNormalization N := by
  intro epsilon hepsilon
  have hdecay : Tendsto (fun N : ℕ => c * boundaryLogMesh (k - 4) N)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_boundaryLogMesh (show 0 < k - 4 by omega)).const_mul c
  have hsmall : ∀ᶠ N : ℕ in atTop,
      c * boundaryLogMesh (k - 4) N < epsilon * twinPrimeConstant :=
    hdecay.eventually (gt_mem_nhds (mul_pos hepsilon twinPrimeConstant_pos))
  filter_upwards [hsmall, eventually_one_le_nat_log] with N hsmallN hlogN
  have hlog : Real.log (N : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hbase : 0 ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ 2 :=
    div_nonneg (Nat.cast_nonneg N) (sq_nonneg _)
  calc
    c * boundaryLogMesh k N * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 =
        (c * boundaryLogMesh (k - 4) N) *
          ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
      unfold boundaryLogMesh
      conv_lhs => rw [show k = (k - 4) + 4 by omega, pow_add]
      field_simp [hlog] <;> ring
    _ ≤ (epsilon * twinPrimeConstant) *
        ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_right hsmallN.le hbase
    _ = epsilon *
        (twinPrimeConstant * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by ring
    _ ≤ epsilon * singularNormalization N :=
      mul_le_mul_of_nonneg_left (singularNormalization_lower N) hepsilon.le

/-- The full explicit geometric budget, including the sublinear term and
the logarithmic reciprocal-totient factor at its largest permitted cap. -/
def boundaryLogMeshBudget (b : ℝ) (k N : ℕ) : ℝ :=
  (12 * boundaryLogMesh k N * N * Real.log (3 * N) +
    216 * boundaryLogMesh k N * N + 14 * (N : ℝ) ^ (1 / (1 + b))) *
      (4 * (1 + Real.log (N : ℝ)))


/-- A simple power-log majorant for the complete explicit budget. Its two
terms have respectively reciprocal-logarithmic and sublinear-power decay. -/
theorem boundaryLogMeshBudget_le_powerLog (b : ℝ) (k N : ℕ)
    (hN : 1 ≤ (N : ℝ)) (hlog : 1 ≤ Real.log (N : ℝ)) :
    boundaryLogMeshBudget b k N ≤
      2016 * boundaryLogMesh k N * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 +
        112 * (N : ℝ) ^ (1 / (1 + b)) * Real.log (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have hmesh : 0 ≤ boundaryLogMesh k N :=
    div_nonneg zero_le_one (pow_nonneg hlog0 k)
  have hlog3N : Real.log (3 * (N : ℝ)) ≤ 3 * Real.log (N : ℝ) := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hNpos.ne']
    have hthree := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hfirst := mul_le_mul_of_nonneg_left hlog3N
    (show 0 ≤ 12 * boundaryLogMesh k N * (N : ℝ) by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ 216 * boundaryLogMesh k N * (N : ℝ) by positivity)
  have hupper :
      12 * boundaryLogMesh k N * N * Real.log (3 * N) +
        216 * boundaryLogMesh k N * N + 14 * (N : ℝ) ^ (1 / (1 + b)) ≤
      252 * boundaryLogMesh k N * N * Real.log (N : ℝ) +
        14 * (N : ℝ) ^ (1 / (1 + b)) := by
    nlinarith only [hfirst, hsecond]
  have hupper0 : 0 ≤
      252 * boundaryLogMesh k N * N * Real.log (N : ℝ) +
        14 * (N : ℝ) ^ (1 / (1 + b)) := by positivity
  calc
    boundaryLogMeshBudget b k N ≤
        (252 * boundaryLogMesh k N * N * Real.log (N : ℝ) +
          14 * (N : ℝ) ^ (1 / (1 + b))) * (8 * Real.log (N : ℝ)) :=
      mul_le_mul hupper (by linarith) (by positivity) hupper0
    _ = _ := by ring

/-- The entire explicit geometric budget is negligible in the genuine
normalization. The retained sublinear exponent is strictly below one as
soon as the fixed manuscript exponent is positive. -/
theorem eventually_boundaryLogMeshBudget_le_singularNormalization
    {b : ℝ} (hb : 0 < b) {k : ℕ} (hk : 4 < k) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        boundaryLogMeshBudget b k N ≤ epsilon * singularNormalization N := by
  intro epsilon hepsilon
  have hgamma : 1 / (1 + b) < 1 :=
    (div_lt_one (by linarith : 0 < 1 + b)).mpr (by linarith)
  filter_upwards
    [eventually_boundaryLogMesh_main_le_singularNormalization 2016 hk
      (epsilon / 2) (half_pos hepsilon),
      eventually_powerLog_le_singularNormalization 112 (1 / (1 + b)) 1 hgamma
        (epsilon / 2) (half_pos hepsilon),
      eventually_one_le_nat_log, eventually_ge_atTop (1 : ℕ)]
    with N hmain hpower hlog hN
  have hbudget := boundaryLogMeshBudget_le_powerLog b k N (by exact_mod_cast hN) hlog
  simp only [pow_one] at hpower
  linarith

/-- The literal finite envelope mass times the explicit reciprocal-totient
majorant is bounded by the same complete geometric budget, uniformly in
both the real cutoff and the modulus cap. -/
theorem actualGrid_logMesh_boundary_cost_le_budget
    {num den N k D : ℕ} {T : ℝ} (hden : 0 < den)
    (hmesh : 0 < boundaryLogMesh k N) (hmesh1 : boundaryLogMesh k N ≤ 1)
    (hT : 0 ≤ T) (hTN : T ≤ (N : ℝ)) (hN : 1 ≤ (N : ℝ))
    (hb1 : (num : ℝ) / (den : ℝ) ≤ 1) (hD : D ≤ N) :
    finiteSourceMass
      (actualGridProductCarrier num den N T (1 + boundaryLogMesh k N))
      (fun m => actualGridUpperWeight num den N T (1 + boundaryLogMesh k N) m -
        actualGridLowerWeight num den N T (1 + boundaryLogMesh k N) m) *
      (4 * (1 + Real.log (max 1 (D : ℝ)))) ≤
        boundaryLogMeshBudget ((num : ℝ) / (den : ℝ)) k N := by
  have hmass := actualGrid_boundary_mass_le_explicit hden hmesh hmesh1 hT hTN hN hb1
  have hlogD : Real.log (max 1 (D : ℝ)) ≤ Real.log (N : ℝ) := by
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    exact max_le hN (by exact_mod_cast hD)
  have hlogD0 : 0 ≤ Real.log (max 1 (D : ℝ)) :=
    Real.log_nonneg (le_max_left _ _)
  have hlog3N0 : 0 ≤ Real.log (3 * (N : ℝ)) :=
    Real.log_nonneg (by nlinarith)
  have hupper0 : 0 ≤
      12 * boundaryLogMesh k N * N * Real.log (3 * N) +
        216 * boundaryLogMesh k N * N +
          14 * (N : ℝ) ^ (1 / (1 + (num : ℝ) / (den : ℝ))) := by positivity
  exact mul_le_mul hmass (by linarith) (by positivity) hupper0

/-- Actual geometric error is negligible uniformly for every `T` in `[0,N]`
and every natural `D <= N`. The only exponent premises are the literal
rational manuscript range `0 < num / den < 1`; there is no mass premise. -/
theorem eventually_actualGrid_logMesh_boundary_cost_le_singularNormalization
    {num den k : ℕ} (hden : 0 < den)
    (hb : 0 < (num : ℝ) / (den : ℝ))
    (hb1 : (num : ℝ) / (den : ℝ) < 1) (hk : 4 < k) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ T : ℝ, ∀ D : ℕ,
        0 ≤ T → T ≤ (N : ℝ) → D ≤ N →
        finiteSourceMass
          (actualGridProductCarrier num den N T (1 + boundaryLogMesh k N))
          (fun m => actualGridUpperWeight num den N T (1 + boundaryLogMesh k N) m -
            actualGridLowerWeight num den N T (1 + boundaryLogMesh k N) m) *
          (4 * (1 + Real.log (max 1 (D : ℝ)))) ≤
            epsilon * singularNormalization N := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_boundaryLogMeshBudget_le_singularNormalization hb hk epsilon hepsilon,
      eventually_boundaryLogMesh_mem k, eventually_ge_atTop (1 : ℕ)]
    with N hbudget hmesh hN
  intro T D hT hTN hD
  exact (actualGrid_logMesh_boundary_cost_le_budget hden hmesh.1 hmesh.2
    hT hTN (by exact_mod_cast hN) hb1.le hD).trans hbudget

/-- In particular, paying the genuine finite reciprocal-totient sum for the
actual envelope difference has arbitrarily small normalized cost. -/
theorem eventually_actualGrid_logMesh_boundary_totient_cost_le_singularNormalization
    {num den k : ℕ} (hden : 0 < den)
    (hb : 0 < (num : ℝ) / (den : ℝ))
    (hb1 : (num : ℝ) / (den : ℝ) < 1) (hk : 4 < k) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ T : ℝ, ∀ D : ℕ,
        0 ≤ T → T ≤ (N : ℝ) → D ≤ N →
        finiteSourceMass
          (actualGridProductCarrier num den N T (1 + boundaryLogMesh k N))
          (fun m => actualGridUpperWeight num den N T (1 + boundaryLogMesh k N) m -
            actualGridLowerWeight num den N T (1 + boundaryLogMesh k N) m) *
          (∑ d ∈ Finset.Icc 1 D, 1 / (Nat.totient d : ℝ)) ≤
            epsilon * singularNormalization N := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_actualGrid_logMesh_boundary_cost_le_singularNormalization
      hden hb hb1 hk epsilon hepsilon] with N hN
  intro T D hT hTN hD
  have hmass0 : 0 ≤ finiteSourceMass
      (actualGridProductCarrier num den N T (1 + boundaryLogMesh k N))
      (fun m => actualGridUpperWeight num den N T (1 + boundaryLogMesh k N) m -
        actualGridLowerWeight num den N T (1 + boundaryLogMesh k N) m) := by
    rw [actualGrid_boundary_mass_eq_card]
    positivity
  exact (mul_le_mul_of_nonneg_left (sum_reciprocal_totient_le_log D) hmass0).trans
    (hN T D hT hTN hD)

end

end ImbalancedChen
