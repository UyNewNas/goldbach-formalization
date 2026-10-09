import ImbalancedChen.CurvedDiscrepancyReduction
import ImbalancedChen.LogMeshGridCount

/-!
# Arbitrary logarithmic accuracy for the actual geometric boundary error

For every fixed natural accuracy `A`, any fixed mesh exponent `k > A + 2`
gives boundary cost at most `epsilon * N / (log N)^A` eventually. In
particular, `k = A + 3` can be chosen before `epsilon`, the eventual
threshold, the cutoff, the modulus cap, or the selected modulus family.

This follows from the proved, literal boundary majorant
`2016 * delta * N * (log N)^2 + 112 * N^(1/(1+b)) * log N`.
Its second term retains the lattice-rounding losses. The exponent `b` is
fixed in its original range `0 < b < 1`; the threshold may depend on it.
No singular-series upper bound or analytic distribution input is assumed.

The small boundary quantity is the actual envelope-gap mass times the
reciprocal-totient sum. The resulting curved-discrepancy reduction retains
the sum of absolute discrepancies of all selected full prime rectangles.
That rectangle sum is not claimed small here.
-/

namespace ImbalancedChen

open Filter Topology
open scoped BigOperators

noncomputable section

/-- A fixed sublinear power times any fixed logarithm power has arbitrary
unweighted logarithmic accuracy. This uses the proved power-log limit,
without passing through the singular-series normalization. -/
theorem eventually_powerLog_le_logAccuracy
    (c theta : ℝ) (j A : ℕ) (htheta : theta < 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        c * (N : ℝ) ^ theta * (Real.log (N : ℝ)) ^ j ≤
          epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  intro epsilon hepsilon
  have hdecay : Tendsto (fun N : ℕ =>
      c * ((Real.log (N : ℝ)) ^ (j + A) / (N : ℝ) ^ (1 - theta)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_nat_log_pow_div_rpow (j + A) (sub_pos.mpr htheta)).const_mul c
  have hsmall : ∀ᶠ N : ℕ in atTop,
      c * ((Real.log (N : ℝ)) ^ (j + A) / (N : ℝ) ^ (1 - theta)) < epsilon :=
    hdecay.eventually (gt_mem_nhds hepsilon)
  filter_upwards [hsmall, eventually_one_le_nat_log, eventually_ge_atTop (1 : ℕ)]
    with N hsmallN hlogN hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hlog : Real.log (N : ℝ) ≠ 0 := hlogpos.ne'
  have hpow : (N : ℝ) ^ theta ≠ 0 := (Real.rpow_pos_of_pos hNpos theta).ne'
  have hbase : 0 ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ A :=
    div_nonneg (Nat.cast_nonneg N) (pow_nonneg hlogpos.le A)
  calc
    c * (N : ℝ) ^ theta * (Real.log (N : ℝ)) ^ j =
        (c * ((Real.log (N : ℝ)) ^ (j + A) / (N : ℝ) ^ (1 - theta))) *
          ((N : ℝ) / (Real.log (N : ℝ)) ^ A) := by
      rw [Real.rpow_sub hNpos, Real.rpow_one, pow_add]
      field_simp [hNpos.ne', hlog, hpow] <;> ring
    _ ≤ epsilon * ((N : ℝ) / (Real.log (N : ℝ)) ^ A) :=
      mul_le_mul_of_nonneg_right hsmallN.le hbase
    _ = epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by ring

/-- Paying the two logarithms in the explicit mesh term leaves decay as
soon as the mesh exponent exceeds the requested accuracy by two. -/
theorem eventually_boundaryLogMesh_main_le_logAccuracy
    (c : ℝ) (A : ℕ) {k : ℕ} (hk : A + 2 < k) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        c * boundaryLogMesh k N * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 ≤
          epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  intro epsilon hepsilon
  have hdecay : Tendsto (fun N : ℕ => c * boundaryLogMesh (k - (A + 2)) N)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_boundaryLogMesh (show 0 < k - (A + 2) by omega)).const_mul c
  have hsmall : ∀ᶠ N : ℕ in atTop,
      c * boundaryLogMesh (k - (A + 2)) N < epsilon :=
    hdecay.eventually (gt_mem_nhds hepsilon)
  filter_upwards [hsmall, eventually_one_le_nat_log] with N hsmallN hlogN
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hlog : Real.log (N : ℝ) ≠ 0 := hlogpos.ne'
  have hbase : 0 ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ A :=
    div_nonneg (Nat.cast_nonneg N) (pow_nonneg hlogpos.le A)
  calc
    c * boundaryLogMesh k N * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 =
        (c * boundaryLogMesh (k - (A + 2)) N) *
          ((N : ℝ) / (Real.log (N : ℝ)) ^ A) := by
      unfold boundaryLogMesh
      conv_lhs =>
        rw [show k = (k - (A + 2)) + (A + 2) by omega, pow_add, pow_add]
      field_simp [hlog] <;> ring
    _ ≤ epsilon * ((N : ℝ) / (Real.log (N : ℝ)) ^ A) :=
      mul_le_mul_of_nonneg_right hsmallN.le hbase
    _ = epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by ring

/-- Arbitrary logarithmic accuracy for the complete explicit geometric
budget, including its sublinear lattice-rounding term. -/
theorem eventually_boundaryLogMeshBudget_le_logAccuracy
    {b : ℝ} (hb : 0 < b) (A : ℕ) {k : ℕ} (hk : A + 2 < k) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        boundaryLogMeshBudget b k N ≤
          epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  intro epsilon hepsilon
  have hgamma : 1 / (1 + b) < 1 :=
    (div_lt_one (by linarith : 0 < 1 + b)).mpr (by linarith)
  filter_upwards
    [eventually_boundaryLogMesh_main_le_logAccuracy 2016 A hk
      (epsilon / 2) (half_pos hepsilon),
      eventually_powerLog_le_logAccuracy 112 (1 / (1 + b)) 1 A hgamma
        (epsilon / 2) (half_pos hepsilon),
      eventually_one_le_nat_log, eventually_ge_atTop (1 : ℕ)]
    with N hmain hpower hlog hN
  simp only [pow_one] at hpower
  calc
    boundaryLogMeshBudget b k N ≤
        2016 * boundaryLogMesh k N * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 +
          112 * (N : ℝ) ^ (1 / (1 + b)) * Real.log (N : ℝ) :=
      boundaryLogMeshBudget_le_powerLog b k N (by exact_mod_cast hN) hlog
    _ ≤ (epsilon / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A +
        (epsilon / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A := add_le_add hmain hpower
    _ = epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by ring

/-- The actual envelope-gap mass times the explicit reciprocal-totient
majorant has arbitrary logarithmic accuracy, uniformly in the real
cutoff and the entire allowed modulus cap. -/
theorem eventually_actualGrid_logMesh_boundary_cost_le_logAccuracy
    {num den k : ℕ} (hden : 0 < den)
    (hb : 0 < (num : ℝ) / (den : ℝ))
    (hb1 : (num : ℝ) / (den : ℝ) < 1) (A : ℕ) (hk : A + 2 < k) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ T : ℝ, ∀ D : ℕ,
        0 ≤ T → T ≤ (N : ℝ) → D ≤ N →
        finiteSourceMass
          (actualGridProductCarrier num den N T (1 + boundaryLogMesh k N))
          (fun m => actualGridUpperWeight num den N T (1 + boundaryLogMesh k N) m -
            actualGridLowerWeight num den N T (1 + boundaryLogMesh k N) m) *
          (4 * (1 + Real.log (max 1 (D : ℝ)))) ≤
            epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_boundaryLogMeshBudget_le_logAccuracy hb A hk epsilon hepsilon,
      eventually_boundaryLogMesh_mem k, eventually_ge_atTop (1 : ℕ)]
    with N hbudget hmesh hN
  intro T D hT hTN hD
  exact (actualGrid_logMesh_boundary_cost_le_budget hden hmesh.1 hmesh.2
    hT hTN (by exact_mod_cast hN) hb1.le hD).trans hbudget

/-- The actual summed geometric boundary cost, with the genuine finite
reciprocal-totient sum over any selected positive moduli. The same eventual
threshold works for every cutoff, modulus cap, and subset under that cap. -/
theorem eventually_actualGrid_logMesh_boundary_totient_cost_le_logAccuracy
    {num den k : ℕ} (hden : 0 < den)
    (hb : 0 < (num : ℝ) / (den : ℝ))
    (hb1 : (num : ℝ) / (den : ℝ) < 1) (A : ℕ) (hk : A + 2 < k) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ T : ℝ, ∀ D : ℕ, ∀ S : Finset ℕ,
        0 ≤ T → T ≤ (N : ℝ) → D ≤ N → S ⊆ Finset.Icc 1 D →
        finiteSourceMass
          (actualGridProductCarrier num den N T (1 + boundaryLogMesh k N))
          (fun m => actualGridUpperWeight num den N T (1 + boundaryLogMesh k N) m -
            actualGridLowerWeight num den N T (1 + boundaryLogMesh k N) m) *
          (∑ d ∈ S, 1 / (Nat.totient d : ℝ)) ≤
            epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_actualGrid_logMesh_boundary_cost_le_logAccuracy
      hden hb hb1 A hk epsilon hepsilon] with N hboundary
  intro T D S hT hTN hD hS
  have hmass0 : 0 ≤ finiteSourceMass
      (actualGridProductCarrier num den N T (1 + boundaryLogMesh k N))
      (fun m => actualGridUpperWeight num den N T (1 + boundaryLogMesh k N) m -
        actualGridLowerWeight num den N T (1 + boundaryLogMesh k N) m) := by
    rw [actualGrid_boundary_mass_eq_card]
    exact Nat.cast_nonneg _
  exact (mul_le_mul_of_nonneg_left
    (sum_reciprocal_totient_subset_le_log S D hS) hmass0).trans
      (hboundary T D hT hTN hD)

/-- A single mesh can be chosen first for every requested accuracy. The
witness is exactly `k = A + 3`, independent even of the fixed source
exponent. The grid remains polylogarithmic at that same mesh. -/
theorem exists_logMesh_boundary_arbitrary_accuracy
    {num den : ℕ} (hden : 0 < den)
    (hb : 0 < (num : ℝ) / (den : ℝ))
    (hb1 : (num : ℝ) / (den : ℝ) < 1) (A : ℕ) :
    ∃ k : ℕ, k = A + 3 ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ N : ℕ in atTop, ∀ T : ℝ, ∀ D : ℕ, ∀ S : Finset ℕ,
          0 ≤ T → T ≤ (N : ℝ) → D ≤ N → S ⊆ Finset.Icc 1 D →
          (finiteSourceMass
            (actualGridProductCarrier num den N T (1 + boundaryLogMesh k N))
            (fun m => actualGridUpperWeight num den N T (1 + boundaryLogMesh k N) m -
              actualGridLowerWeight num den N T (1 + boundaryLogMesh k N) m) *
            (∑ d ∈ S, 1 / (Nat.totient d : ℝ)) ≤
              epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A) ∧
          ((actualGridIntersectingIndices num den N T
            (1 + boundaryLogMesh k N)).card : ℝ) ≤
              (2 * (Real.log (N : ℝ)) ^ (k + 1) + 1) ^ 2 := by
  refine ⟨A + 3, rfl, ?_⟩
  intro epsilon hepsilon
  filter_upwards
    [eventually_actualGrid_logMesh_boundary_totient_cost_le_logAccuracy
      hden hb hb1 A (show A + 2 < A + 3 by omega) epsilon hepsilon,
      eventually_actualGrid_logMesh_card_le (A + 3)] with N hboundary hcount
  intro T D S hT hTN hD hS
  exact ⟨hboundary T D S hT hTN hD hS, (hcount num den T).1⟩

/-- Curved discrepancy reduces to the literal rectangle sum with any
fixed requested logarithmic accuracy in its additive geometric error.
The exponent `k` is fixed before all eventual and finite choices. -/
theorem eventually_sum_abs_halfProductPrimitiveDiscrepancy_le_actualGridRectangles_logAccuracy
    {num den k : ℕ} (hden : 0 < den)
    (hb : 0 < (num : ℝ) / (den : ℝ))
    (hb1 : (num : ℝ) / (den : ℝ) < 1) (A : ℕ) (hk : A + 2 < k) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ T : ℝ, ∀ D : ℕ, ∀ S : Finset ℕ,
        0 ≤ T → T ≤ (N : ℝ) → D ≤ N → S ⊆ Finset.Icc 1 D →
        (∑ d ∈ S, |halfProductCongruenceMass num den N T d -
          halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)|) ≤
        (∑ ij ∈ actualGridIntersectingIndices num den N T (1 + boundaryLogMesh k N),
          ∑ d ∈ S, |actualGridRectangleDiscrepancy (1 + boundaryLogMesh k N) ij N d|) +
          epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_actualGrid_logMesh_boundary_totient_cost_le_logAccuracy
      hden hb hb1 A hk epsilon hepsilon, eventually_boundaryLogMesh_mem k]
    with N hboundary hmesh
  intro T D S hT hTN hD hS
  have hκ : 1 < 1 + boundaryLogMesh k N := by linarith [hmesh.1]
  exact (sum_abs_halfProductPrimitiveDiscrepancy_le_actualGridRectangles hden hκ S).trans
    (add_le_add le_rfl (hboundary T D S hT hTN hD hS))

/-- The same arbitrary-accuracy reduction at the literal manuscript
cutoff, without assuming any estimate for the retained rectangle sum. -/
theorem eventually_sum_abs_logCutoff_halfProductDiscrepancy_le_actualGridRectangles_logAccuracy
    {num den k : ℕ} (hden : 0 < den)
    (hb : 0 < (num : ℝ) / (den : ℝ))
    (hb1 : (num : ℝ) / (den : ℝ) < 1) (A : ℕ) (hk : A + 2 < k) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ D : ℕ, ∀ S : Finset ℕ,
        D ≤ N → S ⊆ Finset.Icc 1 D →
        (∑ d ∈ S, |halfProductCongruenceMass num den N (logCutoff N) d -
          halfProductCoprimeMass num den N (logCutoff N) d / (Nat.totient d : ℝ)|) ≤
        (∑ ij ∈ actualGridIntersectingIndices num den N (logCutoff N)
            (1 + boundaryLogMesh k N),
          ∑ d ∈ S, |actualGridRectangleDiscrepancy (1 + boundaryLogMesh k N) ij N d|) +
          epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_sum_abs_halfProductPrimitiveDiscrepancy_le_actualGridRectangles_logAccuracy
      hden hb hb1 A hk epsilon hepsilon, eventually_one_le_nat_log]
    with N hreduce hlog
  intro D S hD hS
  have hpow : 1 ≤ (Real.log (N : ℝ)) ^ 10 := one_le_pow₀ hlog
  have hpowpos : 0 < (Real.log (N : ℝ)) ^ 10 := by linarith
  have hcutoff : logCutoff N ≤ (N : ℝ) := by
    unfold logCutoff
    apply (div_le_iff₀ hpowpos).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg N)
  exact hreduce (logCutoff N) D S (logCutoff_nonneg N) hcutoff hD hS

end

end ImbalancedChen
