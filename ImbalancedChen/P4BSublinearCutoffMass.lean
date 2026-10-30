import ImbalancedChen.P4BSourceCutoffTransport
import ImbalancedChen.RealHalfProductMassSuppliers
import ImbalancedChen.PowerErrorBudget

/-!
# Actual source mass is independent of a sublinear power cutoff

SOURCE ONLY / YELLOW / UNCOMPILED. The sibling transport import is its
intended future normal module name.

The exact cutoff band bounds the cardinality change by `ceil(max T U)`.
Every eventually nonnegative cutoff `L(N) ≤ C*N^theta`, with fixed `C ≥ 0`
and `theta < 1`, consequently has the same actual source mass coefficient
`log(1/b)` as the proved manuscript source. We compare with the existing
supplier at `kappa=1/2`. The small-cutoff payment is proved from the existing
logarithm-versus-positive-power absorption theorem, with no supplied mass
estimate. No density, distribution, or upper-sieve conclusion is asserted.
-/

namespace ImbalancedChen.P4BSublinearCutoffMass

noncomputable section
open Filter Topology
open P4BSourceCutoffTransport

/-- The exact removed band lies below its strict upper cutoff. The real
upper wall is encoded by the actual natural ceiling, including at integers. -/
theorem cutoffBand_card_le_ceil_of_upper
    (b : ℝ) (N : ℕ) (T U V : ℝ) (hUV : U ≤ V) :
    (cutoffBand b N T U).card ≤ Nat.ceil V := by
  have hsub : cutoffBand b N T U ⊆ Finset.range (Nat.ceil V) := by
    intro m hm
    have hmU := (mem_cutoffBand.mp hm).2.2.2
    exact Finset.mem_range.mpr (Nat.lt_ceil.mpr (hmU.trans_le hUV))
  simpa only [Finset.card_range] using Finset.card_le_card hsub

/-- A finite cutoff change costs at most the ceiling of the larger cutoff.
This statement even permits negative real cutoffs. -/
theorem source_card_abs_sub_le_ceil_max (b : ℝ) (N : ℕ) (T U : ℝ) :
    |((realHalfProductSource b N T).card : ℝ) -
        ((realHalfProductSource b N U).card : ℝ)| ≤
      (Nat.ceil (max T U) : ℝ) := by
  rcases le_total T U with hTU | hUT
  · rw [source_card_sub_eq_band hTU, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast cutoffBand_card_le_ceil_of_upper b N T U (max T U)
      (le_max_right T U)
  · rw [abs_sub_comm, source_card_sub_eq_band hUT,
      abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast cutoffBand_card_le_ceil_of_upper b N U T (max T U)
      (le_max_left T U)

/-- The familiar real bound, with its exact one-unit rounding buffer. -/
theorem source_card_abs_sub_le_max_add_one (b : ℝ) (N : ℕ) (T U : ℝ)
    (hmax : 0 ≤ max T U) :
    |((realHalfProductSource b N T).card : ℝ) -
        ((realHalfProductSource b N U).card : ℝ)| ≤ max T U + 1 := by
  exact (source_card_abs_sub_le_ceil_max b N T U).trans
    (Nat.ceil_lt_add_one hmax).le

/-- A sum-form envelope convenient for paying two nonnegative cutoffs
separately on the source-mass scale. -/
theorem source_card_abs_sub_le_cutoffs_add_one
    (b : ℝ) (N : ℕ) {T U : ℝ} (hT : 0 ≤ T) (hU : 0 ≤ U) :
    |((realHalfProductSource b N T).card : ℝ) -
        ((realHalfProductSource b N U).card : ℝ)| ≤ T + U + 1 := by
  have hmax : 0 ≤ max T U := hT.trans (le_max_left T U)
  have hsum : max T U ≤ T + U := max_le (by linarith) (by linarith)
  exact (source_card_abs_sub_le_max_add_one b N T U hmax).trans
    (add_le_add_left hsum 1)

/-- Fixed sublinear real powers, including their additive unit, are
negligible relative to `N/log N`. This is derived from the proved
manuscript-cutoff log/rpow absorption, not assumed as a growth estimate. -/
theorem eventually_sublinearPower_add_one_le_massScale
    {C theta : ℝ} (hC : 0 ≤ C) (htheta : theta < 1) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) ^ theta + 1 ≤
        epsilon * ((N : ℝ) / Real.log (N : ℝ)) := by
  intro epsilon hepsilon
  let D : ℝ := C + 1
  have hD : 0 < D := by dsimp only [D]; linarith
  have hsmall := eventually_manuscriptHalfProductCutoff_add_one_le_massScale
    (κ := 1 - theta) (sub_pos.mpr htheta)
    (epsilon / D) (div_pos hepsilon hD)
  filter_upwards [hsmall] with N hsmallN
  have hpow : 0 ≤ (N : ℝ) ^ theta := Real.rpow_nonneg (Nat.cast_nonneg N) theta
  have hexponent : 1 - (1 - theta) = theta := by ring
  have hcompare : C * (N : ℝ) ^ theta + 1 ≤
      D * (manuscriptHalfProductCutoff (1 - theta) N + 1) := by
    dsimp only [D]
    simp only [manuscriptHalfProductCutoff, hexponent]
    nlinarith only [hC, hpow, mul_nonneg hC hpow]
  calc
    C * (N : ℝ) ^ theta + 1 ≤
        D * (manuscriptHalfProductCutoff (1 - theta) N + 1) := hcompare
    _ ≤ D * ((epsilon / D) * ((N : ℝ) / Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hsmallN hD.le
    _ = epsilon * ((N : ℝ) / Real.log (N : ℝ)) := by
      have hcancel : D * (epsilon / D) = epsilon := by
        field_simp [ne_of_gt hD]
      rw [← mul_assoc, hcancel]

/-- An arbitrary cutoff beneath an eventual sublinear power envelope
changes the actual source cardinality by a negligible amount relative to
the existing manuscript source at `kappa=1/2`. -/
theorem eventually_source_card_cutoff_error_le_massScale
    (b : ℝ) (L : ℕ → ℝ) {C theta : ℝ}
    (hC : 0 ≤ C) (htheta : theta < 1)
    (hL : ∀ᶠ N : ℕ in atTop, 0 ≤ L N ∧ L N ≤ C * (N : ℝ) ^ theta) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ N : ℕ in atTop,
      |((realHalfProductSource b N (L N)).card : ℝ) -
          ((realHalfProductSource b N
            (manuscriptHalfProductCutoff (1 / 2) N)).card : ℝ)| ≤
        epsilon * ((N : ℝ) / Real.log (N : ℝ)) := by
  intro epsilon hepsilon
  filter_upwards
    [hL, eventually_sublinearPower_add_one_le_massScale hC htheta
      (epsilon / 2) (half_pos hepsilon),
      eventually_manuscriptHalfProductCutoff_add_one_le_massScale
        (κ := (1 / 2 : ℝ)) (by norm_num) (epsilon / 2) (half_pos hepsilon)]
    with N hLN hpower hmanuscript
  have hfinite := source_card_abs_sub_le_cutoffs_add_one b N hLN.1
    (manuscriptHalfProductCutoff_nonneg (1 / 2) N)
  linarith [hLN.2]

/-- The actual ordered half-product source mass for every eventually
nonnegative cutoff bounded by a fixed sublinear power. PNT and weighted
Mertens are discharged by the existing suppliers; there is no `hMass`
parameter and no altered multiplicity or strict badness predicate. -/
theorem tendsto_source_sublinearCutoff_mass
    {b C theta : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hC : 0 ≤ C) (htheta : theta < 1) (L : ℕ → ℝ)
    (hL : ∀ᶠ N : ℕ in atTop, 0 ≤ L N ∧ L N ≤ C * (N : ℝ) ^ theta) :
    Tendsto (fun N : ℕ =>
      ((realHalfProductSource b N (L N)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)))
      atTop (𝓝 (Real.log (1 / b))) := by
  have hbase := tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers
    (κ := (1 / 2 : ℝ)) hb hb1 (by norm_num)
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hnear := (Metric.tendsto_nhds.mp hbase)
    (epsilon / 2) (half_pos hepsilon)
  filter_upwards
    [eventually_source_card_cutoff_error_le_massScale b L hC htheta hL
      (epsilon / 2) (half_pos hepsilon), hnear,
      eventually_ge_atTop (2 : ℕ)] with N herr hnearN hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 < (N : ℝ) / Real.log (N : ℝ) :=
    div_pos (zero_lt_one.trans hN1) (Real.log_pos hN1)
  have herrsmall :
      |((realHalfProductSource b N (L N)).card : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) -
        ((realHalfProductSource b N
          (manuscriptHalfProductCutoff (1 / 2) N)).card : ℝ) /
            ((N : ℝ) / Real.log (N : ℝ))| ≤ epsilon / 2 := by
    rw [← sub_div, abs_div, abs_of_pos hscale]
    exact (div_le_iff₀ hscale).mpr herr
  rw [Real.dist_eq] at hnearN ⊢
  have htriangle := abs_add_le
    (((realHalfProductSource b N (L N)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) -
      ((realHalfProductSource b N
        (manuscriptHalfProductCutoff (1 / 2) N)).card : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)))
    (((realHalfProductSource b N
        (manuscriptHalfProductCutoff (1 / 2) N)).card : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) - Real.log (1 / b))
  have heq :
      ((realHalfProductSource b N (L N)).card : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) -
        ((realHalfProductSource b N
          (manuscriptHalfProductCutoff (1 / 2) N)).card : ℝ) /
            ((N : ℝ) / Real.log (N : ℝ)) +
        (((realHalfProductSource b N
          (manuscriptHalfProductCutoff (1 / 2) N)).card : ℝ) /
            ((N : ℝ) / Real.log (N : ℝ)) - Real.log (1 / b)) =
      ((realHalfProductSource b N (L N)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) - Real.log (1 / b) := by ring
  rw [heq] at htriangle
  linarith

/-- In particular the literal real cutoff `C*N^theta` has the true source
mass coefficient, for every fixed `C ≥ 0` and `theta < 1`. -/
theorem tendsto_source_powerCutoff_mass
    {b C theta : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hC : 0 ≤ C) (htheta : theta < 1) :
    Tendsto (fun N : ℕ =>
      ((realHalfProductSource b N (C * (N : ℝ) ^ theta)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)))
      atTop (𝓝 (Real.log (1 / b))) := by
  apply tendsto_source_sublinearCutoff_mass hb hb1 hC htheta
    (fun N => C * (N : ℝ) ^ theta)
  exact Filter.Eventually.of_forall fun N =>
    ⟨mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg N) theta), le_rfl⟩

end
end ImbalancedChen.P4BSublinearCutoffMass
