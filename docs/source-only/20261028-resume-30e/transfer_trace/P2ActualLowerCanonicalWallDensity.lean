import ImbalancedChen.P2CanonicalWallFullResidualPayment
import ImbalancedChen.ActualCompilerDensityReserve

/-!
# The same actual LOWER rho on a canonical-prefix wall

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The small beta arguments are reversed for the lower coefficient. Negation
and beta-swap identify its density perturbation exactly with the existing
proved absolute supplier, so no upper-attachment theorem is silently used
with the wrong sign. The wall contribution equals a sum of the actual full
compiled rho entries on their unique small/rough products.

The uniform result below pays the full canonical-wall residual sum at the
manuscript density scale. It does not declare that all mixed warm fibres
are covered by the as-yet incomplete finite wall catalogue.
-/

namespace ImbalancedChen.P2ActualLowerCanonicalWallDensity

noncomputable section
open scoped Classical BigOperators
open P2LowerFiniteCellRounding
open P2CanonicalWallFullResidualPayment

private theorem coefficient_neg_swap (c lo hi : ℝ) :
    signAttachedCoefficient (-c) lo hi = -signAttachedCoefficient c hi lo := by
  by_cases h0 : c = 0
  · simp [h0, signAttachedCoefficient]
  · by_cases hc : 0 ≤ c
    · have hn : ¬ 0 ≤ -c := by intro hn; apply h0; linarith
      simp only [signAttachedCoefficient, if_neg hn, if_pos hc]
      ring
    · have hn : 0 ≤ -c := by linarith
      simp only [signAttachedCoefficient, if_pos hn, if_neg hc]
      ring

/-- Exact coefficient identity, including zero and off-support fibres. -/
theorem rho_neg_swap (small rough : Finset ℕ) (c lo hi : ℕ → ℝ) (q : ℕ) :
    smallRoughRho small rough (fun d => -c d) lo hi q =
      -smallRoughRho small rough c hi lo q := by
  unfold smallRoughRho
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  exact coefficient_neg_swap (c x.2) (lo x.1) (hi x.1)

theorem density_neg_swap (small rough : Finset ℕ) (c lo hi : ℕ → ℝ) :
    physicalDensitySum (smallRoughModuli small rough)
      (smallRoughRho small rough (fun d => -c d) lo hi) =
      -physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough c hi lo) := by
  unfold physicalDensitySum
  simp_rw [rho_neg_swap, neg_div]
  exact Finset.sum_neg_distrib

/-- Literal lower attachment of the SAME rough coefficient on the actual
canonical-wall subcarrier; no new small weights or normalization are used. -/
def lowerWallDensity {j k : ℕ} (N cap : ℕ) (omega v level : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ)
    (roughCoeff : ℕ → ℝ) : ℝ :=
  let small := actualSmallRosserSupport N cap ((N : ℝ) ^ omega)
  let rough := canonicalWallModuli N cap omega v L c delta
  physicalDensitySum (smallRoughModuli small rough)
    (smallRoughRho small rough roughCoeff
      (actualSmallRosserPlus N cap ((N : ℝ) ^ omega) level)
      (actualSmallRosserMinus N cap ((N : ℝ) ^ omega) level))

/-- The compiled wall density is an actual contribution of the complete
physical compiler rho: cutoff-separated factorization proves each entry. -/
theorem compiledWallDensity_eq_actual_rho_entries {j k : ℕ}
    (keep : List ℕ → Bool) (N cap : ℕ) (omega v tau level : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) :
    lowerWallDensity N cap omega v level L c delta
      (coefficient keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau) =
      ∑ q ∈ smallRoughModuli
        (actualSmallRosserSupport N cap ((N : ℝ) ^ omega))
        (canonicalWallModuli N cap omega v L c delta),
        P2LowerFiniteCellBetaCompiler.rho keep N cap ((N : ℝ) ^ omega)
          ((N : ℝ) ^ v) tau level q / (Nat.totient q : ℝ) := by
  have hsmall : ∀ e ∈ actualSmallRosserSupport N cap ((N : ℝ) ^ omega),
      SmallPrimeSupportedAt ((N : ℝ) ^ omega) e :=
    fun e he => actualSmallRosserSupport_smallPrimeSupportedAt N cap _ he
  have hrough : ∀ d ∈ canonicalWallModuli N cap omega v L c delta,
      RoughPrimeSupportedAt ((N : ℝ) ^ omega) d := by
    intro d hd
    exact universe_rough N cap _ _ (Finset.mem_filter.mp hd).1
  unfold lowerWallDensity physicalDensitySum
  rw [sum_smallRoughModuli hsmall hrough, sum_smallRoughModuli hsmall hrough]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨he, hd⟩ := Finset.mem_product.mp hx
  rw [smallRoughRho_mul hsmall hrough _ _ _ he hd,
    P2LowerFiniteCellBetaCompiler.rho_at_product keep N cap _ _ tau level he
      (Finset.mem_filter.mp hd).1]
  rfl

/-- Each occupied wall fibre is the SAME full compiler entry, by genuine
small/rough uniqueness. This is stronger than a density-sum identity. -/
theorem wall_rho_eq_actual_rho {j k : ℕ}
    (keep : List ℕ → Bool) (N cap : ℕ) (omega v tau level : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ)
    {q : ℕ} (hq : q ∈ smallRoughModuli
      (actualSmallRosserSupport N cap ((N : ℝ) ^ omega))
      (canonicalWallModuli N cap omega v L c delta)) :
    smallRoughRho (actualSmallRosserSupport N cap ((N : ℝ) ^ omega))
      (canonicalWallModuli N cap omega v L c delta)
      (coefficient keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau)
      (actualSmallRosserPlus N cap ((N : ℝ) ^ omega) level)
      (actualSmallRosserMinus N cap ((N : ℝ) ^ omega) level) q =
    P2LowerFiniteCellBetaCompiler.rho keep N cap ((N : ℝ) ^ omega)
      ((N : ℝ) ^ v) tau level q := by
  obtain ⟨⟨e, d⟩, hed, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨he, hd⟩ := Finset.mem_product.mp hed
  rw [smallRoughRho_mul
    (fun _ hm => actualSmallRosserSupport_smallPrimeSupportedAt N cap _ hm)
    (fun _ hm => universe_rough N cap _ _ (Finset.mem_filter.mp hm).1)
    _ _ _ he hd,
    P2LowerFiniteCellBetaCompiler.rho_at_product keep N cap _ _ tau level he
      (Finset.mem_filter.mp hd).1]
  rfl

/-- The raw comparison is also the installed original lower rho, on the
same physical q subcarrier. Zero extension does not change its entries. -/
theorem rawWallDensity_eq_actual_rho_entries {j k : ℕ}
    (keep : List ℕ → Bool) (N cap : ℕ) (omega v level : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) :
    lowerWallDensity N cap omega v level L c delta
      (raw keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v)) =
      ∑ q ∈ smallRoughModuli
        (actualSmallRosserSupport N cap ((N : ℝ) ^ omega))
        (canonicalWallModuli N cap omega v L c delta),
        actualLowerSmallRoughRho keep N cap ((N : ℝ) ^ omega)
          ((N : ℝ) ^ v) level q / (Nat.totient q : ℝ) := by
  have hs : ∀ e ∈ actualSmallRosserSupport N cap ((N : ℝ) ^ omega),
      SmallPrimeSupportedAt ((N : ℝ) ^ omega) e :=
    fun _ he => actualSmallRosserSupport_smallPrimeSupportedAt N cap _ he
  have hr : ∀ d ∈ canonicalWallModuli N cap omega v L c delta,
      RoughPrimeSupportedAt ((N : ℝ) ^ omega) d :=
    fun _ hd => universe_rough N cap _ _ (Finset.mem_filter.mp hd).1
  unfold lowerWallDensity physicalDensitySum
  rw [sum_smallRoughModuli hs hr, sum_smallRoughModuli hs hr]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨he, hd⟩ := Finset.mem_product.mp hx
  rw [← P2LowerFiniteCellBetaCompiler.raw_attachment_eq_actual keep N cap _ _ level,
    smallRoughRho_mul hs hr _ _ _ he hd,
    smallRoughRho_mul hs (fun _ hm => universe_rough N cap _ _ hm)
      _ _ _ he (Finset.mem_filter.mp hd).1]

/-- The actual marked SourceForm raw supplier bounds this very wall rho
with its original external pair multiplier. No raw-support or rank bound
is a new premise; no wall/global-coverage assertion is needed for support. -/
theorem sourceform_wall_rho_full_prefix_level {j k mesh : ℕ}
    (R : P2OriginalPairSourceReceiver.PairRange)
    (bank : P2OriginalLowerWholeBoxBranchSelect.CandidateBank mesh)
    (buffer : ℚ) (seed : ℝ)
    (hseed : seed ≤ P2OriginalLowerCompactStartCapConstructor.topCap)
    {N : ℕ} (hN : 1 < (N : ℝ)) (cap : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ P5SelectedMaskTransport.sixthSupport N)
    (omega ell tau : ℝ) (homega : 0 < omega) (htau : 0 < tau)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ)
    {q : ℕ}
    (hq : smallRoughRho (actualSmallRosserSupport N cap ((N : ℝ) ^ omega))
      (canonicalWallModuli N cap omega (417 / 5000) L c delta)
      (coefficient
        (P2OriginalPairRootRoughProducer.pairPolicy
          (P2OriginalPairSourceReceiver.pairPlan R bank buffer seed)
          (R.epsilon : ℝ) (P2OriginalPairSourceReceiver.ceiling : ℝ) seed N p)
        N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ (417 / 5000 : ℝ)) tau)
      (actualSmallRosserPlus N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ ell))
      (actualSmallRosserMinus N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ ell)) q ≠ 0) :
    (((p.1 * p.2) * q : ℕ) : ℝ) ≤ (N : ℝ) ^
      (P2OriginalLowerCompactStartCapConstructor.topCap + ell +
        (Nat.ceil (P2OriginalLowerCompactStartCapConstructor.topCap / omega) : ℝ) * tau) := by
  have hmem : q ∈ smallRoughModuli
      (actualSmallRosserSupport N cap ((N : ℝ) ^ omega))
      (canonicalWallModuli N cap omega (417 / 5000) L c delta) := by
    by_contra hmem
    exact hq (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hmem)
  rw [wall_rho_eq_actual_rho _ N cap omega (417 / 5000) tau _ L c delta hmem] at hq
  apply P2RoundedCausalFibreLossAndLevel.rounded_rho_full_level hN _ cap
    (p.1 * p.2) (Nat.ceil (P2OriginalLowerCompactStartCapConstructor.topCap / omega))
    _ _ P2OriginalLowerCompactStartCapConstructor.topCap ell htau ?_ hq
  intro r hr
  exact P2SourceFormPairRoundedSigmaLevel.sourceform_pair_raw_support
    R bank buffer seed hseed hN cap hp omega homega hr

/-- The existing actual supplier pays the lower beta swap by an exact
negation identity. The charge is the FULL rough-modulus wall sum. -/
theorem exists_actual_lower_wall_density_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ nu : ℝ, 0 < nu →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (cap : ℝ) →
      ∀ j k : ℕ, ∀ v tau : ℝ,
      ∀ L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ, ∀ c : Fin k → ℝ, ∀ delta : ℝ,
      ∀ keep : List ℕ → Bool,
      let omega := nu * epsilon ^ 2
      let level := (N : ℝ) ^ (nu * epsilon)
      |lowerWallDensity N cap omega v level L c delta
          (coefficient keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau) -
        lowerWallDensity N cap omega v level L c delta
          (raw keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v))| ≤
        ((B / omega) * wallRoundingCharge keep N cap omega v tau L c delta) *
          (singularSeries N / Real.log (N : ℝ)) := by
  obtain ⟨B, hB, hsupply⟩ := exists_actualCompiledRho_target_density_difference_bound
  refine ⟨B, hB, ?_⟩
  intro nu hnu epsilon he he8
  obtain ⟨N0, hN0, hsupply⟩ := hsupply nu hnu epsilon he he8
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap j k v tau L c delta keep
  let omega := nu * epsilon ^ 2
  let rough := canonicalWallModuli N cap omega v L c delta
  let comp := coefficient keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau
  let old := raw keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v)
  have hr : ∀ d ∈ rough, RoughPrimeSupportedAt ((N : ℝ) ^ omega) d := by
    intro d hd
    exact universe_rough N cap _ _ (Finset.mem_filter.mp hd).1
  have h := hsupply N hN hEven cap hcap rough hr (fun d => -comp d) (fun d => -old d)
  dsimp only at h ⊢
  simp_rw [density_neg_swap] at h
  have hm : reciprocalTotientDensity rough (fun d => |-comp d - -old d|) =
      wallRoundingCharge keep N cap omega v tau L c delta := by
    unfold reciprocalTotientDensity wallRoundingCharge
    apply Finset.sum_congr rfl
    intro d _
    simp only [neg_sub_neg, abs_sub_comm]
  rw [hm] at h
  simpa only [neg_sub_neg, abs_sub_comm, lowerWallDensity, comp, old, rough, omega] using h

/-- Uniform normalized arithmetic wall contribution, after ALL residual
moduli and the true lower beta attachment have been paid. Width is chosen
before N and before every later cap, causal policy and rounding mesh. -/
theorem exists_actual_lower_full_residual_wall_reserve {j k : ℕ}
    (nu epsilon v : ℝ) (hnu : 0 < nu) (he : 0 < epsilon) (he8 : epsilon < 1 / 8)
    (hv : nu * epsilon ^ 2 < v)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (hL : ∀ i, L i ≠ 0)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ,
      (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (cap : ℝ) →
      ∀ (keep : List ℕ → Bool) (tau : ℝ),
      let omega := nu * epsilon ^ 2
      let level := (N : ℝ) ^ (nu * epsilon)
      |lowerWallDensity N cap omega v level L c delta
          (coefficient keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau) -
        lowerWallDensity N cap omega v level L c delta
          (raw keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v))| ≤
        eta * (singularSeries N / Real.log (N : ℝ)) := by
  obtain ⟨B, hB, hsupply⟩ := exists_actual_lower_wall_density_bound
  obtain ⟨Nd, hNd, hdensity⟩ := hsupply nu hnu epsilon he he8
  have homega : 0 < nu * epsilon ^ 2 := mul_pos hnu (sq_pos_of_pos he)
  let M : ℝ := B / (nu * epsilon ^ 2)
  have hM : 0 < M := div_pos hB homega
  obtain ⟨delta, hdelta, Nm, hNm, hmass⟩ :=
    exists_uniform_full_residual_wall_payment (nu * epsilon ^ 2) v homega hv
      L c hL (eta / M) (div_pos heta hM)
  refine ⟨delta, hdelta, max Nd Nm, hNd.trans (le_max_left _ _), ?_⟩
  intro N hN hEven cap hcap keep tau
  have hd := hdensity N ((le_max_left _ _).trans hN) hEven cap hcap j k v tau L c delta keep
  have hm := hmass N ((le_max_right _ _).trans hN) hEven cap keep tau
  have hsmall : M * wallRoundingCharge keep N cap (nu * epsilon ^ 2) v tau L c delta ≤ eta := by
    have h := (lt_div_iff₀ hM).mp hm
    nlinarith
  have hN2 : 2 ≤ N := hNd.trans ((le_max_left _ _).trans hN)
  have hNR : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hn : 0 ≤ singularSeries N / Real.log (N : ℝ) :=
    div_nonneg (singularSeries_pos N).le (Real.log_pos hNR).le
  dsimp only at hd ⊢
  exact hd.trans (mul_le_mul_of_nonneg_right hsmall hn)

end
end ImbalancedChen.P2ActualLowerCanonicalWallDensity
