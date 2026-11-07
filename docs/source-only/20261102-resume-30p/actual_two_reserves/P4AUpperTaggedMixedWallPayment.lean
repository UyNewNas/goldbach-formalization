import ImbalancedChen.P4ACommonPolicyTaggedCompiler
import ImbalancedChen.P2CanonicalWallFullResidualPayment
import ImbalancedChen.FirstExitValidSelection

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

The arithmetic wall supplier reused below is policy-independent: it factors
the actual canonical prime prefix from the COMPLETE residual divisor sum.
No lower coefficient or lower attachment is used. The new charge is the
literal O upper tagged compiler's changed/crossing set on that carrier.

This pays any specified finite family of proper canonical-prefix walls,
with one positive width before N and uniformly in the later fine mesh.
It does NOT assume or assert that those walls cover every mixed cell of
the held policy8, or that policy8 is the full original 87-domain policy.
-/

namespace ImbalancedChen.P4AUpperTaggedMixedWallPayment

noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler
open P2CanonicalWallFullResidualPayment

/-- The complete retained-support test is the actual canonical first-exit
selection. Canonicalization uses the real descending rough-prime carrier. -/
theorem raw_support_iff_canonical_validSelection
    (keep : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    d ∈ rawSupport keep N cap w z ↔
      d ∈ universe N cap w z ∧
        FirstExitValidSelection (oddFirstExitPolicy keep) [] true
          d.primeFactorsList.reverse := by
  have hmem : d ∈ rawSupport keep N cap w z ↔
      ∃ chosen : List ℕ, chosen <+ roughPrimeUniverse N cap w z ∧
        FirstExitValidSelection (oddFirstExitPolicy keep) [] true chosen ∧
          chosen.prod = d := by
    change d ∈ firstExitRetainedModuli (oddFirstExitPolicy keep)
      (roughPrimeUniverse N cap w z) ↔ _
    exact mem_firstExitRetainedModuli_iff_validSelection _ _ _
  constructor
  · intro hd
    obtain ⟨chosen, hsub, hvalid, hprod⟩ := hmem.mp hd
    have heq := P2LowerCanonicalRetainedTrace.actual_chosen_eq_canonical
      N cap w z chosen hsub hprod
    exact ⟨rawSupport_subset_universe keep N cap w z hd, heq ▸ hvalid⟩
  · rintro ⟨hd, hvalid⟩
    obtain ⟨hsub, hprod⟩ :=
      P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N cap w z hd
    exact hmem.mpr ⟨d.primeFactorsList.reverse, hsub, hvalid, hprod⟩

/-- The point being charged, d itself, has an opposite canonical selection
in its own frozen tagged cell. A wall around a different retained witness
alone would not justify a bound for the mass summed at d. -/
theorem crossing_at_point_has_opposite_canonical_selection
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) {d : ℕ}
    (hd : d ∈ universe N cap w z) (hc : crossing keep tag N cap w z tau d) :
    ∃ e ∈ cell tag N cap w z tau d, tag e = tag d ∧
      primeWordLabel N tau e = primeWordLabel N tau d ∧
      ¬(FirstExitValidSelection (oddFirstExitPolicy keep) [] true
          d.primeFactorsList.reverse ↔
        FirstExitValidSelection (oddFirstExitPolicy keep) [] true
          e.primeFactorsList.reverse) := by
  obtain ⟨a, ha, b, hb, hretain, hreject⟩ :=
    crossing_has_opposite_witnesses keep tag N cap w z tau hc
  by_cases hraw : d ∈ rawSupport keep N cap w z
  · refine ⟨b, hb, cell_frozen_tag tag N cap w z tau hb,
      cell_prime_labels tag N cap w z tau hb, ?_⟩
    intro heq
    apply hreject
    exact (raw_support_iff_canonical_validSelection keep N cap w z b).mpr
      ⟨(Finset.mem_filter.mp hb).1,
        heq.mp ((raw_support_iff_canonical_validSelection keep N cap w z d).mp hraw).2⟩
  · refine ⟨a, ha, cell_frozen_tag tag N cap w z tau ha,
      cell_prime_labels tag N cap w z tau ha, ?_⟩
    intro heq
    apply hraw
    exact (raw_support_iff_canonical_validSelection keep N cap w z d).mpr
      ⟨hd, heq.mpr
        ((raw_support_iff_canonical_validSelection keep N cap w z a).mp hretain).2⟩

/-- Actual changed coefficients on the specified canonical-prefix walls. -/
def changedWallMass {j k : ℕ} (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (omega v tau : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) : ℝ :=
  ∑ d ∈ (canonicalWallModuli N cap omega v L c delta).filter
    (changed keep tag N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau),
    1 / (Nat.totient d : ℝ)

/-- Actual mixed tagged cells restricted at the charged point, after all
residual moduli have been included. No representative or cell count occurs. -/
def mixedWallMass {j k : ℕ} (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (omega v tau : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) : ℝ :=
  ∑ d ∈ (canonicalWallModuli N cap omega v L c delta).filter
    (crossing keep tag N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau),
    1 / (Nat.totient d : ℝ)

theorem wall_coefficient_error_eq_changedWallMass {j k : ℕ}
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (omega v tau : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) :
    reciprocalTotientDensity (canonicalWallModuli N cap omega v L c delta)
      (fun d => |coefficient keep tag N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau d -
        raw keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) d|) =
      changedWallMass keep tag N cap omega v tau L c delta := by
  unfold reciprocalTotientDensity changedWallMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  rw [abs_coefficient_sub_raw keep tag N cap _ _ tau (Finset.mem_filter.mp hd).1]
  split_ifs <;> simp

theorem changedWallMass_le_mixedWallMass {j k : ℕ}
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (omega v tau : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) :
    changedWallMass keep tag N cap omega v tau L c delta ≤
      mixedWallMass keep tag N cap omega v tau L c delta := by
  unfold changedWallMass mixedWallMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hd, hchanged⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨hd, changed_implies_crossing keep tag N cap _ _ tau
      (Finset.mem_filter.mp hd).1 hchanged⟩
  · intro d _ _
    positivity

/-- Quantitative finite mixed-cell estimate with its true arithmetic
prefix mass and complete residual Euler mass. The constant is one. -/
theorem mixedWallMass_le_actual_strip_mul_full_residual {j k : ℕ}
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (omega v tau : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) :
    mixedWallMass keep tag N cap omega v tau L c delta ≤
      actualPrimeAffineWallStripMass N (fun _ => omega) (fun _ => v) L c delta *
        P2ActualResidualUniverseMass.mass N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) := by
  apply le_trans ?_
    (canonical_wall_mass_le_strip_mul_full_residual N cap omega v L c delta)
  unfold mixedWallMass
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro d _ _
  positivity

/-- Frozen proper wall family and reserve, then width, then one threshold.
Uniformity in keep/tag/tau prevents multiplication by the later atom count.
There is no global mixed-cell coverage or final error hypothesis. -/
theorem exists_uniform_mixedWallMass_lt {j k : ℕ}
    (omega v : ℝ) (homega : 0 < omega) (hov : omega < v)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (hL : ∀ i, L i ≠ 0)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ,
      ∀ (keep : List ℕ → Bool) (tag : ℕ → List Bool) (tau : ℝ),
        mixedWallMass keep tag N cap omega v tau L c delta < eta := by
  obtain ⟨C, hC, Nm, hNm, hmass⟩ :=
    P2ActualResidualUniverseMass.exists_eventual_uniform_mass_bound omega v homega hov
  obtain ⟨delta, hdelta, Ns, _hNs, hstrip⟩ :=
    exists_actualPrimeAffineWallStrip_mass_lt homega hov L c hL
      (eta / C) (div_pos heta hC)
  refine ⟨delta, hdelta, max Nm Ns, hNm.trans (le_max_left _ _), ?_⟩
  intro N hN hEven cap keep tag tau
  have hm := hmass N ((le_max_left _ _).trans hN) hEven cap
  have hs := hstrip N ((le_max_right _ _).trans hN)
  have hS : 0 ≤ actualPrimeAffineWallStripMass N
      (fun _ : Fin j => omega) (fun _ => v) L c delta := by
    unfold actualPrimeAffineWallStripMass
    apply Finset.sum_nonneg
    intro p hp
    exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1
  exact (mixedWallMass_le_actual_strip_mul_full_residual keep tag N cap omega v tau L c delta).trans_lt
    ((mul_le_mul_of_nonneg_left hm hS).trans_lt ((lt_div_iff₀ hC).mp hs))

/-- Restricting the rough carrier to a wall does not replace the physical
coefficient: every occupied small/rough product is the global O rho entry. -/
theorem wall_rho_eq_global_rho {j k : ℕ}
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (omega v tau level : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ)
    {q : ℕ} (hq : q ∈ smallRoughModuli
      (actualSmallRosserSupport N cap ((N : ℝ) ^ omega))
      (canonicalWallModuli N cap omega v L c delta)) :
    smallRoughRho (actualSmallRosserSupport N cap ((N : ℝ) ^ omega))
      (canonicalWallModuli N cap omega v L c delta)
      (coefficient keep tag N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau)
      (actualSmallRosserMinus N cap ((N : ℝ) ^ omega) level)
      (actualSmallRosserPlus N cap ((N : ℝ) ^ omega) level) q =
    P4AUpperTaggedBetaAttachment.rho keep tag N cap ((N : ℝ) ^ omega)
      ((N : ℝ) ^ v) tau level q := by
  obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨ha, hd⟩ := Finset.mem_product.mp had
  rw [smallRoughRho_mul
    (fun _ hm => actualSmallRosserSupport_smallPrimeSupportedAt N cap _ hm)
    (fun _ hm => P2LowerFiniteCellRounding.universe_rough N cap _ _
      (Finset.mem_filter.mp hm).1) _ _ _ ha hd,
    P4AUpperTaggedBetaAttachment.rho_at_product keep tag N cap _ _ tau level
      ha (Finset.mem_filter.mp hd).1]

/-- Physical contribution of this same O rho on a fixed prefix-wall set. -/
def wallDensity {j k : ℕ} (N cap : ℕ) (omega v level : ℝ)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ)
    (roughCoeff : ℕ → ℝ) : ℝ :=
  physicalDensitySum
    (smallRoughModuli (actualSmallRosserSupport N cap ((N : ℝ) ^ omega))
      (canonicalWallModuli N cap omega v L c delta))
    (smallRoughRho (actualSmallRosserSupport N cap ((N : ℝ) ^ omega))
      (canonicalWallModuli N cap omega v L c delta) roughCoeff
      (actualSmallRosserMinus N cap ((N : ℝ) ^ omega) level)
      (actualSmallRosserPlus N cap ((N : ℝ) ^ omega) level))

/-- A genuine local compiler reserve, including all residual moduli and
actual beta slopes. This is not an input error estimate. Only the wall
family/properness is primitive; coverage of all mixed cells remains open. -/
theorem exists_same_rho_wall_compilation_payment {j k : ℕ}
    (nu epsilon v : ℝ) (hnu : 0 < nu) (he : 0 < epsilon) (he8 : epsilon < 1 / 8)
    (hv : nu * epsilon ^ 2 < v)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (hL : ∀ i, L i ≠ 0)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ,
      (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (cap : ℝ) →
      ∀ (keep : List ℕ → Bool) (tag : ℕ → List Bool) (tau : ℝ),
      let omega := nu * epsilon ^ 2
      let level := (N : ℝ) ^ (nu * epsilon)
      |wallDensity N cap omega v level L c delta
          (coefficient keep tag N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau) -
        wallDensity N cap omega v level L c delta
          (raw keep N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v))| <
        eta * (singularSeries N / Real.log (N : ℝ)) := by
  obtain ⟨B, hB, hsupply⟩ := exists_actualCompiledRho_target_density_difference_bound
  obtain ⟨Nd, hNd, hdensity⟩ := hsupply nu hnu epsilon he he8
  have homega : 0 < nu * epsilon ^ 2 := mul_pos hnu (sq_pos_of_pos he)
  let M : ℝ := B / (nu * epsilon ^ 2)
  have hM : 0 < M := div_pos hB homega
  obtain ⟨delta, hdelta, Nm, _hNm, hmass⟩ :=
    exists_uniform_mixedWallMass_lt (nu * epsilon ^ 2) v homega hv L c hL
      (eta / M) (div_pos heta hM)
  refine ⟨delta, hdelta, max Nd Nm, hNd.trans (le_max_left _ _), ?_⟩
  intro N hN hEven cap hcap keep tag tau
  have hN2 : 2 ≤ N := hNd.trans ((le_max_left _ _).trans hN)
  have hscale := densityScale_pos hN2
  have h := hdensity N ((le_max_left _ _).trans hN) hEven cap hcap
    (canonicalWallModuli N cap (nu * epsilon ^ 2) v L c delta)
    (fun _ hd => P2LowerFiniteCellRounding.universe_rough N cap _ _
      (Finset.mem_filter.mp hd).1)
    (coefficient keep tag N cap ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ v) tau)
    (raw keep N cap ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ v))
  dsimp only at h ⊢
  rw [wall_coefficient_error_eq_changedWallMass] at h
  change |wallDensity _ _ _ _ _ _ _ _ _ - wallDensity _ _ _ _ _ _ _ _ _| ≤
    (M * changedWallMass keep tag N cap (nu * epsilon ^ 2) v tau L c delta) *
      (singularSeries N / Real.log (N : ℝ)) at h
  have hm := hmass N ((le_max_right _ _).trans hN) hEven cap keep tag tau
  have hchanged :=
    (changedWallMass_le_mixedWallMass keep tag N cap (nu * epsilon ^ 2) v tau L c delta).trans_lt hm
  have hpay : M * changedWallMass keep tag N cap (nu * epsilon ^ 2) v tau L c delta < eta := by
    have hp := (lt_div_iff₀ hM).mp hchanged
    simpa only [mul_comm] using hp
  exact h.trans_lt (mul_lt_mul_of_pos_right hpay hscale)

end
end ImbalancedChen.P4AUpperTaggedMixedWallPayment
