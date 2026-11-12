import ImbalancedChen.Part5OriginalH430FrozenClassicalRootAP
import ImbalancedChen.Part5OriginalH430RootIntervalTheta
import ImbalancedChen.P5zElevenErrorTransport

/-! The ordinary AP pool for all original classical U3 roots is
little-o of the physical mass on the positive-width structural clamp.
The comparison level N^(1/2) enters only in the lower bound for that
mass. Each paid AP row still uses its own frozen Q and original key. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalRootThetaPayment
noncomputable section
open Finset Filter Real
open scoped Classical BigOperators Topology
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2OriginalPositiveSameQMassLift (thetaAtom_nonneg)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430TaggedArithmeticReceivers (originalBand original_band_prime)
open Part5OriginalH430RootIntervalTheta
open Part5OriginalH430RootRosserSurplus (signedAP)
open Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430FrozenClassicalRootAP (classical_tail_AP_log_saving)

theorem clamp_subset_classical {N : ℕ} (hN : 2 ≤ N) :
    clampPrimes N ⊆ classicalBand N := by
  intro p hp
  obtain ⟨hb, hlo⟩ := Finset.mem_filter.mp hp
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp := zero_lt_one.trans hNr
  have h := Real.log_le_log (Real.rpow_pos_of_pos hNp clampStart) hlo
  rw [Real.log_rpow hNp] at h
  have hcoord : clampStart ≤ physicalPrime N p := by
    apply (le_div_iff₀ (Real.log_pos hNr)).mpr
    simpa only [mul_comm] using h
  exact Finset.mem_filter.mpr ⟨hb, (by norm_num [tailCutoff, clampStart] :
    tailCutoff ≤ clampStart).trans hcoord⟩

private theorem interval_subset_clamp {N : ℕ} (hN : 1 ≤ N) :
    primeBand N clampStart (1/3) ⊆ clampPrimes N := by
  intro p hp
  obtain ⟨hc, hlo, hhi⟩ := Finset.mem_filter.mp hp
  have ha : (N:ℝ)^a ≤ (N:ℝ)^clampStart := Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hN) (by norm_num [a, clampStart])
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hc, ha.trans hlo, hhi⟩, hlo⟩

private theorem theta_antitone {N p : ℕ} {Q Q' : ℝ}
    (hN : 4 ≤ N) (hp : 0 < p) (hR : 1 < Q/(p:ℝ)) (hQ : Q ≤ Q') :
    thetaAtom N Q' p ≤ thetaAtom N Q p := by
  have hφ : 0 < (Nat.totient p:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hp)
  have huv := div_le_div_of_nonneg_right hQ (Nat.cast_nonneg p)
  have hl := Real.log_pos hR
  have hl' := Real.log_pos (hR.trans_le huv)
  have hθ := thetaAtom_nonneg hN hp hR
  have he : thetaAtom N Q' p * Real.log (Q'/p) =
      thetaAtom N Q p * Real.log (Q/p) := by
    unfold thetaAtom
    field_simp [hφ.ne', hl.ne', hl'.ne'] <;> ring
  have hprod := mul_le_mul_of_nonneg_left (Real.log_le_log (zero_lt_one.trans hR) huv) hθ
  by_contra! h
  linarith only [he, hprod, mul_lt_mul_of_pos_right h hl']

/-- One fixed half-level test integral is a uniform positive witness
for every permitted frozen n and every τ in the geometry range. -/
theorem uniform_clamp_witness :
    let I := intervalMass clampStart (1/3) (1/2)
    0 < I ∧ ∀ᶠ N : ℕ in atTop, ∀ (n : ℕ) (τ : ℝ),
      0 ≤ τ → τ ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      (I/2)*singularNormalization N ≤ clampMass N n τ := by
  dsimp only
  let I := intervalMass clampStart (1/3) (1/2)
  have hb : 0 < clampStart := by norm_num [clampStart]
  have hbc : clampStart < 1/3 := by norm_num [clampStart]
  have hI : 0 < I := intervalMass_positive hb hbc (by norm_num)
  have hh := actual_interval_theta_limit hb hbc (by norm_num : (1/3:ℝ)<1)
    (by norm_num : (1/3:ℝ)<1/2)
  refine ⟨hI, ?_⟩
  filter_upwards [hh.eventually (Ioi_mem_nhds (show I/2 < I by linarith)),
    eventually_singularNormalization_pos, eventually_ge_atTop (4:ℕ)] with N hw hS hN
  intro n τ hτ hτ' hn
  have h2 : 2 ≤ N := by omega
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let B := primeBand N clampStart (1/3)
  have hB : B ⊆ clampPrimes N := interval_subset_clamp (by omega)
  have hsmall : I/2 * singularNormalization N ≤
      ∑ p ∈ B, thetaAtom N ((N:ℝ)^(1/2:ℝ)) p := ((lt_div_iff₀ hS).mp hw).le
  apply hsmall.trans
  calc
    _ ≤ ∑ p ∈ B, thetaAtom N (rootQ N n .U3 τ p) p := by
      apply Finset.sum_le_sum
      intro p hp
      have hc := clamp_subset_classical h2 (hB hp)
      have hg := classical_geometry (m := 0) h2 hτ hτ' hn hc
      exact theta_antitone hN (original_band_prime (Finset.mem_filter.mp hc).1).1.pos hg.1
        (hg.2.2.trans (Real.rpow_le_rpow_of_exponent_le hNr (by linarith)))
    _ ≤ clampMass N n τ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hB
      intro p hp _
      have hc := clamp_subset_classical h2 hp
      exact thetaAtom_nonneg hN (original_band_prime (Finset.mem_filter.mp hc).1).1.pos
        (classical_geometry (m := 0) h2 hτ hτ' hn hc).1

def classicalMass (N n : ℕ) (τ : ℝ) : ℝ :=
  ∑ p ∈ classicalBand N, thetaAtom N (rootQ N n .U3 τ p) p

theorem clampMass_le_classicalMass {N n : ℕ} {τ : ℝ} (hN : 4 ≤ N)
    (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    clampMass N n τ ≤ classicalMass N n τ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (clamp_subset_classical (by omega))
  intro p hp _
  exact thetaAtom_nonneg hN (original_band_prime (Finset.mem_filter.mp hp).1).1.pos
    (classical_geometry (m := 0) (by omega) hτ hτ' hn hp).1

/-- A single ε allowance pays the entire absolute signed-row pool
against the true clamp mass, uniformly in both resolutions. τ is fixed
before its BV threshold. No marked family is divided by its Θ. -/
theorem complete_classical_AP_le_clamp_theta {τ ε : ℝ}
    (hτ : 0 < τ) (hτ' : τ ≤ 1/12) (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ n m : ℕ, 1/((n:ℝ)+1) ≤ 11/384 →
      (∑ p ∈ classicalBand N, |signedAP N p (rootQ N n .U3 τ p)
        (cutoffAt N n m p τ)|) ≤ ε * clampMass N n τ := by
  let I := intervalMass clampStart (1/3) (1/2)
  obtain ⟨hi, hw⟩ := uniform_clamp_witness
  have hI : 0 < I := hi
  obtain ⟨C, _, hAP⟩ := classical_tail_AP_log_saving hτ hτ' 3 (by decide)
  filter_upwards [hAP, hw,
    p5z_eventually_logCube_le_singularNormalization C (ε*(I/2)) (by positivity)]
    with N hp hmass hnorm
  intro n m hn
  calc
    _ ≤ _ := hp n m hn
    _ ≤ (ε*(I/2))*singularNormalization N := hnorm
    _ = ε*((I/2)*singularNormalization N) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hmass n τ hτ.le hτ' hn) he.le

end
end ImbalancedChen.Part5OriginalH430ClassicalRootThetaPayment
