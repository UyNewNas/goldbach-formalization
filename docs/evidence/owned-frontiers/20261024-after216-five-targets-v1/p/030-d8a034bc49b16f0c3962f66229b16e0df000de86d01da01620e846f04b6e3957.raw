import ImbalancedChen.Part3ActualModeJointBetaPositiveCount
import ImbalancedChen.Part3ActualClosedTCountLicense

/-!
SOURCEONLY / UNCOMPILED module assembly candidate.
The two project imports above are PENDING ROOT installation and strict compilation
from this batch's recipe. At assembly time neither proposed project module exists.
The repaired restricted consumer namespace body below is byte-for-byte unchanged.
Only PUBLIC APIs of the two pending modules are consumed; no private supplier is
cross-file referenced. No chart/sign/mode recombination or spectral closure is
asserted by this assembly, and no proof/definition/premise is altered.
-/
namespace ImbalancedChen.Part3.ActualRestrictedChartWeightCountSourceOnly
noncomputable section
open Classical Finset CommonSmoothCutoff GeneralDGateNormalization
open ActualFixedFeaturePacketPushforwardSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly ActualM2FinitePoissonAdapterSourceOnly
open ActualPositiveLatticeSmoothCoverSourceOnly ActualReciprocalSquarePoissonSourceOnly
open ActualCompletedSquarePushforwardSourceOnly ActualClosedTCountLicenseSourceOnly
open ActualModeBetaPositiveCountSourceOnly
open GeneralDActiveOuterEnergySourceOnly GeneralDActivePairCountSourceOnly
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The quotient's positivity is supplied by an actual nonempty fixed slice. -/
theorem quotient_pos_of_actual_fixedSlice
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) (Yb Ys : ℝ)
    {D delta g l : ℕ} (hD : 0 < D) {o : OuterIndex}
    (ho : o ∈ fixedSlice e Yb Ys D delta g l) : 0 < D / delta := by
  obtain ⟨_, _, _, hr, _, _, _, _, hd, _, _, _, _⟩ :=
    fixedSlice_facts e Yb Ys D delta g l ho
  have hR : 1 ≤ e.Q3 := he.2.2.2.2.1
  have hq := (quotient_data (factorCarrier_bounds hR hr).1 hD).1
  simpa only [quotient, hd] using hq

/-- This is one original t-chart and one original signed dyadic-f fibre. -/
def actualChartSource (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ)
    (negative upper : Bool) (j : ℕ × Bool) : Finset Source :=
  fBlock (g*l) (signedResidue negative e.residue)
    (e.Q2 / ((D/delta : ℕ) : ℝ)) upper (e.sharedSmoothFrequencyBound Z D)
    (scaleF e D g) j

theorem actualChartSource_subset_actual
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    (D delta g l : ℕ) (Z : ℝ) (negative : Bool) (hq : 0 < D/delta)
    (upper : Bool) (j : ℕ × Bool) :
    actualChartSource e D delta g l Z negative upper j ⊆
      actualNonzeroSource e D delta g l Z negative := by
  have hQ2 : 0 ≤ e.Q2 := zero_le_one.trans he.2.2.2.1
  unfold actualChartSource actualNonzeroSource
  rw [baseCarrier_eq_factorCarrier_div e hQ2 hq]
  exact fBlock_subset_fullSource _ _ _ _ _ _ _

/-- The SAME restricted joint coefficient, with its original complex weights. -/
def actualChartWeightedEnergy (e : MediumAtom) (D delta g l : ℕ)
    [NeZero (g*l)] (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ)
    (negative : Bool) (u : (ZMod (g*l))ˣ) (k : ZMod (g*l))
    (upper : Bool) (j : ℕ × Bool) (nu : ℕ) : ℝ :=
  let U := actualChartSource e D delta g l Z negative upper j
  ∑ zy ∈ U.image output, if (nu : ℤ) ∣ zy.2 then
    ‖beta U (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) zy‖^2 else 0

section ActualMode
variable {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
variable (he : MediumAdmissible B sigma kappa c0 e)
variable (D delta g l : ℕ) [NeZero (g*l)] (Z : ℝ)
variable (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
variable (u : (ZMod (g*l))ˣ) (k : ZMod (g*l))
include he

private theorem restricted_weight_norm_le (hq : 0 < D/delta)
    (upper : Bool) (j : ℕ × Bool) {s : Source}
    (hs : s ∈ actualChartSource e D delta g l Z negative upper j) :
    ‖weight (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) s‖ ≤ 1 := by
  have hs' := actualChartSource_subset_actual he D delta g l Z negative hq upper j hs
  have hr := (mem_filter.mp (mem_filter.mp hs').1).1
  have hp := mem_product.mp (mem_product.mp hr).2
  have ht1 := (mem_product.mp hp.1).1
  have ht2 := (mem_product.mp hp.2).1
  have h1 := actualModeLambda_norm_le he D delta g l m negative u k ht1
  have h2 := actualModeLambda_norm_le he D delta g l m negative u k ht2
  have hh1 := actualModeOmega_norm_le e D g l Z tag m negative k s.2.1.2
  have hh2 := actualModeOmega_norm_le e D g l Z tag m negative k s.2.2.2
  have ha1 : ‖atomCoeff (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) s.2.1‖ ≤ 1 := by
    rw [atomCoeff, norm_mul]
    exact (mul_le_mul h1 hh1 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have ha2 : ‖atomCoeff (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) s.2.2‖ ≤ 1 := by
    rw [atomCoeff, norm_mul]
    exact (mul_le_mul h2 hh2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  rw [weight, norm_mul, norm_star]
  exact (mul_le_mul ha1 ha2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- This never bounds a subset coefficient by a possibly cancelling full beta. -/
theorem actual_chart_beta_norm_le_count (hq : 0 < D/delta)
    (upper : Bool) (j : ℕ × Bool) (zy : Output) :
    ‖beta (actualChartSource e D delta g l Z negative upper j)
      (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) zy‖ ≤
      ((fiber (actualChartSource e D delta g l Z negative upper j) zy).card : ℝ) := by
  unfold beta
  calc
    _ ≤ ∑ s ∈ fiber (actualChartSource e D delta g l Z negative upper j) zy,
        ‖weight (actualModeLambda e D delta g l m negative u k)
          (actualModeOmega e D g l Z tag m negative k) s‖ := norm_sum_le _ _
    _ ≤ ∑ _s ∈ fiber (actualChartSource e D delta g l Z negative upper j) zy, (1 : ℝ) := by
      apply sum_le_sum
      intro s hs
      exact restricted_weight_norm_le he D delta g l Z tag m negative u k hq upper j
        (mem_filter.mp hs).1
    _ = _ := by simp only [sum_const, nsmul_eq_mul, mul_one]

/-- One literal chart receives the SAME positive counting energy, with cost1. -/
theorem actual_chart_weighted_energy_le_count (hq : 0 < D/delta)
    (upper : Bool) (j : ℕ × Bool) (nu : ℕ) :
    actualChartWeightedEnergy e D delta g l Z tag m negative u k upper j nu ≤
      chartCountEnergy (g*l) (signedResidue negative e.residue)
        (e.Q2 / ((D/delta : ℕ) : ℝ)) upper (e.sharedSmoothFrequencyBound Z D)
        (scaleF e D g) j nu := by
  unfold actualChartWeightedEnergy chartCountEnergy
  dsimp only [actualChartSource]
  apply sum_le_sum
  intro zy _
  by_cases hd : (nu : ℤ) ∣ zy.2
  · simp only [if_pos hd]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (actual_chart_beta_norm_le_count he D delta g l Z tag m negative u k hq upper j zy) 2
  · simp only [if_neg hd, le_refl]

/-- Actual restricted mode coefficients meet the old576/nu licence on ONE
closed-T/sign/dyadic-f chart. No recombination factor is silently paid here. -/
theorem actual_chart_weighted_576 (hq : 0 < D/delta)
    (upper : Bool) (j : ℕ × Bool) (hH : 1 ≤ e.sharedSmoothFrequencyBound Z D)
    (nu : ℕ) (hnu : 0 < nu) :
    let S := e.Q2 / ((D/delta : ℕ) : ℝ)
    let H := e.sharedSmoothFrequencyBound Z D
    let R := countScale S upper
    let G := fScale j.1
    actualChartWeightedEnergy e D delta g l Z tag m negative u k upper j nu ≤
      576*(LichtmanSignedDifferenceMultiplicity.divisorMaximum R H G : ℝ)^5*
        (harmonic (Nat.floor (2*R)) : ℝ)*(1+(H : ℝ)/R)*((H : ℝ)*R)^2*G/(nu : ℝ) ∧
      (8*G*(H : ℝ)*R ≤ (nu : ℝ) →
        actualChartWeightedEnergy e D delta g l Z tag m negative u k upper j nu = 0) := by
  dsimp only
  have hQ2 : 0 < e.Q2 := zero_lt_one.trans_le he.2.2.2.1
  have hqR : (0 : ℝ) < ((D/delta : ℕ) : ℝ) := by exact_mod_cast hq
  have hS := div_pos hQ2 hqR
  have hb := actual_chart_count_576 (A := g*l) (a := signedResidue negative e.residue)
    hS upper (e.sharedSmoothFrequencyBound Z D) hH (scaleF e D g) j nu hnu
  have hd := actual_chart_weighted_energy_le_count he D delta g l Z tag m negative u k
    hq upper j nu
  refine ⟨hd.trans hb.1, ?_⟩
  intro hlarge
  apply le_antisymm
  · simpa only [hb.2 hlarge] using hd
  · unfold actualChartWeightedEnergy
    dsimp only
    exact sum_nonneg (fun _ _ => by split_ifs <;> positivity)

end ActualMode
end
end ImbalancedChen.Part3.ActualRestrictedChartWeightCountSourceOnly
