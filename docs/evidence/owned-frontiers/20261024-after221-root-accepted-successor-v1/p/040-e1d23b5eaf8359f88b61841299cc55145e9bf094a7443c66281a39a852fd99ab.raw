import ImbalancedChen.Part3ActualRestrictedChartWeightCount
import ImbalancedChen.Part3ActualLogTagBetaRestriction

/-!
SOURCEONLY / UNCOMPILED / INDEPENDENT MODULE ASSEMBLY CANDIDATE.
Proposed module: ImbalancedChen.Part3ActualChartTagHeightCount.
The first import has real current actual source76b718 (header-open repair). The second is PENDING
ROOT installation/compilation from exact177f Part3ActualLogTagBetaRestriction.
It is a declared project dependency, not a claim of an installed import.
Only this header/import block changes from original223LF/d119 append.
The complete namespace suffix below is byte-for-byte identical: no theorem,
definition, hypothesis or by proof changes. Positive/closedT/restricted bodies
are imported transitively, never copied into this module. Only public parent
APIs are consumed; private proof helpers below belong to this module itself.
This is module assembly only, with no new mathematical completion claim.
-/

namespace ImbalancedChen.Part3.ActualChartTagHeight576SourceOnly
noncomputable section
attribute [local instance] Classical.propDecidable
open Classical Finset CommonSmoothCutoff
open ActualReciprocalSquarePoissonSourceOnly ActualCompletedSquarePushforwardSourceOnly
open ActualM2FinitePoissonAdapterSourceOnly ActualSeparatedRowPacketMatchSourceOnly
open ActualModeBetaPositiveCountSourceOnly ActualClosedTCountLicenseSourceOnly
open ActualRestrictedChartWeightCountSourceOnly ActualLogTagHSupportSourceOnly
open ActualPositiveLatticeSmoothCoverSourceOnly
open scoped BigOperators

/-- Exact existing nonzero-y and signed-fKey filters, independent of h height. -/
private lemma fBlock_eq_carrier_filter (A : ℕ) (a : ℤ) (S : ℝ)
    (upper : Bool) (H : ℕ) (F : ℝ) (fj : ℕ × Bool) :
    fBlock A a S upper H F fj =
      (carrier A a (tChart S upper) H (Icc (Int.ceil (-F)) (Int.floor F))).filter
        (fun s => (output s).2 ≠ 0 ∧ fKey s = fj) := by
  ext s
  simp only [fBlock, upperSource, nonzeroSource, mem_filter]
  tauto

/-- SAME actual mode weights and SAME signed-f chart; only the two h caps differ. -/
theorem actual_chart_beta_eq_tag_height (e : MediumAtom) (D delta g l : ℕ)
    [NeZero (g*l)] (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (upper : Bool) (fj : ℕ × Bool)
    (zy : Output) :
    beta (actualChartSource e D delta g l Z negative upper fj)
      (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) zy =
    beta (fBlock (g*l) (signedResidue negative e.residue)
      (e.Q2 / ((D/delta : ℕ) : ℝ)) upper (tagFrequencyBound tag) (scaleF e D g) fj)
      (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) zy := by
  unfold actualChartSource
  rw [fBlock_eq_carrier_filter, fBlock_eq_carrier_filter]
  convert (actual_beta_global_eq_tag_bound e D g l Z tag m negative k (g*l)
    (signedResidue negative e.residue) (tChart (e.Q2 / ((D/delta : ℕ) : ℝ)) upper)
    (Icc (Int.ceil (-scaleF e D g)) (Int.floor (scaleF e D g)))
    (fun s => (output s).2 ≠ 0 ∧ fKey s = fj)
    (actualModeLambda e D delta g l m negative u k) zy) using 1 <;>
    congr 1 <;>
    ext s <;>
    simp only [mem_filter]

/-- Algebraic zero-extension across two different output images. No subset-beta bound. -/
private theorem beta_energy_eq_of_pointwise (U V : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (nu : ℕ)
    (heq : ∀ zy, beta U lambda omega zy = beta V lambda omega zy) :
    (∑ zy ∈ U.image output, if (nu : ℤ) ∣ zy.2 then
      ‖beta U lambda omega zy‖^2 else 0) =
    ∑ zy ∈ V.image output, if (nu : ℤ) ∣ zy.2 then
      ‖beta V lambda omega zy‖^2 else 0 := by
  let W := U.image output ∪ V.image output
  have hz (T : Finset Source) (zy : Output) (hn : zy ∉ T.image output) :
      beta T lambda omega zy = 0 := by
    by_contra hb
    exact hn (beta_ne_zero_mem_image hb)
  have hU : (∑ zy ∈ U.image output, if (nu : ℤ) ∣ zy.2 then
      ‖beta U lambda omega zy‖^2 else 0) =
      ∑ zy ∈ W, if (nu : ℤ) ∣ zy.2 then ‖beta U lambda omega zy‖^2 else 0 := by
    apply sum_subset (show U.image output ⊆ W from subset_union_left)
    intro zy _ hn
    simp only [hz U zy hn, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), ite_self]
  have hV : (∑ zy ∈ V.image output, if (nu : ℤ) ∣ zy.2 then
      ‖beta V lambda omega zy‖^2 else 0) =
      ∑ zy ∈ W, if (nu : ℤ) ∣ zy.2 then ‖beta V lambda omega zy‖^2 else 0 := by
    apply sum_subset (show V.image output ⊆ W from subset_union_right)
    intro zy _ hn
    simp only [hz V zy hn, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), ite_self]
  calc
    _ = ∑ zy ∈ W, if (nu : ℤ) ∣ zy.2 then ‖beta U lambda omega zy‖^2 else 0 := hU
    _ = ∑ zy ∈ W, if (nu : ℤ) ∣ zy.2 then ‖beta V lambda omega zy‖^2 else 0 := by
      apply sum_congr rfl
      intro zy _
      rw [heq zy]
    _ = _ := hV.symm

/-- Auxiliary expression for the SAME energy on its exactly equivalent h-tag source. -/
def tagChartWeightedEnergy (e : MediumAtom) (D delta g l : ℕ)
    [NeZero (g*l)] (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (upper : Bool) (fj : ℕ × Bool) (nu : ℕ) : ℝ :=
  let U := fBlock (g*l) (signedResidue negative e.residue)
    (e.Q2 / ((D/delta : ℕ) : ℝ)) upper (tagFrequencyBound tag) (scaleF e D g) fj
  ∑ zy ∈ U.image output, if (nu : ℤ) ∣ zy.2 then
    ‖beta U (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) zy‖^2 else 0

theorem actual_chart_energy_eq_tag_height (e : MediumAtom) (D delta g l : ℕ)
    [NeZero (g*l)] (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (upper : Bool) (fj : ℕ × Bool) (nu : ℕ) :
    actualChartWeightedEnergy e D delta g l Z tag m negative u k upper fj nu =
      tagChartWeightedEnergy e D delta g l Z tag m negative u k upper fj nu := by
  unfold actualChartWeightedEnergy tagChartWeightedEnergy
  dsimp only
  apply beta_energy_eq_of_pointwise
  intro zy
  exact actual_chart_beta_eq_tag_height e D delta g l Z tag m negative u k upper fj zy

section ActualMode
variable {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
variable (he : MediumAdmissible B sigma kappa c0 e)
variable (D delta g l : ℕ) [NeZero (g*l)] (Z : ℝ)
variable (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
variable (u : (ZMod (g*l))ˣ) (k : ZMod (g*l))
include he

/-- Public actual mode norm suppliers apply to this t-chart at ANY h cap.
No Htag<=Hglobal or containment in the global h carrier is asserted. -/
private theorem tag_chart_weight_norm_le (hq : 0 < D/delta)
    (upper : Bool) (fj : ℕ × Bool) {s : Source}
    (hs : s ∈ fBlock (g*l) (signedResidue negative e.residue)
      (e.Q2 / ((D/delta : ℕ) : ℝ)) upper (tagFrequencyBound tag) (scaleF e D g) fj) :
    ‖weight (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) s‖ ≤ 1 := by
  have hc := (mem_filter.mp (mem_filter.mp hs).1).1
  have hr := (mem_filter.mp hc).1
  have hp := mem_product.mp (mem_product.mp hr).2
  have ht1 := (mem_product.mp hp.1).1
  have ht2 := (mem_product.mp hp.2).1
  have hQ2 : 0 ≤ e.Q2 := zero_le_one.trans he.2.2.2.1
  have ht1' : s.2.1.1 ∈ baseCarrier e (D/delta) := by
    rw [baseCarrier_eq_factorCarrier_div e hQ2 hq]
    exact (mem_filter.mp ht1).1
  have ht2' : s.2.2.1 ∈ baseCarrier e (D/delta) := by
    rw [baseCarrier_eq_factorCarrier_div e hQ2 hq]
    exact (mem_filter.mp ht2).1
  have h1 := actualModeLambda_norm_le he D delta g l m negative u k ht1'
  have h2 := actualModeLambda_norm_le he D delta g l m negative u k ht2'
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

private theorem tag_chart_beta_norm_le_count (hq : 0 < D/delta)
    (upper : Bool) (fj : ℕ × Bool) (zy : Output) :
    let U := fBlock (g*l) (signedResidue negative e.residue)
      (e.Q2 / ((D/delta : ℕ) : ℝ)) upper (tagFrequencyBound tag) (scaleF e D g) fj
    ‖beta U (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) zy‖ ≤ ((fiber U zy).card : ℝ) := by
  dsimp only
  unfold beta
  calc
    _ ≤ ∑ s ∈ fiber (fBlock (g*l) (signedResidue negative e.residue)
        (e.Q2 / ((D/delta : ℕ) : ℝ)) upper (tagFrequencyBound tag) (scaleF e D g) fj) zy,
        ‖weight (actualModeLambda e D delta g l m negative u k)
          (actualModeOmega e D g l Z tag m negative k) s‖ := norm_sum_le _ _
    _ ≤ ∑ _s ∈ fiber (fBlock (g*l) (signedResidue negative e.residue)
        (e.Q2 / ((D/delta : ℕ) : ℝ)) upper (tagFrequencyBound tag) (scaleF e D g) fj) zy,
        (1 : ℝ) := by
      apply sum_le_sum
      intro s hs
      exact tag_chart_weight_norm_le he D delta g l Z tag m negative u k hq upper fj
        (mem_filter.mp hs).1
    _ = _ := by simp only [sum_const, nsmul_eq_mul, mul_one]

/-- The original restricted weighted energy is charged at Htag, with cost1. -/
theorem actual_chart_energy_le_tag_count (hq : 0 < D/delta)
    (upper : Bool) (fj : ℕ × Bool) (nu : ℕ) :
    actualChartWeightedEnergy e D delta g l Z tag m negative u k upper fj nu ≤
      chartCountEnergy (g*l) (signedResidue negative e.residue)
        (e.Q2 / ((D/delta : ℕ) : ℝ)) upper (tagFrequencyBound tag) (scaleF e D g) fj nu := by
  rw [actual_chart_energy_eq_tag_height]
  unfold tagChartWeightedEnergy chartCountEnergy
  dsimp only
  apply sum_le_sum
  intro zy _
  by_cases hd : (nu : ℤ) ∣ zy.2
  · simp only [if_pos hd]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (tag_chart_beta_norm_le_count he D delta g l Z tag m negative u k hq upper fj zy) 2
  · simp only [if_neg hd, le_refl]

/-- Original public one-chart576 contract, now at the PROVED h-tag height.
The LHS is literally the old actualChartWeightedEnergy, not a renamed count.
No global-height assumption and no relationship between tag.2 and fj.2. -/
theorem actual_chart_weighted_576_tag_height (hq : 0 < D/delta)
    (upper : Bool) (fj : ℕ × Bool) (nu : ℕ) (hnu : 0 < nu) :
    let S := e.Q2 / ((D/delta : ℕ) : ℝ)
    let H := tagFrequencyBound tag
    let R := countScale S upper
    let G := fScale fj.1
    actualChartWeightedEnergy e D delta g l Z tag m negative u k upper fj nu ≤
      576*(LichtmanSignedDifferenceMultiplicity.divisorMaximum R H G : ℝ)^5*
        (harmonic (Nat.floor (2*R)) : ℝ)*(1+(H : ℝ)/R)*((H : ℝ)*R)^2*G/(nu : ℝ) ∧
      (8*G*(H : ℝ)*R ≤ (nu : ℝ) →
        actualChartWeightedEnergy e D delta g l Z tag m negative u k upper fj nu = 0) := by
  dsimp only
  have hQ2 : 0 < e.Q2 := zero_lt_one.trans_le he.2.2.2.1
  have hqR : (0 : ℝ) < ((D/delta : ℕ) : ℝ) := by exact_mod_cast hq
  have hS := div_pos hQ2 hqR
  have hH : 1 ≤ tagFrequencyBound tag := by
    rw [tagFrequencyBound_eq]
    exact Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2 : ℕ)) _)
  have hb := actual_chart_count_576 (A := g*l) (a := signedResidue negative e.residue)
    hS upper (tagFrequencyBound tag) hH (scaleF e D g) fj nu hnu
  have hd := actual_chart_energy_le_tag_count he D delta g l Z tag m negative u k hq upper fj nu
  refine ⟨hd.trans hb.1, ?_⟩
  intro hlarge
  apply le_antisymm
  · simpa only [hb.2 hlarge] using hd
  · unfold actualChartWeightedEnergy
    dsimp only
    exact sum_nonneg (fun _ _ => by split_ifs <;> positivity)

end ActualMode
end
end ImbalancedChen.Part3.ActualChartTagHeight576SourceOnly
