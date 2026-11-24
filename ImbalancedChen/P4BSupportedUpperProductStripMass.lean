import ImbalancedChen.P4BSupportedRampStripUnion
import ImbalancedChen.P4BOuterRampRoughness
import ImbalancedChen.P4BPhysicalShellMass

/-!
# P4B: arithmetic mass of the jointly supported physical upper strip

YELLOW / SOURCE-ONLY / UNCOMPILED. Sibling imports name their intended
future normal modules. The strip is the genuine physicalSupportedStrip
at wall 3, with all other softened margins retained.

The tuple product is sorted only after proving both possible b/2 power
inequalities from the actual softened order and imbalance walls. Product
and orientation together form an injection into two copies of the actual
ordered-source physical shell. Even-target endpoint exclusion uses the
proved roughness and the eventual condition N^theta>=2; it is not inferred
from N>=8 alone. The shell mass supplier is proved in its sibling module.
No boundary count, roughness estimate or analytic mass conclusion is a
hypothesis of the final reserve theorem.
-/

namespace ImbalancedChen.P4BSupportedUpperProductStripMass

noncomputable section
open Filter Topology
open scoped BigOperators
open Classical
open ImbalancedChen.Part3
open ImbalancedChen.P4B
open ImbalancedChen.P4BLabelledPairDictionary
open ImbalancedChen.P4BLabelledLogGeometry
open ImbalancedChen.P4BOuterRampRoughness
open ImbalancedChen.P4BPhysicalShellMass

/-- Strict softened scalar support gives a positive actual scalar ramp. -/
theorem logGateOuterRamp_pos_of_soft_support
    {width x : ℝ} (hwidth : 0 < width) (hx : -width < x) :
    0 < logGateOuterRamp width x := by
  have hdiv : -1 < x / width := (lt_div_iff₀ hwidth).mpr (by linarith only [hx])
  have hterm : 0 < 1 + x / width := by linarith only [hdiv]
  exact lt_min zero_lt_one (hterm.trans_le (le_max_right _ _))

/-- All joint softened gates make the literal four-ramp weight nonzero. -/
theorem physical_ramp_ne_zero_of_all_soft_margins
    {b T width : ℝ} {N : ℕ} {t : Fin 2 → Fin (N + 1)}
    (hwidth : 0 < width)
    (hsoft : ∀ j : Fin 4, -width < physicalPairMargins b N T t j) :
    physicalPairOuterRamp b N T width t ≠ 0 := by
  change (∏ i : Fin 4, logGateOuterRamp width (physicalPairMargins b N T t i)) ≠ 0
  exact ne_of_gt (Finset.prod_pos fun i hi =>
    logGateOuterRamp_pos_of_soft_support hwidth (hsoft i))

/-- A narrow enough relaxed order/imbalance corner satisfies both possible
half-exponent inequalities, so sorting introduces no artificial badness. -/
theorem softened_corner_half_exponent_bounds
    {b theta width x y : ℝ} (hb : 0 < b) (hb1 : b < 1) (htheta : 0 < theta)
    (hx : theta < x) (hy : theta < y) (hwidth : width ≤ b * theta / 4)
    (horder : -width < y - x) (hbalance : -width < x - b * y) :
    (b / 2) * y < x ∧ (b / 2) * x < y := by
  have hbt : 0 < b * theta := mul_pos hb htheta
  have hby : b * theta < b * y := mul_lt_mul_of_pos_left hy hb
  have hbtheta : b * theta < theta := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hb1 htheta
  have hx0 : 0 < x := htheta.trans hx
  have hbx : b * x < x := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hb1 hx0
  constructor
  · nlinarith only [hwidth, hbt, hby, hbalance]
  · nlinarith only [hwidth, hbtheta, hx, hbx, hx0, horder]

/-- Every jointly supported tuple obeys strict rough-coordinate bounds. -/
theorem supported_upper_log_coordinates_rough
    {b kappa theta width : ℝ} {N : ℕ} (hb : 0 < b) (hN : 2 ≤ N)
    (hwidth : 0 < width) (hgap : 2 * width ≤ baseline b kappa - theta)
    {t : Fin 2 → Fin (N + 1)}
    (ht : t ∈ physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 3) :
    theta < logPoint N t 0 ∧ theta < logPoint N t 1 := by
  obtain ⟨htprime, hstrip, hsoft⟩ := (mem_physicalSupportedStrip _ _ _ _ _ _).mp ht
  exact physical_ramp_nonzero_log_coordinates_above_theta hb hN hwidth hgap
    (physical_ramp_ne_zero_of_all_soft_margins hwidth hsoft)

/-- Sorted tuple factors satisfy the genuine strict ordered badness wall
with exponent b/2. This conclusion is derived from the actual joint gates. -/
theorem supported_upper_product_realOrderedBad_half
    {b kappa theta width : ℝ} {N : ℕ}
    (hb : 0 < b) (hb1 : b < 1) (htheta : 0 < theta) (hN : 2 ≤ N)
    (hwidth : 0 < width) (hgap : 2 * width ≤ baseline b kappa - theta)
    (hwidthSmall : width ≤ b * theta / 4)
    {t : Fin 2 → Fin (N + 1)}
    (ht : t ∈ physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 3) :
    RealOrderedBadReceiver (b / 2) (labelledProduct t) := by
  obtain ⟨htprime, hstrip, hsoft⟩ := (mem_physicalSupportedStrip _ _ _ _ _ _).mp ht
  have hprime : ∀ i : Fin 2, Nat.Prime (t i).val := (Finset.mem_filter.mp htprime).2
  obtain ⟨hx, hy⟩ := supported_upper_log_coordinates_rough hb hN hwidth hgap ht
  have horder := hsoft (0 : Fin 4)
  have hbalance := hsoft (1 : Fin 4)
  rw [physicalPairMargins_eq_original_of_ne_upper b _ N t (by decide : (0 : Fin 4) ≠ 3)] at horder
  rw [physicalPairMargins_eq_original_of_ne_upper b _ N t (by decide : (1 : Fin 4) ≠ 3)] at hbalance
  change -width < logPoint N t 1 - logPoint N t 0 at horder
  change -width < logPoint N t 0 - b * logPoint N t 1 at hbalance
  obtain ⟨hforward, hreverse⟩ := softened_corner_half_exponent_bounds
    hb hb1 htheta hx hy hwidthSmall horder hbalance
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hrR, hqR⟩ := labelled_prime_pair_pos htprime
  have hforwardPow : ((tuplePair t).2 : ℝ) ^ (b / 2) < ((tuplePair t).1 : ℝ) :=
    (power_iff_normalized_logs (b / 2) hN1 hrR hqR).mpr hforward
  have hreversePow : ((tuplePair t).1 : ℝ) ^ (b / 2) < ((tuplePair t).2 : ℝ) :=
    (power_iff_normalized_logs (b / 2) hN1 hqR hrR).mpr hreverse
  by_cases hsorted : (tuplePair t).1 ≤ (tuplePair t).2
  · exact ⟨(tuplePair t).1, (tuplePair t).2, hprime 0, hprime 1,
      labelledProduct_eq_pairProduct t, hsorted, hforwardPow⟩
  · exact ⟨(tuplePair t).2, (tuplePair t).1, hprime 1, hprime 0,
      (labelledProduct_eq_pairProduct t).trans (Nat.mul_comm _ _),
      (lt_of_not_ge hsorted).le, hreversePow⟩

/-- The even-target endpoint is excluded only after the actual tuple
factors have been proved strictly larger than the small prime two. -/
theorem supported_upper_product_ne_even_target
    {b kappa theta width : ℝ} {N : ℕ} (hb : 0 < b) (hN : 2 ≤ N)
    (hEven : Even N) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - theta)
    (hpower : (2 : ℝ) ≤ (N : ℝ) ^ theta)
    {t : Fin 2 → Fin (N + 1)}
    (ht : t ∈ physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 3) :
    labelledProduct t ≠ N := by
  obtain ⟨htprime, hstrip, hsoft⟩ := (mem_physicalSupportedStrip _ _ _ _ _ _).mp ht
  intro heq
  have htwo : 2 ∣ labelledProduct t := by
    rw [heq]
    obtain ⟨k, hk⟩ := hEven
    exact ⟨k, by omega⟩
  have hrough := physical_ramp_nonzero_prime_divisor_rough hb hN hwidth hgap htprime
    (physical_ramp_ne_zero_of_all_soft_margins hwidth hsoft) Nat.prime_two htwo
  exact (not_lt_of_ge hpower) hrough

/-- A supported physical upper-strip product lies in an actual ordered
b/2 source shell of any larger physical logarithmic width. -/
theorem supported_upper_product_mem_physical_shell
    {b kappa theta width shellWidth : ℝ} {N : ℕ}
    (hb : 0 < b) (hb1 : b < 1) (htheta : 0 < theta) (hN : 2 ≤ N)
    (hEven : Even N) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - theta)
    (hwidthSmall : width ≤ b * theta / 4) (hwidthShell : width ≤ shellWidth)
    (hpower : (2 : ℝ) ≤ (N : ℝ) ^ theta)
    {t : Fin 2 → Fin (N + 1)}
    (ht : t ∈ physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 3) :
    labelledProduct t ∈ physicalProductShell (b / 2) (Real.exp shellWidth) N := by
  obtain ⟨htprime, hstrip, hsoft⟩ := (mem_physicalSupportedStrip _ _ _ _ _ _).mp ht
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hprodLower, hprodUpper⟩ :=
    (physical_upper_margin_strip_iff_product_shell hN1 htprime).mp hstrip
  have hNprod : N ≤ labelledProduct t := by
    exact_mod_cast (show (N : ℝ) ≤ (labelledProduct t : ℝ) by
      simpa only [labelledProduct_eq_pairProduct] using hprodLower)
  have hne := supported_upper_product_ne_even_target hb hN hEven hwidth hgap hpower ht
  have hprodStrict : N < labelledProduct t := by omega
  have hupper : (labelledProduct t : ℝ) < Real.exp width * (N : ℝ) := by
    simpa only [labelledProduct_eq_pairProduct] using hprodUpper
  have hcap : labelledProduct t ≤ Nat.floor (Real.exp shellWidth * (N : ℝ)) := by
    apply Nat.le_floor
    exact hupper.le.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr hwidthShell) (Nat.cast_nonneg N))
  exact mem_physicalProductShell.mpr ⟨hprodStrict, hcap,
    supported_upper_product_realOrderedBad_half hb hb1 htheta hN hwidth hgap hwidthSmall ht⟩

/-- The orientation tag distinguishes the two possible labelled orders. -/
def orientationTag {N : ℕ} (t : Fin 2 → Fin (N + 1)) : ℕ :=
  if (tuplePair t).1 ≤ (tuplePair t).2 then 0 else 1

theorem labelled_product_orientation_injective
    {N : ℕ} {t u : Fin 2 → Fin (N + 1)}
    (ht : t ∈ labelledPrimeTuples 2 N) (hu : u ∈ labelledPrimeTuples 2 N)
    (hprod : labelledProduct t = labelledProduct u)
    (htag : orientationTag t = orientationTag u) : t = u := by
  have htprime : ∀ i : Fin 2, Nat.Prime (t i).val := (Finset.mem_filter.mp ht).2
  have huprime : ∀ i : Fin 2, Nat.Prime (u i).val := (Finset.mem_filter.mp hu).2
  have hmul : (tuplePair t).1 * (tuplePair t).2 =
      (tuplePair u).1 * (tuplePair u).2 := by
    simpa only [labelledProduct_eq_pairProduct] using hprod
  apply tuplePair_injective N
  by_cases hto : (tuplePair t).1 ≤ (tuplePair t).2
  · have huo : (tuplePair u).1 ≤ (tuplePair u).2 := by
      by_contra huo
      simp [orientationTag, hto, huo] at htag
    obtain ⟨hfirst, hsecond⟩ := ordered_prime_factors_unique
      (htprime 0) (htprime 1) (huprime 0) (huprime 1) hto huo hmul
    exact Prod.ext hfirst hsecond
  · have huo : ¬(tuplePair u).1 ≤ (tuplePair u).2 := by
      intro huo
      simp [orientationTag, hto, huo] at htag
    have hreverse : (tuplePair t).2 * (tuplePair t).1 =
        (tuplePair u).2 * (tuplePair u).1 := by
      simpa only [Nat.mul_comm] using hmul
    obtain ⟨hsecond, hfirst⟩ := ordered_prime_factors_unique
      (htprime 1) (htprime 0) (huprime 1) (huprime 0)
      (lt_of_not_ge hto).le (lt_of_not_ge huo).le hreverse
    exact Prod.ext hfirst hsecond

/-- Exact finite multiplicity payment: product and orientation inject into
two copies of the actual ordered-source shell, including prime squares. -/
theorem supported_upper_strip_card_le_two_shell
    {b kappa theta width shellWidth : ℝ} {N : ℕ}
    (hb : 0 < b) (hb1 : b < 1) (htheta : 0 < theta) (hN : 2 ≤ N)
    (hEven : Even N) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - theta)
    (hwidthSmall : width ≤ b * theta / 4) (hwidthShell : width ≤ shellWidth)
    (hpower : (2 : ℝ) ≤ (N : ℝ) ^ theta) :
    (physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 3).card ≤
      2 * (physicalProductShell (b / 2) (Real.exp shellWidth) N).card := by
  have hcard :
      (physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 3).card ≤
        ((physicalProductShell (b / 2) (Real.exp shellWidth) N) ×ˢ Finset.range 2).card := by
    apply Finset.card_le_card_of_injOn (fun t => (labelledProduct t, orientationTag t))
    · intro t ht
      apply Finset.mem_product.mpr
      refine ⟨supported_upper_product_mem_physical_shell hb hb1 htheta hN hEven
        hwidth hgap hwidthSmall hwidthShell hpower ht, ?_⟩
      dsimp only [orientationTag]
      split_ifs <;> norm_num
    · intro t ht u hu htu
      apply labelled_product_orientation_injective
        ((mem_physicalSupportedStrip _ _ _ _ _ _).mp ht).1
        ((mem_physicalSupportedStrip _ _ _ _ _ _).mp hu).1
        (congrArg Prod.fst htu) (congrArg Prod.snd htu)
  simpa only [Finset.card_product, Finset.card_range, Nat.mul_comm] using hcard

/-- The actual wall-3 supported-strip reserve has one positive physical
width and one common natural threshold. No mass or roughness input remains. -/
theorem exists_width_eventually_supported_upper_strip_le
    {b kappa : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1)
    (eta widthMax : ℝ) (heta : 0 < eta) (hwidthMax : 0 < widthMax) :
    ∃ width : ℝ, 0 < width ∧ width ≤ widthMax ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → Even N →
        ((physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 3).card : ℝ) ≤
          eta * ((N : ℝ) / Real.log (N : ℝ)) := by
  have hhalf : 0 < b / 2 := half_pos hb
  have hhalf1 : b / 2 < 1 := by linarith only [hb1]
  obtain ⟨shellWidth, hshellWidth, Nshell, hshell⟩ :=
    exists_log_width_eventually_shell_le hhalf hhalf1 (eta / 2) (half_pos heta)
  have hbase : 0 < baseline b kappa := by
    unfold baseline
    exact div_pos (mul_pos (sub_pos.mpr hkappa1) hb) (by linarith only [hb])
  let theta : ℝ := baseline b kappa / 2
  have htheta : 0 < theta := half_pos hbase
  let width : ℝ := min widthMax (min shellWidth (min (baseline b kappa / 4) (b * theta / 4)))
  have hwidth : 0 < width := lt_min hwidthMax
    (lt_min hshellWidth (lt_min (by positivity) (by positivity)))
  have hwidthMax' : width ≤ widthMax := min_le_left _ _
  have hwidthShell : width ≤ shellWidth :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hwidthBase : width ≤ baseline b kappa / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hwidthSmall : width ≤ b * theta / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hgap : 2 * width ≤ baseline b kappa - theta := by
    dsimp only [theta]
    linarith only [hwidthBase]
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ theta) atTop atTop :=
    (tendsto_rpow_atTop htheta).comp tendsto_natCast_atTop_atTop
  have hpaid : ∀ᶠ N : ℕ in atTop, Even N →
      ((physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 3).card : ℝ) ≤
        eta * ((N : ℝ) / Real.log (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop Nshell, eventually_ge_atTop (2 : ℕ),
      hpower.eventually (eventually_ge_atTop (2 : ℝ))] with N hNshell hN hNpower
    intro hEven
    have hfinite :
        ((physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 3).card : ℝ) ≤
          2 * ((physicalProductShell (b / 2) (Real.exp shellWidth) N).card : ℝ) := by
      exact_mod_cast supported_upper_strip_card_le_two_shell hb hb1 htheta hN hEven
        hwidth hgap hwidthSmall hwidthShell hNpower
    have hshellN := hshell N hNshell
    linarith only [hfinite, hshellN]
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hpaid
  exact ⟨width, hwidth, hwidthMax', N0, hN0⟩

end

end ImbalancedChen.P4BSupportedUpperProductStripMass
