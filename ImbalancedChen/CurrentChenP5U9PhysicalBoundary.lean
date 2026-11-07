import ImbalancedChen.P5zUpsilon9SourceMass

/-!
# The actual U9 source near the physical upper boundary

SOURCE ONLY / UNCOMPILED. The band is (1-kappa)N < product < N,
on the original labelled, centre-coprime source with its square-root cutoff.
It is not a fixed erosion of the logarithmic exponent simplex.

Both prime-counting endpoints have their exact natural floors. The same
actual PNT threshold is used at x and (1-kappa)x. Monotonicity of log gives
the lower-end main term at least (1-kappa)x/log x, so a separate true-li
ratio theorem is unnecessary. The coefficient of the final mass is kappa J.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

/-- The upper physical band in the actual source, retaining every label. -/
def p5z_u9_nearTopLabels (kappa : ℝ) (N : ℕ) : Finset P5zU9Triple :=
  (p5z_u9_switchedLabels N).filter fun t =>
    (1 - kappa) * (N : ℝ) < (p5z_u9_product t : ℝ)

/-- Exact prime window for one ORIGINAL pair product. The upper endpoint
is inclusive; this only enlarges the original strict product<N condition. -/
def p5z_u9_physicalPrimeWindow (kappa : ℝ) (N a : ℕ) : Finset ℕ :=
  Nat.primesLE (N / a) \
    Nat.primesLE (Nat.floor ((1 - kappa) * ((N : ℝ) / (a : ℝ))))

def p5z_u9_physicalWindowMass (kappa : ℝ) (N : ℕ) : ℝ :=
  ∑ a ∈ currentChenUpsilon9PrefixProducts N,
    ((p5z_u9_physicalPrimeWindow kappa N a).card : ℝ)

/-- Every near-top original label belongs to the corresponding complete
prime window. In particular q equal to a floor endpoint is handled exactly. -/
theorem p5z_u9_nearTopLabels_subset_primeWindows (kappa : ℝ) (N : ℕ)
    (hk : kappa ≤ 1) :
    p5z_u9_nearTopLabels kappa N ⊆
      (chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
        ((N : ℝ) ^ (59 / 250 : ℝ))).sigma
          (fun p => p5z_u9_physicalPrimeWindow kappa N (p.1 * p.2)) := by
  rintro ⟨p, q⟩ ht
  obtain ⟨ht, htop⟩ := Finset.mem_filter.mp ht
  obtain ⟨hp, hq⟩ := Finset.mem_sigma.mp ht
  obtain ⟨_, hprime, hprod, _, _⟩ := Finset.mem_filter.mp hq
  obtain ⟨h₁, h₂, _⟩ := chenY9PrimeSelector_ordered_prime_data hp
  have ha : 0 < p.1 * p.2 := mul_pos h₁.pos h₂.pos
  have har : (0 : ℝ) < (p.1 * p.2 : ℕ) := by exact_mod_cast ha
  have hlow : (1 - kappa) * ((N : ℝ) / (p.1 * p.2 : ℕ)) < (q : ℝ) := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ har).mpr
    simpa only [p5z_u9_product, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]
      using htop
  refine Finset.mem_sigma.mpr ⟨hp, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
  · apply Nat.mem_primesLE.mpr
    refine ⟨(Nat.le_div_iff_mul_le ha).mpr ?_, hprime⟩
    simpa only [Nat.mul_comm] using hprod.le
  · intro hqfloor
    have hqle := (Nat.mem_primesLE.mp hqfloor).1
    have hnonneg : 0 ≤ (1 - kappa) * ((N : ℝ) / (p.1 * p.2 : ℕ)) :=
      mul_nonneg (sub_nonneg.mpr hk) (div_nonneg (Nat.cast_nonneg _) har.le)
    have hfloor := Nat.floor_le hnonneg
    have hqler : (q : ℝ) ≤
        (Nat.floor ((1 - kappa) * ((N : ℝ) / (p.1 * p.2 : ℕ))) : ℝ) := by
      exact_mod_cast hqle
    exact (not_lt_of_ge (hqler.trans hfloor)) hlow

/-- Pair-product injection is used only for the outer reindexing. Triple
products are never deduplicated. Both the sqrt cutoff and coprime gate
have only been removed in the prime-window MAJORANT. -/
theorem p5z_u9_nearTopLabels_card_le_physicalWindowMass
    (kappa : ℝ) (N : ℕ) (hk : kappa ≤ 1) :
    ((p5z_u9_nearTopLabels kappa N).card : ℝ) ≤
      p5z_u9_physicalWindowMass kappa N := by
  have hcard := Finset.card_le_card
    (p5z_u9_nearTopLabels_subset_primeWindows kappa N hk)
  unfold p5z_u9_physicalWindowMass currentChenUpsilon9PrefixProducts
  rw [Finset.sum_image (chenY9PrimeSelector_multiplier_injOn N _ _)]
  rw [Finset.card_sigma] at hcard
  exact_mod_cast hcard

/-- Exact floor-window cardinality, including its natural subtraction. -/
theorem p5z_u9_physicalPrimeWindow_card (kappa : ℝ) (N a : ℕ)
    (ha : 0 < a) (hk0 : 0 ≤ kappa) (hk1 : kappa ≤ 1) :
    ((p5z_u9_physicalPrimeWindow kappa N a).card : ℝ) =
      (Nat.primeCounting (N / a) : ℝ) -
        (Nat.primeCounting
          (Nat.floor ((1 - kappa) * ((N : ℝ) / (a : ℝ)))) : ℝ) := by
  have hx : 0 ≤ (N : ℝ) / (a : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcx : (1 - kappa) * ((N : ℝ) / (a : ℝ)) ≤ (N : ℝ) / (a : ℝ) := by
    nlinarith only [mul_nonneg hk0 hx]
  have hf := Nat.floor_mono hcx
  rw [halfProduct_nat_floor_div ha] at hf
  unfold p5z_u9_physicalPrimeWindow
  rw [Finset.card_sdiff_of_subset (Nat.primesLE_mono hf)]
  simp only [Nat.primesLE_card_eq_primeCounting]
  exact Nat.cast_sub (Nat.monotone_primeCounting hf)

/-- Genuine uniform two-endpoint PNT. The logarithm at the lower endpoint
is smaller, so its main term is at least (1-kappa)x/log x. This yields the
sharp leading kappa without assuming a boundary density estimate. -/
theorem p5z_u9_exists_physical_primeWindow_threshold
    (kappa : ℝ) (hk0 : 0 < kappa) (hk1 : kappa < 1)
    (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1) :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ (1 - kappa) * x →
      (Nat.primeCounting (Nat.floor x) : ℝ) -
        (Nat.primeCounting (Nat.floor ((1 - kappa) * x)) : ℝ) ≤
          (kappa + 2 * delta) * trueLogarithmicIntegral x := by
  obtain ⟨X, hX2, hX⟩ :=
    exists_primeCounting_real_relative_error_threshold_of_real_pnt
      realHalfProduct_primeCounting_asymptotic_real delta hd
  refine ⟨X, hX2, ?_⟩
  intro x hXcx
  have hc : 0 < 1 - kappa := sub_pos.mpr hk1
  have hcxpos : 0 < (1 - kappa) * x := (by norm_num : (0 : ℝ) < 2).trans_le
    (hX2.trans hXcx)
  have hxpos : 0 < x := by
    rcases mul_pos_iff.mp hcxpos with h | h
    · exact h.2
    · exact ((not_lt_of_ge hc.le) h.1).elim
  have hcxle : (1 - kappa) * x ≤ x := by nlinarith only [mul_nonneg hk0.le hxpos.le]
  have hXx : X ≤ x := hXcx.trans hcxle
  obtain ⟨hlogx, herrx⟩ := hX x hXx
  obtain ⟨hlogcx, herrcx⟩ := hX ((1 - kappa) * x) hXcx
  have hupper := (le_abs_self
    ((Nat.primeCounting (Nat.floor x) : ℝ) - x / Real.log x)).trans herrx
  have hlower := (neg_le_abs
    ((Nat.primeCounting (Nat.floor ((1 - kappa) * x)) : ℝ) -
      ((1 - kappa) * x) / Real.log ((1 - kappa) * x))).trans herrcx
  have hlogle : Real.log ((1 - kappa) * x) ≤ Real.log x :=
    Real.log_le_log hcxpos hcxle
  have hmain : (1 - kappa) * (x / Real.log x) ≤
      ((1 - kappa) * x) / Real.log ((1 - kappa) * x) := by
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_left hcxpos.le hlogcx hlogle
  have hmainlower := mul_le_mul_of_nonneg_left hmain (sub_nonneg.mpr hd1)
  have hnonneg : 0 ≤ x / Real.log x := div_nonneg hxpos.le hlogx.le
  have herror : 0 ≤ delta * kappa * (x / Real.log x) :=
    mul_nonneg (mul_nonneg hd.le hk0.le) hnonneg
  have hwindow : (Nat.primeCounting (Nat.floor x) : ℝ) -
      (Nat.primeCounting (Nat.floor ((1 - kappa) * x)) : ℝ) ≤
        (kappa + 2 * delta) * (x / Real.log x) := by
    nlinarith only [hupper, hlower, hmainlower, herror]
  exact hwindow.trans (mul_le_mul_of_nonneg_left
    (div_log_le_liuLogarithmicIntegral (hX2.trans hXx))
      (by positivity : 0 ≤ kappa + 2 * delta))

/-- A single N-threshold controls EVERY original pair window. The actual
quotients are all at least N^(191/500), and their lower endpoints have the
same fixed positive linear factor 1-kappa. -/
theorem p5z_eventually_u9_physicalWindowMass_le_trueLiMass
    (kappa : ℝ) (hk0 : 0 < kappa) (hk1 : kappa < 1)
    (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1) :
    ∀ᶠ N : ℕ in atTop, p5z_u9_physicalWindowMass kappa N ≤
      (kappa + 2 * delta) * currentChenUpsilon9LiMainMass N := by
  obtain ⟨X, hX2, hX⟩ :=
    p5z_u9_exists_physical_primeWindow_threshold kappa hk0 hk1 delta hd hd1
  have hc : 0 < 1 - kappa := sub_pos.mpr hk1
  have hlarge : ∀ᶠ N : ℕ in atTop,
      X / (1 - kappa) ≤ (N : ℝ) ^ (191 / 500 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 191 / 500)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with N hlargeN hN
  unfold p5z_u9_physicalWindowMass currentChenUpsilon9LiMainMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have haPos := (currentChenUpsilon9PrefixProducts_data ha).1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have harg := currentChenUpsilon9_li_argument_power_lower hNr ha
  have hXarg : X ≤ (1 - kappa) * ((N : ℝ) / (a : ℝ)) := by
    have h := (div_le_iff₀ hc).mp (hlargeN.trans harg)
    simpa only [mul_comm] using h
  rw [p5z_u9_physicalPrimeWindow_card kappa N a haPos hk0.le hk1.le]
  have h := hX ((N : ℝ) / (a : ℝ)) hXarg
  rw [halfProduct_nat_floor_div haPos] at h
  exact h

/-- The genuine physical boundary estimate at the literal harmonic
integral. There is no assumed arithmetic boundary supplier in this theorem. -/
theorem p5z_eventually_u9_nearTopLabels_mass_le_harmonicIntegral
    (kappa : ℝ) (hk0 : 0 < kappa) (hk1 : kappa < 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      ((p5z_u9_nearTopLabels kappa N).card : ℝ) ≤
        (kappa * currentChenUpsilon9HarmonicIntegral + eta) *
          ((N : ℝ) / Real.log (N : ℝ)) := by
  let J := currentChenUpsilon9HarmonicIntegral
  have hJ : 0 ≤ J := p5z_u9_HarmonicIntegral_nonneg
  let D := 11 * (J + 1)
  have hD : 0 < D := by dsimp [D]; linarith only [hJ]
  let delta := min 1 (eta / D)
  have hd : 0 < delta := lt_min zero_lt_one (div_pos heta hD)
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hbudget : delta * D ≤ eta := (le_div_iff₀ hD).mp (min_le_right _ _)
  have hsquare : delta * delta ≤ delta := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1 hd.le
  have hkdelta : kappa * delta ≤ delta := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hk1.le hd.le
  have hfactor : (kappa + 2 * delta) * (1 + delta) ≤ kappa + 5 * delta := by
    nlinarith only [hsquare, hkdelta]
  have hfactorJ := mul_le_mul_of_nonneg_right hfactor (add_nonneg hJ hd.le)
  have hcoefficient : (kappa + 2 * delta) * (1 + delta) * (J + delta) ≤
      kappa * J + eta := by
    dsimp [D] at hbudget
    nlinarith only [hfactorJ, hsquare, hkdelta, hbudget, mul_nonneg hJ hd.le, hd]
  have hnear : ∀ᶠ N : ℕ in atTop, currentChenUpsilon9LogTotientMass N ≤ J + delta :=
    (tendsto_currentChenUpsilon9LogTotientMass.eventually
      (eventually_lt_nhds (lt_add_of_pos_right J hd))).mono (fun _ h => h.le)
  filter_upwards [p5z_eventually_u9_physicalWindowMass_le_trueLiMass
      kappa hk0 hk1 delta hd hd1,
    eventually_currentChenUpsilon9_liMainMass_le_logTotientMass delta hd,
    hnear, eventually_ge_atTop (2 : ℕ)] with N hwindow hli hnearN hN
  have hsource := (p5z_u9_nearTopLabels_card_le_physicalWindowMass kappa N hk1.le).trans hwindow
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hlog := Real.log_pos hNr
  have h1 : ((p5z_u9_nearTopLabels kappa N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ) ≤
      (kappa + 2 * delta) *
        (currentChenUpsilon9LiMainMass N * Real.log (N : ℝ) / (N : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hsource (div_nonneg hlog.le hNp.le)
    convert h using 1 <;> ring
  have h2 := mul_le_mul_of_nonneg_left hli
    (by positivity : 0 ≤ kappa + 2 * delta)
  have hnormalized : ((p5z_u9_nearTopLabels kappa N).card : ℝ) *
      Real.log (N : ℝ) / (N : ℝ) ≤ kappa * J + eta := by
    calc
      _ ≤ (kappa + 2 * delta) * ((1 + delta) * currentChenUpsilon9LogTotientMass N) :=
        h1.trans h2
      _ = ((kappa + 2 * delta) * (1 + delta)) * currentChenUpsilon9LogTotientMass N := by ring
      _ ≤ ((kappa + 2 * delta) * (1 + delta)) * (J + delta) :=
        mul_le_mul_of_nonneg_left hnearN (by positivity)
      _ ≤ kappa * J + eta := hcoefficient
  have hraw := (div_le_iff₀ hNp).mp hnormalized
  calc
    ((p5z_u9_nearTopLabels kappa N).card : ℝ) ≤
        ((kappa * J + eta) * (N : ℝ)) / Real.log (N : ℝ) :=
      (le_div_iff₀ hlog).mpr hraw
    _ = (kappa * currentChenUpsilon9HarmonicIntegral + eta) *
        ((N : ℝ) / Real.log (N : ℝ)) := by dsimp [J]; ring

/-- Exact pushforward of the physical band to the actual product-fibre
weight. Products with several labels retain that multiplicity. -/
theorem p5z_u9_nearTopWeight_mass_eq_card (kappa : ℝ) (N : ℕ) :
    (∑ m ∈ Finset.range N, p5z_u9_switchedWeight N m *
      (if (1 - kappa) * (N : ℝ) < (m : ℝ) then 1 else 0)) =
        ((p5z_u9_nearTopLabels kappa N).card : ℝ) := by
  rw [p5z_u9_switchedWeight_sum]
  rw [← Finset.sum_filter]
  simp [p5z_u9_nearTopLabels]

/-- The same unconditional physical estimate at the ORIGINAL multiplicity
weight, ready for a cutoff on m/N. -/
theorem p5z_eventually_u9_nearTopWeight_mass_le_harmonicIntegral
    (kappa : ℝ) (hk0 : 0 < kappa) (hk1 : kappa < 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      (∑ m ∈ Finset.range N, p5z_u9_switchedWeight N m *
        (if (1 - kappa) * (N : ℝ) < (m : ℝ) then 1 else 0)) ≤
          (kappa * currentChenUpsilon9HarmonicIntegral + eta) *
            ((N : ℝ) / Real.log (N : ℝ)) := by
  simpa only [p5z_u9_nearTopWeight_mass_eq_card] using
    p5z_eventually_u9_nearTopLabels_mass_le_harmonicIntegral kappa hk0 hk1 eta heta

/-- A cutoff equal to one below (1-kappa)N loses at most the actual band
mass. No regularity of the cutoff and no prime-receiver gate is assumed.
The unused upper bound chi<=1 is unnecessary for this one-sided inequality. -/
theorem p5z_u9_physicalSmoothingLoss_le_nearTopLabels
    (kappa : ℝ) (N : ℕ) (chi : ℕ → ℝ)
    (hchi0 : ∀ m < N, 0 ≤ chi m)
    (hchiOne : ∀ m < N, (m : ℝ) ≤ (1 - kappa) * (N : ℝ) → chi m = 1) :
    (∑ m ∈ Finset.range N, p5z_u9_switchedWeight N m * (1 - chi m)) ≤
      ((p5z_u9_nearTopLabels kappa N).card : ℝ) := by
  rw [p5z_u9_switchedWeight_sum]
  calc
    (∑ t ∈ p5z_u9_switchedLabels N, 1 - chi (p5z_u9_product t)) ≤
        ∑ t ∈ p5z_u9_switchedLabels N,
          if (1 - kappa) * (N : ℝ) < (p5z_u9_product t : ℝ) then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro t ht
      have hm := p5z_u9_switchedLabels_product_lt ht
      by_cases htop : (1 - kappa) * (N : ℝ) < (p5z_u9_product t : ℝ)
      · rw [if_pos htop]
        linarith only [hchi0 (p5z_u9_product t) hm]
      · rw [if_neg htop, hchiOne (p5z_u9_product t) hm (le_of_not_gt htop)]
        norm_num
    _ = ((p5z_u9_nearTopLabels kappa N).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [p5z_u9_nearTopLabels]

/-- Uniformity in the smoothing function: it is chosen AFTER N and need
only satisfy the stated actual physical support conditions. -/
theorem p5z_eventually_u9_physicalSmoothingLoss_le_harmonicIntegral
    (kappa : ℝ) (hk0 : 0 < kappa) (hk1 : kappa < 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ chi : ℕ → ℝ,
      (∀ m < N, 0 ≤ chi m) →
      (∀ m < N, (m : ℝ) ≤ (1 - kappa) * (N : ℝ) → chi m = 1) →
      (∑ m ∈ Finset.range N, p5z_u9_switchedWeight N m * (1 - chi m)) ≤
        (kappa * currentChenUpsilon9HarmonicIntegral + eta) *
          ((N : ℝ) / Real.log (N : ℝ)) := by
  filter_upwards [p5z_eventually_u9_nearTopLabels_mass_le_harmonicIntegral
    kappa hk0 hk1 eta heta] with N hN
  intro chi hchi0 hchiOne
  exact (p5z_u9_physicalSmoothingLoss_le_nearTopLabels
    kappa N chi hchi0 hchiOne).trans hN

/-- The finite loss is exactly the difference between the full original
source mass and its smoothed mass. -/
theorem p5z_u9_physicalSmoothingLoss_eq_mass_sub (N : ℕ) (chi : ℕ → ℝ) :
    (∑ m ∈ Finset.range N, p5z_u9_switchedWeight N m * (1 - chi m)) =
      p5z_labelledMass (Finset.range N) (p5z_u9_switchedWeight N) -
        ∑ m ∈ Finset.range N, p5z_u9_switchedWeight N m * chi m := by
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, p5z_labelledMass]

/-- For a cutoff between zero and one the difference is nonnegative, so
the same physical estimate bounds its absolute value. -/
theorem p5z_eventually_u9_physicalSmoothedMass_abs_sub_le
    (kappa : ℝ) (hk0 : 0 < kappa) (hk1 : kappa < 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ chi : ℕ → ℝ,
      (∀ m < N, 0 ≤ chi m ∧ chi m ≤ 1) →
      (∀ m < N, (m : ℝ) ≤ (1 - kappa) * (N : ℝ) → chi m = 1) →
      |p5z_labelledMass (Finset.range N) (p5z_u9_switchedWeight N) -
        ∑ m ∈ Finset.range N, p5z_u9_switchedWeight N m * chi m| ≤
          (kappa * currentChenUpsilon9HarmonicIntegral + eta) *
            ((N : ℝ) / Real.log (N : ℝ)) := by
  filter_upwards [p5z_eventually_u9_physicalSmoothingLoss_le_harmonicIntegral
    kappa hk0 hk1 eta heta] with N hN
  intro chi hchi hchiOne
  rw [← p5z_u9_physicalSmoothingLoss_eq_mass_sub]
  have hnonneg : 0 ≤
      ∑ m ∈ Finset.range N, p5z_u9_switchedWeight N m * (1 - chi m) := by
    apply Finset.sum_nonneg
    intro m hm
    exact mul_nonneg (p5z_u9_switchedWeight_nonneg N m)
      (sub_nonneg.mpr (hchi m (Finset.mem_range.mp hm)).2)
  rw [abs_of_nonneg hnonneg]
  exact hN chi (fun m hm => (hchi m hm).1) hchiOne

/-- The physical width can be chosen to pay any prescribed SOURCE-scale
budget. The threshold is chosen after the fixed width, uniformly in chi. -/
theorem p5z_u9_exists_physicalSmoothingWidth
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ kappa : ℝ, 0 < kappa ∧ kappa < 1 / 2 ∧
      ∀ᶠ N : ℕ in atTop, ∀ chi : ℕ → ℝ,
        (∀ m < N, 0 ≤ chi m) →
        (∀ m < N, (m : ℝ) ≤ (1 - kappa) * (N : ℝ) → chi m = 1) →
        (∑ m ∈ Finset.range N, p5z_u9_switchedWeight N m * (1 - chi m)) ≤
          epsilon * ((N : ℝ) / Real.log (N : ℝ)) := by
  let J := currentChenUpsilon9HarmonicIntegral
  have hJ : 0 ≤ J := p5z_u9_HarmonicIntegral_nonneg
  let D := 4 * (J + 1)
  have hD : 0 < D := by dsimp [D]; linarith only [hJ]
  let kappa := min (1 / 4 : ℝ) (epsilon / D)
  have hk0 : 0 < kappa := lt_min (by norm_num) (div_pos hepsilon hD)
  have hkquarter : kappa ≤ 1 / 4 := min_le_left _ _
  have hkhalf : kappa < 1 / 2 := by linarith only [hkquarter]
  have hk1 : kappa < 1 := by linarith only [hkhalf]
  have hbudget : kappa * D ≤ epsilon := (le_div_iff₀ hD).mp (min_le_right _ _)
  have hcoefficient : kappa * J + epsilon / 2 ≤ epsilon := by
    dsimp [D] at hbudget
    nlinarith only [hbudget, hk0, hepsilon, mul_nonneg hk0.le hJ]
  refine ⟨kappa, hk0, hkhalf, ?_⟩
  filter_upwards [p5z_eventually_u9_physicalSmoothingLoss_le_harmonicIntegral
      kappa hk0 hk1 (epsilon / 2) (half_pos hepsilon),
    eventually_ge_atTop (2 : ℕ)] with N hN hN2
  intro chi hchi0 hchiOne
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 ≤ (N : ℝ) / Real.log (N : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Real.log_pos hNr).le
  exact (hN chi hchi0 hchiOne).trans
    (mul_le_mul_of_nonneg_right hcoefficient hscale)

end

end ImbalancedChen
