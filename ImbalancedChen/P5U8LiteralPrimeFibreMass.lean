import ImbalancedChen.CurrentChenUpsilon8HarmonicMean
import ImbalancedChen.RealHalfProductMassSuppliers
import ImbalancedChen.UniformPrimeTail
import ImbalancedChen.HalfProductMassLimit

/-!
SOURCE_ONLY / UNCOMPILED. Unconditional original U8 prime-prefix source mass.
This is the N/logN source scale. The actual arithmetic pair carrier, inclusive
second-prime wall and moving sqrt upper wall are retained. A source's q>=p2
and centre-coprime product gates may only be relaxed for this upper bound.
Prime(N-product) never appears. No ordinary U8 count mean or sharpK source
distribution theorem is asserted or assumed.
-/

namespace ImbalancedChen.P5U8LiteralPrimeFibreMassSourceOnly

noncomputable section

open Filter Topology Asymptotics
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

def primeCountMass (N : ℕ) : ℝ :=
  ∑ a ∈ currentChenUpsilon8PrefixProducts N, (Nat.primeCounting (N / a) : ℝ)

/-- Every literal q fibre injects into its prime prefix. The finite premise
is only the true source membership data prime(q) and p1*p2*q<N; it is not
a source-mass estimate. No triple-product injectivity is assumed. -/
theorem rowCards_le_primeCountMass (N : ℕ) (F : (ℕ × ℕ) → Finset ℕ)
    (hF : ∀ t ∈ chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)), ∀ q ∈ F t, Nat.Prime q ∧ t.1 * t.2 * q < N) :
    (∑ t ∈ chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)), ((F t).card : ℝ)) ≤ primeCountMass N := by
  unfold primeCountMass currentChenUpsilon8PrefixProducts
  rw [Finset.sum_image (chenY8PrimeSelector_multiplier_injOn N _ _)]
  apply Finset.sum_le_sum
  intro t ht
  obtain ⟨hc, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc₁, hc₂⟩ := Finset.mem_product.mp hc
  have hb : 0 < t.1 * t.2 := mul_pos
    (mem_chenAdditivePrimeCarrier.mp hc₁).2.1.pos
    (mem_chenAdditivePrimeCarrier.mp hc₂).2.1.pos
  have hsub : F t ⊆ Nat.primesLE (N / (t.1 * t.2)) := by
    intro q hq
    obtain ⟨hprime, hprod⟩ := hF t ht q hq
    apply Nat.mem_primesLE.mpr
    refine ⟨(Nat.le_div_iff_mul_le hb).mpr ?_, hprime⟩
    simpa only [Nat.mul_comm] using hprod.le
  exact_mod_cast (Finset.card_le_card hsub).trans_eq
    (Nat.primesLE_card_eq_primeCounting (N / (t.1 * t.2)))

/-- One PNT threshold serves all actual moving quotient arguments. The
natural floor division is exact; no endpoint error is discarded. -/
theorem eventually_primeCounting_le_trueLi (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, ∀ a ∈ currentChenUpsilon8PrefixProducts N,
      (Nat.primeCounting (N / a) : ℝ) ≤
        (1 + delta) * trueLogarithmicIntegral ((N : ℝ) / (a : ℝ)) := by
  obtain ⟨X, hX2, hX⟩ :=
    exists_primeCounting_real_relative_error_threshold_of_real_pnt
      realHalfProduct_primeCounting_asymptotic_real delta hdelta
  have hlarge : ∀ᶠ N : ℕ in atTop, X ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop X)
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with N hlargeN hN
  intro a ha
  have haPos := (currentChenUpsilon8PrefixProducts_data ha).1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have harg := currentChenUpsilon8_li_argument_power_lower hNr ha
  have hXarg : X ≤ (N : ℝ) / (a : ℝ) := hlargeN.trans harg
  have hx2 : 2 ≤ (N : ℝ) / (a : ℝ) := hX2.trans hXarg
  obtain ⟨_hlog, herr⟩ := hX ((N : ℝ) / (a : ℝ)) hXarg
  rw [halfProduct_nat_floor_div haPos] at herr
  have hupper := (le_abs_self
    ((Nat.primeCounting (N / a) : ℝ) -
      ((N : ℝ) / (a : ℝ)) / Real.log ((N : ℝ) / (a : ℝ)))).trans herr
  have hLi : ((N : ℝ) / (a : ℝ)) / Real.log ((N : ℝ) / (a : ℝ)) ≤
      trueLogarithmicIntegral ((N : ℝ) / (a : ℝ)) :=
    div_log_le_liuLogarithmicIntegral hx2
  calc
    (Nat.primeCounting (N / a) : ℝ) ≤
        (1 + delta) * (((N : ℝ) / (a : ℝ)) /
          Real.log ((N : ℝ) / (a : ℝ))) := by linarith only [hupper]
    _ ≤ _ := mul_le_mul_of_nonneg_left hLi (by linarith only [hdelta])

theorem eventually_primeCountMass_le_trueLiMass (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop,
      primeCountMass N ≤ (1 + delta) * currentChenUpsilon8LiMainMass N := by
  filter_upwards [eventually_primeCounting_le_trueLi delta hdelta] with N hN
  unfold primeCountMass currentChenUpsilon8LiMainMass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun a ha => hN a ha)

/-- Nonnegativity of the literal actual double harmonic integral follows
from its genuine arithmetic limit, with no numerical integral premise. -/
theorem harmonicIntegral_nonneg : 0 ≤ currentChenUpsilon8HarmonicIntegral := by
  by_contra hnot
  have hneg : currentChenUpsilon8HarmonicIntegral < 0 := lt_of_not_ge hnot
  have hnegative : ∀ᶠ N : ℕ in atTop, currentChenUpsilon8LogTotientMass N < 0 :=
    tendsto_currentChenUpsilon8LogTotientMass.eventually (eventually_lt_nhds hneg)
  obtain ⟨N, hNneg, hN2⟩ := (hnegative.and (eventually_ge_atTop (2 : ℕ))).exists
  exact (not_lt_of_ge (currentChenUpsilon8LogTotientMass_nonneg hN2)) hNneg

/-- Unconditional original U8 prime-prefix mass supplier at its actual
literal double integral, retaining coefficient one and the source scale. -/
theorem eventually_primeCountMass_le_harmonicIntegral (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      primeCountMass N ≤ (currentChenUpsilon8HarmonicIntegral + eta) *
        ((N : ℝ) / Real.log (N : ℝ)) := by
  let J := currentChenUpsilon8HarmonicIntegral
  have hJ : 0 ≤ J := harmonicIntegral_nonneg
  let D := 7 * (J + 1)
  have hD : 0 < D := by dsimp [D]; linarith only [hJ]
  let delta := min 1 (eta / D)
  have hd : 0 < delta := lt_min zero_lt_one (div_pos heta hD)
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hbudget : delta * D ≤ eta := (le_div_iff₀ hD).mp (min_le_right _ _)
  have hsquare : delta * delta ≤ delta := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1 hd.le
  have hquad : (1 + delta) ^ 2 ≤ 1 + 3 * delta := by nlinarith only [hsquare]
  have hquadJ := mul_le_mul_of_nonneg_right hquad (add_nonneg hJ hd.le)
  have hJdelta := mul_nonneg hJ hd.le
  have hcoefficient : (1 + delta) ^ 2 * (J + delta) ≤ J + eta := by
    dsimp [D] at hbudget
    nlinarith only [hbudget, hsquare, hquadJ, hJdelta, hd]
  have hnear : ∀ᶠ N : ℕ in atTop, currentChenUpsilon8LogTotientMass N ≤ J + delta :=
    (tendsto_currentChenUpsilon8LogTotientMass.eventually
      (eventually_lt_nhds (lt_add_of_pos_right J hd))).mono (fun _ h => h.le)
  filter_upwards [eventually_primeCountMass_le_trueLiMass delta hd,
    eventually_currentChenUpsilon8_liMainMass_le_logTotientMass delta hd,
    hnear, eventually_ge_atTop (2 : ℕ)] with N hsource hli hnearN hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 ≤ (N : ℝ) / Real.log (N : ℝ) :=
    div_nonneg (Nat.cast_nonneg N) (Real.log_pos hNr).le
  have h1d : 0 ≤ 1 + delta := by linarith only [hd]
  calc
    primeCountMass N ≤ (1 + delta) * currentChenUpsilon8LiMainMass N := hsource
    _ ≤ (1 + delta) * ((1 + delta) * ((N : ℝ) / Real.log (N : ℝ)) *
        currentChenUpsilon8LogTotientMass N) := mul_le_mul_of_nonneg_left hli h1d
    _ = ((1 + delta) ^ 2 * currentChenUpsilon8LogTotientMass N) *
        ((N : ℝ) / Real.log (N : ℝ)) := by ring
    _ ≤ ((1 + delta) ^ 2 * (J + delta)) * ((N : ℝ) / Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnearN (sq_nonneg _)) hscale
    _ ≤ (J + eta) * ((N : ℝ) / Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoefficient hscale
    _ = _ := by rfl

/-- Any literal arithmetic row source with its actual finite membership
data receives the same unconditional supplier, uniformly before all rows. -/
theorem eventually_rowCards_le_harmonicIntegral
    (F : ℕ → (ℕ × ℕ) → Finset ℕ)
    (hF : ∀ N, ∀ t ∈ chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)), ∀ q ∈ F N t, Nat.Prime q ∧ t.1 * t.2 * q < N)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      (∑ t ∈ chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)), ((F N t).card : ℝ)) ≤
        (currentChenUpsilon8HarmonicIntegral + eta) * ((N : ℝ) / Real.log (N : ℝ)) := by
  filter_upwards [eventually_primeCountMass_le_harmonicIntegral eta heta] with N hN
  exact (rowCards_le_primeCountMass N (F N) (hF N)).trans hN

end

end ImbalancedChen.P5U8LiteralPrimeFibreMassSourceOnly
