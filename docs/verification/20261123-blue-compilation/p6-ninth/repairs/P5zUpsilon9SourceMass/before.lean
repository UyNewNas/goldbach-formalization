import ImbalancedChen.P5zUpsilon9SwitchedMultiplicity
import ImbalancedChen.CurrentChenUpsilon9HarmonicMean
import ImbalancedChen.RealHalfProductMassSuppliers
import ImbalancedChen.UniformPrimeTail
import ImbalancedChen.HalfProductMassLimit

/-!
# Unconditional source-mass supplier for the actual ninth triple weight

SOURCE ONLY / UNCOMPILED. The source contains NO Prime(N-product) gate.
Its centre-coprime restriction and moving quotient lower cutoff can be
removed for an upper mass bound. Pair-product injection is already proved;
no triple-product injection is assumed. Every third-prime label is counted.

The actual PNT, true-li leading-one transport, and actual harmonic integral
limit supply the result; there is no assumed desired source-mass estimate.
This is the N/log N SOURCE scale, not the count scale H(N).
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology Asymptotics
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

/-- Literal complete prime-prefix mass over the ORIGINAL pair-product
support. The quotient cutoff and centre-coprime mask are relaxed only for
this upper bound; the summation over pair products uses proved injection. -/
def p5z_u9_primeCountMass (N : ℕ) : ℝ :=
  ∑ a ∈ currentChenUpsilon9PrefixProducts N, (Nat.primeCounting (N / a) : ℝ)

/-- Every original labelled row injects into its full prime prefix.
The triple-product map need not be injective, and is not used as if it were. -/
theorem p5z_u9_switchedLabels_card_le_primeCountMass (N : ℕ) :
    ((p5z_u9_switchedLabels N).card : ℝ) ≤ p5z_u9_primeCountMass N := by
  unfold p5z_u9_primeCountMass currentChenUpsilon9PrefixProducts
  rw [Finset.sum_image (chenY9PrimeSelector_multiplier_injOn N _ _)]
  unfold p5z_u9_switchedLabels
  rw [Finset.card_sigma, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hb : 0 < p.1 * p.2 := by
    obtain ⟨h₁, h₂, _⟩ := chenY9PrimeSelector_ordered_prime_data hp
    exact mul_pos h₁.pos h₂.pos
  have hsub : ((Finset.range (N + 1)).filter fun q => Nat.Prime q ∧
      p.1 * p.2 * q < N ∧
      Real.sqrt ((N : ℝ) / ((p.1 : ℝ) * (p.2 : ℝ))) ≤ (q : ℝ) ∧
      Nat.Coprime (N - p.1 * p.2 * q) N) ⊆ Nat.primesLE (N / (p.1 * p.2)) := by
    intro q hq
    obtain ⟨_, hprime, hprod, _, _⟩ := Finset.mem_filter.mp hq
    apply Nat.mem_primesLE.mpr
    refine ⟨(Nat.le_div_iff_mul_le hb).mpr ?_, hprime⟩
    simpa only [Nat.mul_comm] using hprod.le
  exact_mod_cast (Finset.card_le_card hsub).trans_eq
    (Nat.primesLE_card_eq_primeCounting (N / (p.1 * p.2)))

/-- PNT gives a SINGLE threshold for every moving actual product argument.
The real division endpoint is converted to its exact natural floor, with
no discarded rounding error. The true-li lower bound has no PNT premise. -/
theorem p5z_eventually_u9_primeCounting_le_trueLi
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, ∀ a ∈ currentChenUpsilon9PrefixProducts N,
      (Nat.primeCounting (N / a) : ℝ) ≤
        (1 + delta) * trueLogarithmicIntegral ((N : ℝ) / (a : ℝ)) := by
  obtain ⟨X, hX2, hX⟩ :=
    exists_primeCounting_real_relative_error_threshold_of_real_pnt
      realHalfProduct_primeCounting_asymptotic_real delta hdelta
  have hlarge : ∀ᶠ N : ℕ in atTop, X ≤ (N : ℝ) ^ (191 / 500 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 191 / 500)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop X)
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with N hlargeN hN
  intro a ha
  have haPos := (currentChenUpsilon9PrefixProducts_data ha).1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have harg := currentChenUpsilon9_li_argument_power_lower hNr ha
  have hXarg : X ≤ (N : ℝ) / (a : ℝ) := hlargeN.trans harg
  have hx2 : 2 ≤ (N : ℝ) / (a : ℝ) := hX2.trans hXarg
  obtain ⟨hlog, herr⟩ := hX ((N : ℝ) / (a : ℝ)) hXarg
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

/-- Finite summation of the genuine uniform PNT estimate preserves all
actual pair products and bounds the source by its literal true-li mass. -/
theorem p5z_eventually_u9_switchedLabels_card_le_trueLiMass
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop,
      ((p5z_u9_switchedLabels N).card : ℝ) ≤
        (1 + delta) * currentChenUpsilon9LiMainMass N := by
  filter_upwards [p5z_eventually_u9_primeCounting_le_trueLi delta hdelta] with N hN
  apply (p5z_u9_switchedLabels_card_le_primeCountMass N).trans
  change (∑ a ∈ currentChenUpsilon9PrefixProducts N, (Nat.primeCounting (N / a) : ℝ)) ≤
    (1 + delta) * ∑ a ∈ currentChenUpsilon9PrefixProducts N,
      trueLogarithmicIntegral ((N : ℝ) / (a : ℝ))
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun a ha => hN a ha)

/-- Positivity of the actual harmonic integral follows from the already
proved nonnegative arithmetic harmonic sums and their genuine limit. -/
theorem p5z_u9_HarmonicIntegral_nonneg : 0 ≤ currentChenUpsilon9HarmonicIntegral := by
  by_contra hnot
  have hneg : currentChenUpsilon9HarmonicIntegral < 0 := lt_of_not_ge hnot
  have hnegative : ∀ᶠ N : ℕ in atTop, currentChenUpsilon9LogTotientMass N < 0 :=
    tendsto_currentChenUpsilon9LogTotientMass.eventually (eventually_lt_nhds hneg)
  obtain ⟨N, hNneg, hN2⟩ := (hnegative.and (eventually_ge_atTop (2 : ℕ))).exists
  exact (not_lt_of_ge (currentChenUpsilon9LogTotientMass_nonneg hN2)) hNneg

/-- Unconditional source mass at the LITERAL actual harmonic integral.
No count-scale error payment or adopted K mean occurs. In particular this
is a concrete source-mass supplier for the positive-family U* bridge. -/
theorem p5z_eventually_u9_switchedLabels_mass_le_harmonicIntegral
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      ((p5z_u9_switchedLabels N).card : ℝ) ≤
        (currentChenUpsilon9HarmonicIntegral + eta) * ((N : ℝ) / Real.log (N : ℝ)) := by
  let J := currentChenUpsilon9HarmonicIntegral
  have hJ : 0 ≤ J := p5z_u9_HarmonicIntegral_nonneg
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
  have hnear : ∀ᶠ N : ℕ in atTop, currentChenUpsilon9LogTotientMass N ≤ J + delta :=
    (tendsto_currentChenUpsilon9LogTotientMass.eventually
      (eventually_lt_nhds (lt_add_of_pos_right J hd))).mono (fun _ h => h.le)
  filter_upwards [p5z_eventually_u9_switchedLabels_card_le_trueLiMass delta hd,
    eventually_currentChenUpsilon9_liMainMass_le_logTotientMass delta hd,
    hnear, eventually_ge_atTop (2 : ℕ)] with N hsource hli hnearN hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hlog := Real.log_pos hNr
  have h1 : ((p5z_u9_switchedLabels N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ) ≤
      (1 + delta) * (currentChenUpsilon9LiMainMass N * Real.log (N : ℝ) / (N : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hsource (div_nonneg hlog.le hNp.le)
    convert h using 1 <;> ring
  have h2 := mul_le_mul_of_nonneg_left hli (by linarith only [hd] : 0 ≤ 1 + delta)
  have hnormalized : ((p5z_u9_switchedLabels N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ) ≤
      J + eta := by
    calc
      _ ≤ (1 + delta) * ((1 + delta) * currentChenUpsilon9LogTotientMass N) := h1.trans h2
      _ = (1 + delta) ^ 2 * currentChenUpsilon9LogTotientMass N := by ring
      _ ≤ (1 + delta) ^ 2 * (J + delta) :=
        mul_le_mul_of_nonneg_left hnearN (sq_nonneg _)
      _ ≤ J + eta := hcoefficient
  have hraw := (div_le_iff₀ hNp).mp hnormalized
  calc
    ((p5z_u9_switchedLabels N).card : ℝ) ≤ ((J + eta) * (N : ℝ)) / Real.log (N : ℝ) :=
      (le_div_iff₀ hlog).mpr hraw
    _ = (currentChenUpsilon9HarmonicIntegral + eta) *
        ((N : ℝ) / Real.log (N : ℝ)) := by dsimp [J]; ring

/-- The same unconditional supplier at the actual product-fibre weight. -/
theorem p5z_eventually_u9_switchedWeight_mass_le_harmonicIntegral
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      p5z_labelledMass (Finset.range N) (p5z_u9_switchedWeight N) ≤
        (currentChenUpsilon9HarmonicIntegral + eta) * ((N : ℝ) / Real.log (N : ℝ)) := by
  simpa only [p5z_u9_switchedMass_eq_card] using
    p5z_eventually_u9_switchedLabels_mass_le_harmonicIntegral eta heta

end

end ImbalancedChen
