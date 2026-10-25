import ImbalancedChen.P5U7OriginalBoundaryMass

/-!
Actual original U7 summed rough-band error, source only / uncompiled.
The import is the preceding exclusive draft's proposed installed path.

The selector is s>=1+eta, equivalently t+(2+eta)*u<=1. It is NOT an
additive-intercept collar. The exact native band error is
  C3 * (R(z)*(x/log z) + z/log z), x=N/(p1*p2), z=p2.
The second term is paid row by row using z<=N^(-d*eta)*x, d=59/250.
Thus no additional natural-number power sum or prime test transport is
needed. Every actual marked prime pair remains in the finite sums.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology Set MeasureTheory LiLiuPrereqBuchstab
open scoped BigOperators
open Classical

def p5U7InteriorPairs (N : ℕ) (eta : ℝ) : Finset (ℕ × ℕ) :=
  (chenY7PrimeSelector N ((N : ℝ)^(59/250 : ℝ))).filter fun t =>
    (1+eta)*Real.log (t.2 : ℝ) ≤
      Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))

def p5U7InteriorBandRowError (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  buchstabBandConstant 3 *
    (buchstabRemainder (t.2 : ℝ) *
      (((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ)) +
      (t.2 : ℝ)/Real.log (t.2 : ℝ))

def p5U7InteriorBandError (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7InteriorPairs N eta, p5U7InteriorBandRowError N t

def p5U7InteriorBandMain (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7InteriorPairs N eta,
    let x := (N : ℝ)/((t.1*t.2 : ℕ) : ℝ)
    x * buchstab (Real.log x/Real.log (t.2 : ℝ))/Real.log (t.2 : ℝ)

def p5U7InteriorRoughMass (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7InteriorPairs N eta,
    (roughCount ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ)

def p5U7InteriorErrorCoefficient (N : ℕ) (eta : ℝ) : ℝ :=
  buchstabBandConstant 3 *
    (buchstabRemainder ((N : ℝ)^(59/250 : ℝ)) +
      (N : ℝ)^(-(59/250 : ℝ)*eta)) * (6250/59 : ℝ)

theorem p5U7Interior_gate_iff_argument {N : ℕ} {t : ℕ × ℕ} (eta : ℝ)
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ)^(59/250 : ℝ))) :
    t ∈ p5U7InteriorPairs N eta ↔
      1+eta ≤ Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ) := by
  have hc := (Finset.mem_filter.mp ht).1
  have hp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).2).2.1
  have hlog := Real.log_pos (show (1 : ℝ)<t.2 by exact_mod_cast hp.one_lt)
  simp only [p5U7InteriorPairs,Finset.mem_filter,ht,true_and]
  exact (le_div_iff₀ hlog).symm

/-- Literal interior power wall; this is the multiplicative eta domain. -/
theorem p5U7Interior_power_wall {N : ℕ} {eta : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ p5U7InteriorPairs N eta) :
    (t.2 : ℝ)^(1+eta) ≤ (N : ℝ)/((t.1*t.2 : ℕ) : ℝ) ∧
      (t.1 : ℝ)*(t.2 : ℝ)^(2+eta) ≤ (N : ℝ) := by
  obtain ⟨hto,hgate⟩ := Finset.mem_filter.mp ht
  have hc := (Finset.mem_filter.mp hto).1
  have hp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).1).2.1
  have hq := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).2).2.1
  have hpR : (0 : ℝ)<t.1 := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ)<t.2 := by exact_mod_cast hq.pos
  have hg := p5U7Mass_outer_geometry hto
  have hbR : (0 : ℝ)<((t.1*t.2 : ℕ) : ℝ) := by exact_mod_cast hg.1
  have hxR : (0 : ℝ)<(N : ℝ)/((t.1*t.2 : ℕ) : ℝ) := hqR.trans hg.2.2.1
  have hpower := (Real.rpow_le_iff_le_log hqR hxR).mpr hgate
  refine ⟨hpower,?_⟩
  have hmul := (le_div_iff₀ hbR).mp hpower
  have hidentity : (t.2 : ℝ)^(1+eta)*((t.1*t.2 : ℕ) : ℝ) =
      (t.1 : ℝ)*(t.2 : ℝ)^(2+eta) := by
    rw [Nat.cast_mul]
    calc
      _ = (t.1 : ℝ)*((t.2 : ℝ)^(1+eta)*(t.2 : ℝ)^1) := by rw [Real.rpow_one]; ring
      _ = _ := by
        rw [← Real.rpow_add hqR]
        congr 1 <;> ring
  simpa only [hidentity] using hmul

/-- The troublesome native z/log z term is smaller than the usual row
density by N^(-d*eta), without counting all natural numbers. -/
theorem p5U7Interior_boundary_row_le {N : ℕ} {eta : ℝ} {t : ℕ × ℕ}
    (hN : 0 < N) (heta : 0 ≤ eta) (ht : t ∈ p5U7InteriorPairs N eta) :
    (t.2 : ℝ)/Real.log (t.2 : ℝ) ≤
      (N : ℝ)^(-(59/250 : ℝ)*eta) *
        (((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ)) := by
  have hto := (Finset.mem_filter.mp ht).1
  have hg := p5U7Mass_outer_geometry hto
  have hc := (Finset.mem_filter.mp hto).1
  have hq := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).2).2.1
  have hqR : (0 : ℝ)<t.2 := by exact_mod_cast hq.pos
  have hlog := Real.log_pos (show (1 : ℝ)<t.2 by exact_mod_cast hq.one_lt)
  have hNp : (0 : ℝ)<N := by exact_mod_cast hN
  have hxR : (0 : ℝ)<(N : ℝ)/((t.1*t.2 : ℕ) : ℝ) := hqR.trans hg.2.2.1
  have hwall := (p5U7Interior_power_wall ht).1
  have hmul := mul_le_mul_of_nonneg_left hwall (Real.rpow_nonneg hqR.le (-eta))
  have hcancel : (t.2 : ℝ)^(-eta)*(t.2 : ℝ)^(1+eta) = (t.2 : ℝ) := by
    rw [← Real.rpow_add hqR]
    convert Real.rpow_one (t.2 : ℝ) using 1 <;> ring
  rw [hcancel] at hmul
  have hbase := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNp (59/250 : ℝ))
    hg.2.1 (neg_nonpos.mpr heta)
  rw [← Real.rpow_mul hNp.le] at hbase
  have hfactor : (t.2 : ℝ)^(-eta) ≤ (N : ℝ)^(-(59/250 : ℝ)*eta) := by
    convert hbase using 1 <;> ring
  have hraw := hmul.trans (mul_le_mul_of_nonneg_right hfactor hxR.le)
  have hdiv := div_le_div_of_nonneg_right hraw hlog.le
  simpa only [mul_div_assoc] using hdiv

theorem p5U7Interior_row_error_nonneg {N : ℕ} {eta : ℝ} {t : ℕ × ℕ}
    (hstart : primeErrorStart ≤ (N : ℝ)^(59/250 : ℝ))
    (ht : t ∈ p5U7InteriorPairs N eta) : 0 ≤ p5U7InteriorBandRowError N t := by
  have hg := p5U7Mass_outer_geometry (Finset.mem_filter.mp ht).1
  have hy := hstart.trans hg.2.1
  have hl := (zero_lt_one.trans_le (one_le_log_of_start_le hy)).le
  have hR := buchstabRemainder_nonneg hy
  have hC : 0 ≤ buchstabBandConstant 3 := by linarith [buchstabBandConstant_ge 3]
  unfold p5U7InteriorBandRowError
  positivity

theorem p5U7Interior_row_error_le {N : ℕ} {eta : ℝ} {t : ℕ × ℕ}
    (hN : 0 < N) (heta : 0 ≤ eta)
    (hstart : primeErrorStart ≤ (N : ℝ)^(59/250 : ℝ))
    (ht : t ∈ p5U7InteriorPairs N eta) :
    p5U7InteriorBandRowError N t ≤
      buchstabBandConstant 3 *
        (buchstabRemainder ((N : ℝ)^(59/250 : ℝ)) +
          (N : ℝ)^(-(59/250 : ℝ)*eta)) *
        (((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ)) := by
  have hg := p5U7Mass_outer_geometry (Finset.mem_filter.mp ht).1
  have hy := hstart.trans hg.2.1
  have hrem := antitoneOn_buchstabRemainder hstart hy hg.2.1
  have hlog : 0 ≤ Real.log (t.2 : ℝ) :=
    (zero_lt_one.trans_le (one_le_log_of_start_le hy)).le
  have hx : 0 ≤ (N : ℝ)/((t.1*t.2 : ℕ) : ℝ) := by positivity
  have hmain := div_nonneg hx hlog
  have hterm := add_le_add (mul_le_mul_of_nonneg_right hrem hmain)
    (p5U7Interior_boundary_row_le hN heta ht)
  have hC : 0 ≤ buchstabBandConstant 3 := by linarith [buchstabBandConstant_ge 3]
  unfold p5U7InteriorBandRowError
  calc
    _ ≤ buchstabBandConstant 3 *
        (buchstabRemainder ((N : ℝ)^(59/250 : ℝ)) *
          (((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ)) +
          (N : ℝ)^(-(59/250 : ℝ)*eta) *
          (((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hterm hC
    _ = _ := by ring

theorem p5U7Interior_pair_mass_le_outer_square (N : ℕ) (eta : ℝ) :
    (∑ t ∈ p5U7InteriorPairs N eta, 1/((t.1*t.2 : ℕ) : ℝ)) ≤
      (p5U7BoundaryOuterReciprocalMass N)^2 := by
  have hsub : p5U7InteriorPairs N eta ⊆
      p5U7BoundaryOuterPrimes N ×ˢ p5U7BoundaryOuterPrimes N := by
    intro t ht
    have hto := (Finset.mem_filter.mp ht).1
    obtain ⟨hc,hD,ho,_hcap⟩ := Finset.mem_filter.mp hto
    obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hc
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_filter.mpr ⟨h₁,hD⟩,
      Finset.mem_filter.mpr ⟨h₂,hD.trans (by exact_mod_cast ho.le)⟩⟩
  calc
    _ ≤ ∑ t ∈ p5U7BoundaryOuterPrimes N ×ˢ p5U7BoundaryOuterPrimes N,
        1/((t.1*t.2 : ℕ) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = _ := by
      rw [Finset.sum_product]
      simp only [Nat.cast_mul,← one_div_mul_one_div]
      rw [← Finset.sum_mul_sum,pow_two]
      rfl

theorem p5U7Interior_density_sum_le {N : ℕ} (eta : ℝ) (hN : 2 ≤ N)
    (houter : p5U7BoundaryOuterReciprocalMass N ≤ 5) :
    (∑ t ∈ p5U7InteriorPairs N eta,
      ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ)) ≤
      (6250/59 : ℝ)*((N : ℝ)/Real.log (N : ℝ)) := by
  have hNr : (1 : ℝ)<N := by exact_mod_cast (by omega : 1<N)
  have hNp := zero_lt_one.trans hNr
  have hlog := Real.log_pos hNr
  have hdlog : 0 < (59/250 : ℝ)*Real.log (N : ℝ) := mul_pos (by norm_num) hlog
  have hpoint : (∑ t ∈ p5U7InteriorPairs N eta,
      ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ)) ≤
      ((250/59 : ℝ)*((N : ℝ)/Real.log (N : ℝ))) *
        (∑ t ∈ p5U7InteriorPairs N eta, 1/((t.1*t.2 : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    have hg := p5U7Mass_outer_geometry (Finset.mem_filter.mp ht).1
    have hbR : (0 : ℝ)<((t.1*t.2 : ℕ) : ℝ) := by exact_mod_cast hg.1
    have hlow := Real.log_le_log (Real.rpow_pos_of_pos hNp (59/250 : ℝ)) hg.2.1
    rw [Real.log_rpow hNp] at hlow
    have h := div_le_div_of_nonneg_left (div_nonneg hNp.le hbR.le) hdlog hlow
    convert h using 1 <;> field_simp [hbR.ne',hlog.ne'] <;> ring
  have hmass := p5U7Interior_pair_mass_le_outer_square N eta
  have houter0 : 0 ≤ p5U7BoundaryOuterReciprocalMass N := by
    unfold p5U7BoundaryOuterReciprocalMass
    exact Finset.sum_nonneg (by intros; positivity)
  have hsq : (p5U7BoundaryOuterReciprocalMass N)^2 ≤ 25 := by nlinarith
  have hscale : 0 ≤ (250/59 : ℝ)*((N : ℝ)/Real.log (N : ℝ)) := by positivity
  exact hpoint.trans ((mul_le_mul_of_nonneg_left (hmass.trans hsq) hscale).trans_eq (by ring))

/-- Exact summed native error, with the same fixed-eta selector. -/
theorem p5U7Interior_band_error_le_coefficient {N : ℕ} {eta : ℝ}
    (hN : 2 ≤ N) (heta : 0 ≤ eta)
    (hstart : primeErrorStart ≤ (N : ℝ)^(59/250 : ℝ))
    (houter : p5U7BoundaryOuterReciprocalMass N ≤ 5) :
    p5U7InteriorBandError N eta ≤
      p5U7InteriorErrorCoefficient N eta*((N : ℝ)/Real.log (N : ℝ)) := by
  have hN0 : 0<N := by omega
  have hC : 0 ≤ buchstabBandConstant 3 := by linarith [buchstabBandConstant_ge 3]
  have hR := buchstabRemainder_nonneg hstart
  have hcoef : 0 ≤ buchstabBandConstant 3 *
      (buchstabRemainder ((N : ℝ)^(59/250 : ℝ)) +
        (N : ℝ)^(-(59/250 : ℝ)*eta)) := by positivity
  calc
    _ ≤ ∑ t ∈ p5U7InteriorPairs N eta,
        buchstabBandConstant 3 *
          (buchstabRemainder ((N : ℝ)^(59/250 : ℝ)) +
            (N : ℝ)^(-(59/250 : ℝ)*eta)) *
          (((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ)) :=
      Finset.sum_le_sum (fun t ht => p5U7Interior_row_error_le hN0 heta hstart ht)
    _ = buchstabBandConstant 3 *
          (buchstabRemainder ((N : ℝ)^(59/250 : ℝ)) +
            (N : ℝ)^(-(59/250 : ℝ)*eta)) *
          (∑ t ∈ p5U7InteriorPairs N eta,
            ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ buchstabBandConstant 3 *
          (buchstabRemainder ((N : ℝ)^(59/250 : ℝ)) +
            (N : ℝ)^(-(59/250 : ℝ)*eta)) *
          ((6250/59 : ℝ)*((N : ℝ)/Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left (p5U7Interior_density_sum_le eta hN houter) hcoef
    _ = _ := by unfold p5U7InteriorErrorCoefficient; ring

theorem p5U7Interior_error_coefficient_tendsto_zero (eta : ℝ) (heta : 0<eta) :
    Tendsto (fun N : ℕ => p5U7InteriorErrorCoefficient N eta) atTop (𝓝 0) := by
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(59/250 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hR := tendsto_buchstabRemainder.comp hgrowth
  have hp : Tendsto (fun N : ℕ => (N : ℝ)^(-(59/250 : ℝ)*eta)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < (59/250 : ℝ)*eta by positivity)).comp
      tendsto_natCast_atTop_atTop
    simpa only [neg_mul] using h
  simpa only [p5U7InteriorErrorCoefficient,zero_add,mul_zero,zero_mul] using
    ((hR.add hp).const_mul (buchstabBandConstant 3)).mul_const (6250/59 : ℝ)

/-- Fixed eta is chosen first. The complete actual interior band error is
o(N/log N), quantitatively with any positive epsilon. -/
theorem p5U7Interior_eventually_band_error_le (eta : ℝ) (heta : 0<eta)
    (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᶠ N : ℕ in atTop,
      0 ≤ p5U7InteriorBandError N eta ∧
        p5U7InteriorBandError N eta ≤ epsilon*((N : ℝ)/Real.log (N : ℝ)) := by
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(59/250 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [(p5U7Interior_error_coefficient_tendsto_zero eta heta).eventually
      (gt_mem_nhds hepsilon),p5U7Boundary_eventually_outer_mass_le_five,
    hgrowth.eventually (eventually_ge_atTop primeErrorStart),eventually_ge_atTop (2 : ℕ)]
    with N hsmall houter hstart hN
  have hNr : (1 : ℝ)<N := by exact_mod_cast (by omega : 1<N)
  have hscale : 0 ≤ (N : ℝ)/Real.log (N : ℝ) := by positivity
  refine ⟨Finset.sum_nonneg (fun t ht => p5U7Interior_row_error_nonneg hstart ht),?_⟩
  exact (p5U7Interior_band_error_le_coefficient hN heta.le hstart houter).trans
    (mul_le_mul_of_nonneg_right hsmall.le hscale)

theorem p5U7Interior_band_error_normalized_tendsto_zero (eta : ℝ) (heta : 0<eta) :
    Tendsto (fun N : ℕ => p5U7InteriorBandError N eta/
      ((N : ℝ)/Real.log (N : ℝ))) atTop (𝓝 0) := by
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(59/250 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hbase := p5U7Interior_eventually_band_error_le eta heta 1 (by norm_num)
  apply squeeze_zero' ?_ ?_ (p5U7Interior_error_coefficient_tendsto_zero eta heta)
  · filter_upwards [hbase,eventually_ge_atTop (2 : ℕ)] with N hN hN2
    have hNr : (1 : ℝ)<N := by exact_mod_cast (by omega : 1<N)
    exact div_nonneg hN.1 (by positivity)
  · filter_upwards [p5U7Boundary_eventually_outer_mass_le_five,
      hgrowth.eventually (eventually_ge_atTop primeErrorStart),eventually_ge_atTop (2 : ℕ)]
      with N houter hstart hN
    have hNr : (1 : ℝ)<N := by exact_mod_cast (by omega : 1<N)
    have hscale : 0 < (N : ℝ)/Real.log (N : ℝ) := by positivity
    exact (div_le_iff₀ hscale).mpr (p5U7Interior_band_error_le_coefficient hN heta.le hstart houter)

/-- This is the original native finite-band estimate summed on precisely
the interior pair support, with no asymptotic supplier assumed. -/
theorem p5U7Interior_native_rough_error_le {N : ℕ} (eta : ℝ)
    (hstart : primeErrorStart ≤ (N : ℝ)^(59/250 : ℝ)) :
    |p5U7InteriorRoughMass N eta-p5U7InteriorBandMain N eta| ≤ p5U7InteriorBandError N eta := by
  unfold p5U7InteriorRoughMass p5U7InteriorBandMain p5U7InteriorBandError
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ t ∈ p5U7InteriorPairs N eta,
        |(roughCount ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ) -
          ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ)) *
            buchstab (Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ))/
            Real.log (t.2 : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t ht
      have hg := p5U7Mass_outer_geometry (Finset.mem_filter.mp ht).1
      exact roughCount_buchstab_band_error 3 (by norm_num)
        (hstart.trans hg.2.1) hg.2.2.1.le hg.2.2.2

/-- Actual prime/semiprime source rows, with both original marked outer
labels, are bounded by the original Buchstab main plus any epsilon mass.
No interior kernel transport is used here. -/
theorem p5U7Interior_eventually_arithmetic_rows_le_main (eta : ℝ) (heta : 0<eta)
    (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᶠ N : ℕ in atTop,
      (∑ t ∈ p5U7InteriorPairs N eta,
        ((p5U7MassPrimeFibre N (t.1*t.2) t.2).card : ℝ) +
          ((p5U7MassSemiprimePairs N t).card : ℝ)) ≤
        p5U7InteriorBandMain N eta + epsilon*((N : ℝ)/Real.log (N : ℝ)) := by
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(59/250 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [p5U7Interior_eventually_band_error_le eta heta epsilon hepsilon,
    hgrowth.eventually (eventually_ge_atTop primeErrorStart)] with N hsmall hstart
  have hsource : (∑ t ∈ p5U7InteriorPairs N eta,
      ((p5U7MassPrimeFibre N (t.1*t.2) t.2).card : ℝ) +
        ((p5U7MassSemiprimePairs N t).card : ℝ)) ≤ p5U7InteriorRoughMass N eta := by
    apply Finset.sum_le_sum
    intro t ht
    exact p5U7Mass_row_le_roughCount (Finset.mem_filter.mp ht).1
  have hrough := (le_abs_self _).trans (p5U7Interior_native_rough_error_le eta hstart)
  exact hsource.trans (by linarith only [hrough,hsmall.2])

end

end ImbalancedChen
