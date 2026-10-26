import ImbalancedChen.P5U7PrimeCutoffLogIntegral

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Strict positivity and the exact support threshold for the genuine prime
cutoff integral. A nonempty OPEN interval of strictly positive rows is
proved to have positive Lebesgue measure and embedded in the actual
positive-part support. No integral positivity is assumed.
-/
namespace ImbalancedChen
noncomputable section
open Set MeasureTheory Filter Topology
open Classical

/-- The literal logarithmic row is strictly positive exactly before the
strict outer support cap. Closed equality gives the already proved zero. -/
theorem p5U7PrimeCutoffLogRow_pos_iff {eta t : ℝ} (heta : 0 ≤ eta)
    (ht : t ∈ Icc (59/250 : ℝ) (1/3)) :
    0 < p5U7PrimeCutoffLogRow eta t ↔ t < 1/(3+eta) := by
  have hg := p5U7PrimeCutoffLog_geometry heta ht
  have ht0 : 0 < t := by linarith [ht.1]
  have he1 : 0 < 1+eta := by linarith
  have he3 : 0 < 3+eta := by linarith
  constructor
  · intro h
    have hl : 0 < Real.log ((1-2*t)/(t*(1+eta))) := by
      have hh := (lt_div_iff₀ hg.2).mp h
      simpa only [zero_mul] using hh
    have harg := (Real.log_pos_iff hg.1.le).mp hl
    have hm := (one_lt_div (mul_pos ht0 he1)).mp harg
    exact (lt_div_iff₀ he3).mpr (by nlinarith only [hm])
  · intro h
    have hm := (lt_div_iff₀ he3).mp h
    have harg : 1 < (1-2*t)/(t*(1+eta)) :=
      (one_lt_div (mul_pos ht0 he1)).mpr (by nlinarith only [hm])
    exact div_pos (Real.log_pos harg) hg.2

/-- The actual clamped prime row has the SAME sharp positivity support. -/
theorem p5U7PrimeCutoffRow_pos_iff {eta t : ℝ} (heta : 0 ≤ eta)
    (ht : t ∈ Icc (59/250 : ℝ) (1/3)) :
    0 < p5U7PrimeCutoffRow eta t ↔ t < 1/(3+eta) := by
  rw [p5U7PrimeCutoffRow_eq_log_positive_part heta ht]
  have hh : 0 < max 0 (p5U7PrimeCutoffLogRow eta t) ↔
      0 < p5U7PrimeCutoffLogRow eta t := by
    constructor
    · intro h
      by_contra hn
      have hr : p5U7PrimeCutoffLogRow eta t ≤ 0 := le_of_not_gt hn
      rw [max_eq_left hr] at h
      exact (lt_irrefl 0) h
    · intro h
      exact h.trans_le (le_max_right _ _)
  exact hh.trans (p5U7PrimeCutoffLogRow_pos_iff heta ht)

/-- A subcritical nonnegative margin leaves a genuine nonempty outer
prime interval. Its full cap remains inside the original closed interval. -/
theorem p5U7PrimeCutoff_positive_interval {eta : ℝ}
    (heta : 0 ≤ eta) (hsub : eta < (73/59 : ℝ)) :
    (59/250 : ℝ) < 1/(3+eta) ∧ 1/(3+eta) ≤ (1/3 : ℝ) ∧
      0 < volume (Ioo (59/250 : ℝ) (1/(3+eta))) := by
  have he3 : 0 < 3+eta := by linarith
  have hlow : (59/250 : ℝ) < 1/(3+eta) :=
    (lt_div_iff₀ he3).mpr (by nlinarith only [hsub])
  have hhigh : 1/(3+eta) ≤ (1/3 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 3)
      (by linarith only [heta])
  exact ⟨hlow,hhigh,(Measure.measure_Ioo_pos volume).mpr hlow⟩

/-- Genuine strict positivity of the actual cutoff integral, proved from
positive measure of the actual nonzero integrand support. -/
theorem p5U7PrimeLeadingIntegral_pos_of_subcritical (eta : ℝ)
    (heta : 0 ≤ eta) (hsub : eta < (73/59 : ℝ)) :
    0 < p5U7PrimeLeadingIntegral eta := by
  let f : ℝ → ℝ := fun t => max 0 (p5U7PrimeCutoffLogRow eta t)
  have hi : IntervalIntegrable f volume (59/250 : ℝ) (1/3) :=
    p5U7PrimeCutoffLogPositive_intervalIntegrable eta heta
  have hn : ∀ t : ℝ, 0 ≤ f t := fun t => le_max_left _ _
  have hg := p5U7PrimeCutoff_positive_interval heta hsub
  have hsubset : Ioo (59/250 : ℝ) (1/(3+eta)) ⊆
      Function.support f ∩ Ioc (59/250 : ℝ) (1/3) := by
    intro t ht
    have htI : t ∈ Icc (59/250 : ℝ) (1/3) := ⟨ht.1.le,ht.2.le.trans hg.2.1⟩
    have hlog := (p5U7PrimeCutoffLogRow_pos_iff heta htI).mpr ht.2
    have hf : 0 < f t := hlog.trans_le (le_max_right _ _)
    exact ⟨hf.ne',⟨ht.1,ht.2.le.trans hg.2.1⟩⟩
  have hsupport : 0 < volume (Function.support f ∩ Ioc (59/250 : ℝ) (1/3)) :=
    hg.2.2.trans_le (measure_mono hsubset)
  have hpos : 0 < ∫ t in (59/250 : ℝ)..(1/3 : ℝ), f t :=
    (intervalIntegral.integral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall hn) hi).mpr ⟨by norm_num,hsupport⟩
  rw [p5U7PrimeLeadingIntegral_eq_log_positive_part eta heta]
  exact hpos

/-- The native support threshold is exact in BOTH directions. -/
theorem p5U7PrimeLeadingIntegral_pos_iff (eta : ℝ) (heta : 0 ≤ eta) :
    0 < p5U7PrimeLeadingIntegral eta ↔ eta < (73/59 : ℝ) := by
  constructor
  · intro hpos
    by_contra hn
    have hz := p5U7PrimeLeadingIntegral_eq_zero_of_large_margin eta (le_of_not_gt hn)
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos
  · exact p5U7PrimeLeadingIntegral_pos_of_subcritical eta heta

/-- Exact vanishing iff the margin reaches the support threshold. -/
theorem p5U7PrimeLeadingIntegral_zero_iff (eta : ℝ) (heta : 0 ≤ eta) :
    p5U7PrimeLeadingIntegral eta = 0 ↔ (73/59 : ℝ) ≤ eta := by
  constructor
  · intro hz
    by_contra hn
    have hp := p5U7PrimeLeadingIntegral_pos_of_subcritical eta heta (lt_of_not_ge hn)
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  · exact p5U7PrimeLeadingIntegral_eq_zero_of_large_margin eta

/-- The independent original prime component constant is strictly positive. -/
theorem p5U7ComponentPrimeIntegral_pos : 0 < p5U7ComponentPrimeIntegral := by
  rw [← p5U7PrimeLeadingIntegral_zero_eq_component]
  exact p5U7PrimeLeadingIntegral_pos_of_subcritical 0 (by norm_num) (by norm_num)
end
end ImbalancedChen
