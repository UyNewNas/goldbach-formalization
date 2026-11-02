import ImbalancedChen.Part3OriginalGevreyActualPsiFourierIBP
import ImbalancedChen.Part3OriginalPhysicalGevreyFrequencyScale
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-28.

The original medium proof selects the constructed Gevrey majorant, equal to
one on [1,2] and supported in [1/2,5/2]. This file specializes Mathlib's
generic Schwartz Poisson theorem to that actual profile. It retains the
arbitrary signed residue, every Fourier sign, the exact zero mode, and the
nonzero integer-frequency series. It does not equate this profile with the
older hard-coded dyadic bump in Part3CommonPoisson.

The guarded source imports are frozen SHA-256
3edbfd230c917ff0d003c27b11b97e78332fa663389b04b723cbfa319344a715
for actual paperPsi Fourier IBP, and
4176019daa74916cddbc05097aea904c8d98a38f4bd4189aaa5a0af303b6f94d
for the physical Lcm/frequency scale. Neither is installed or typechecked.
The selected-order Gevrey lattice tail and the completed E2 row dictionary
are separate unclosed interfaces.
-/

noncomputable section

open Classical Set MeasureTheory FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open ImbalancedChen.Part3.OriginalGevreyFinalPsi20261028
open ImbalancedChen.Part3.OriginalGevreyActualPsiFourierIBP20261028
open ImbalancedChen.Part3.OriginalPhysicalGevreyFrequencyScale20261028

namespace ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028

private theorem paperPsiComplex_smooth :
    ContDiff ℝ (⊤ : ℕ∞) paperPsiComplex := by
  exact Complex.ofRealCLM.contDiff.comp paperPsi_contDiff

private theorem paperPsiComplex_compact : HasCompactSupport paperPsiComplex := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact (subset_tsupport _).trans paperPsiComplex_tsupport_subset

/-- The manuscript's exact Gevrey profile, packaged for generic Poisson. -/
def paperPsiSchwartz : 𝓢(ℝ, ℂ) :=
  paperPsiComplex_compact.toSchwartzMap paperPsiComplex_smooth

@[simp] theorem paperPsiSchwartz_apply (x : ℝ) :
    paperPsiSchwartz x = paperPsiComplex x := rfl

def scaledPaperPsi (V x : ℝ) : ℂ := paperPsiComplex (x / V)

private theorem scaledPaperPsi_compact {V : ℝ} (hV : 0 < V) :
    HasCompactSupport (scaledPaperPsi V) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  have hne : paperPsiComplex (x / V) ≠ 0 := hx
  have hsupp : x / V ∈ Icc (1 / 2 : ℝ) (5 / 2) :=
    paperPsiComplex_tsupport_subset (subset_tsupport _ hne)
  constructor
  · have hh := (le_div_iff₀ hV).mp hsupp.1
    nlinarith
  · have hh := (div_le_iff₀ hV).mp hsupp.2
    nlinarith

/-- Schwartz rescaling is formed from the same paperPsi, not an arbitrary
replacement weight. -/
def scaledPaperPsiSchwartz (V : ℝ) (hV : 0 < V) : 𝓢(ℝ, ℂ) :=
  (scaledPaperPsi_compact hV).toSchwartzMap
    (paperPsiComplex_smooth.comp (contDiff_id.div_const V))

@[simp] theorem scaledPaperPsiSchwartz_apply (V : ℝ) (hV : 0 < V) (x : ℝ) :
    scaledPaperPsiSchwartz V hV x = scaledPaperPsi V x := rfl

/-- Mathlib's Fourier convention gives the exact positive rescaling. -/
theorem scaledPaperPsi_fourier {V : ℝ} (hV : 0 < V) (frequency : ℝ) :
    𝓕 (scaledPaperPsi V) frequency =
      V • (𝓕 paperPsiComplex) (V * frequency) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have hphase (x : ℝ) : x / V * (V * frequency) = x * frequency := by
    field_simp
  calc
    _ = ∫ x : ℝ, Real.fourierChar (-(x / V * (V * frequency))) •
          paperPsiComplex (x / V) := by
      simp only [hphase, scaledPaperPsi]
    _ = |V| • ∫ x : ℝ,
          Real.fourierChar (-(x * (V * frequency))) • paperPsiComplex x :=
      MeasureTheory.Measure.integral_comp_div
        (fun x : ℝ => Real.fourierChar (-(x * (V * frequency))) •
          paperPsiComplex x) V
    _ = _ := by rw [abs_of_pos hV]

/-- The generic Schwartz Poisson theorem is the only Poisson primitive
used here. The affine residue shift is b/L, and the Fourier argument is
exactly h*V/L. -/
theorem paperPsi_poisson_rescaled {V L : ℝ} (hV : 0 < V) (hL : 0 < L)
    (b : ℝ) :
    (∑' z : ℤ, scaledPaperPsi V (b + L * z)) =
      ∑' h : ℤ, (V / L) • (𝓕 paperPsiComplex) ((V / L) * h) *
        fourier h (b / L : UnitAddCircle) := by
  have hVL : 0 < V / L := div_pos hV hL
  have hscale (z : ℤ) :
      (b / L + (z : ℝ)) / (V / L) = (b + L * z) / V := by
    field_simp
  convert (scaledPaperPsiSchwartz (V / L) hVL).tsum_eq_tsum_fourier (b / L)
      using 1
  · apply tsum_congr
    intro z
    simp only [scaledPaperPsiSchwartz_apply, scaledPaperPsi, hscale]
  · apply tsum_congr
    intro h
    rw [SchwartzMap.fourier_coe]
    exact congrArg (fun v : ℂ => v * fourier h (b / L : UnitAddCircle))
      (scaledPaperPsi_fourier hVL h).symm

/-- The complete paper-profile Fourier series is absolutely summable. -/
theorem paperPsi_frequency_summable_norm {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun h : ℤ =>
      ‖t • (𝓕 paperPsiComplex) (t * h) *
        fourier h (x : UnitAddCircle)‖) := by
  let f := scaledPaperPsiSchwartz t ht
  have hnorm : Summable (fun h : ℤ => ‖(𝓕 f) (h : ℝ)‖) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 f).isBigO_cocompact_rpow (-2)).norm_left.comp_tendsto
        Int.tendsto_coe_cofinite)
  have hcoef (h : ℤ) :
      (𝓕 f) (h : ℝ) = t • (𝓕 paperPsiComplex) (t * h) := by
    rw [SchwartzMap.fourier_coe]
    exact scaledPaperPsi_fourier ht h
  apply hnorm.congr
  intro h
  rw [hcoef]
  simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one]

/-- The signed nonzero mode keeps the exact Fourier transform of paperPsi. -/
def paperPsiNonzeroMode (t x : ℝ) (h : ℤ) : ℂ :=
  if h = 0 then 0 else
    t • (𝓕 paperPsiComplex) (t * h) *
      fourier h (x : UnitAddCircle)

@[simp] theorem paperPsiNonzeroMode_zero (t x : ℝ) :
    paperPsiNonzeroMode t x 0 = 0 := rfl

theorem paperPsiNonzeroMode_summable_norm {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun h : ℤ => ‖paperPsiNonzeroMode t x h‖) := by
  apply (paperPsi_frequency_summable_norm ht x).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro h
  by_cases hh : h = 0
  · simp only [paperPsiNonzeroMode, if_pos hh, norm_zero]
    exact norm_nonneg _
  · simp only [paperPsiNonzeroMode, if_neg hh, le_refl]

/-- Separate h=0 from the same absolutely summable complete series. -/
theorem paperPsi_poisson_zero_add_nonzero
    {V L : ℝ} (hV : 0 < V) (hL : 0 < L) (b : ℝ) :
    (∑' z : ℤ, scaledPaperPsi V (b + L * z)) =
      (V / L) • (𝓕 paperPsiComplex) 0 +
        ∑' h : ℤ, paperPsiNonzeroMode (V / L) (b / L) h := by
  have hr := (paperPsiNonzeroMode_summable_norm (div_pos hV hL) (b / L)).of_norm
  let f : ℤ → ℂ := fun h =>
    (V / L) • (𝓕 paperPsiComplex) ((V / L) * h) *
      fourier h (b / L : UnitAddCircle)
  have hs : Summable (Function.update f 0 0) := by
    apply hr.congr
    intro h
    by_cases hh : h = 0 <;> simp [f, paperPsiNonzeroMode, hh]
  have heq := Summable.tsum_eq_add_tsum_ite' (f := f) 0 hs
  rw [paperPsi_poisson_rescaled hV hL]
  change (∑' h : ℤ, f h) = _
  rw [heq]
  simp only [f, Int.cast_zero, mul_zero, fourier_zero, mul_one,
    paperPsiNonzeroMode]

/-- The finite original residue-class carrier contains all natural points
where the constructed majorant is nonzero. -/
def paperPsiNaturalCarrier (V : ℝ) : Finset ℕ :=
  Finset.Icc (Nat.ceil (V / 2)) (Nat.floor (5 * V / 2))

theorem paperPsiNaturalCarrier_support {V : ℝ} (hV : 0 < V)
    {m : ℕ} (hm : scaledPaperPsi V m ≠ 0) :
    m ∈ paperPsiNaturalCarrier V := by
  have hne : paperPsiComplex ((m : ℝ) / V) ≠ 0 := hm
  have hsupp : (m : ℝ) / V ∈ Icc (1 / 2 : ℝ) (5 / 2) :=
    paperPsiComplex_tsupport_subset (subset_tsupport _ hne)
  have hlo : V / 2 ≤ (m : ℝ) := by
    have hh := (le_div_iff₀ hV).mp hsupp.1
    nlinarith
  have hhi : (m : ℝ) ≤ 5 * V / 2 := by
    have hh := (div_le_iff₀ hV).mp hsupp.2
    nlinarith
  exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo, Nat.le_floor hhi⟩

/-- Natural residue classes and affine integer progressions are identical
on the literal nonzero support, including a negative representative b. -/
theorem paperPsi_finite_progression_eq_tsum
    {V : ℝ} (hV : 0 < V) {L : ℕ} (hL : 0 < L) (b : ℤ) :
    (∑ m ∈ paperPsiNaturalCarrier V,
      if Int.ModEq L (m : ℤ) b then scaledPaperPsi V m else 0) =
        ∑' z : ℤ, scaledPaperPsi V ((b : ℝ) + L * z) := by
  let f : ℕ → ℂ := fun m =>
    if Int.ModEq L (m : ℤ) b then scaledPaperPsi V m else 0
  let g : ℤ → ℂ := fun z => scaledPaperPsi V ((b : ℝ) + L * z)
  have hnonneg (z : Function.support g) :
      0 ≤ b + (L : ℤ) * z.val := by
    have hz : paperPsiComplex (((b : ℝ) + L * z.val) / V) ≠ 0 := by
      simpa only [g, scaledPaperPsi, Function.mem_support, ne_eq] using z.property
    have hp := (paperPsiComplex_tsupport_subset (subset_tsupport _ hz)).1
    have hp' : (0 : ℝ) ≤ (b : ℝ) + L * z.val := by
      have hh := (le_div_iff₀ hV).mp hp
      linarith
    exact_mod_cast hp'
  let i : Function.support g → ℕ :=
    fun z => (b + (L : ℤ) * z.val).toNat
  have hcast (z : Function.support g) :
      (i z : ℤ) = b + (L : ℤ) * z.val :=
    Int.toNat_of_nonneg (hnonneg z)
  have hi : Function.Injective i := by
    intro z z' h
    have he := congrArg (fun n : ℕ => (n : ℤ)) h
    rw [hcast, hcast] at he
    apply Subtype.ext
    exact mul_left_cancel₀ (by exact_mod_cast hL.ne') (add_left_cancel he)
  have hf : Function.support f ⊆ Set.range i := by
    intro m hm
    have hm' : Int.ModEq L (m : ℤ) b ∧ scaledPaperPsi V m ≠ 0 := by
      simpa only [f, Function.mem_support, ne_eq, ite_eq_right_iff,
        Classical.not_imp] using hm
    obtain ⟨z, hz⟩ := Int.modEq_iff_dvd.mp hm'.1.symm
    have he : b + (L : ℤ) * z = m := by linarith
    have heR : (b : ℝ) + (L : ℝ) * z = m := by exact_mod_cast he
    have hg : z ∈ Function.support g := by
      simpa only [Function.mem_support, g, heR, ne_eq] using hm'.2
    refine ⟨⟨z, hg⟩, ?_⟩
    simp only [i, he, Int.toNat_natCast]
  have hfg (z : Function.support g) : f (i z) = g z := by
    have hc : Int.ModEq L (i z : ℤ) b := by
      rw [hcast]
      apply Int.modEq_iff_dvd.mpr
      exact ⟨-z.val, by ring⟩
    have hr : (i z : ℝ) = (b : ℝ) + (L : ℝ) * z.val := by
      exact_mod_cast hcast z
    simp only [f, hc, if_pos, hr, g]
  calc
    _ = ∑' m : ℕ, f m := by
      symm
      apply tsum_eq_sum
      intro m hm
      have hw : scaledPaperPsi V m = 0 := by
        by_contra hw
        exact hm (paperPsiNaturalCarrier_support hV hw)
      simp [f, hw]
    _ = _ := tsum_eq_tsum_of_ne_zero_bij i hi hf hfg

/-- Exact original-profile Poisson packet for a finite natural residue
class. The zero and both signed nonzero frequencies are kept. -/
theorem paperPsi_finite_residue_poisson_packet
    {V : ℝ} (hV : 0 < V) {L : ℕ} (hL : 0 < L) (b : ℤ) :
    (∑ m ∈ paperPsiNaturalCarrier V,
      if Int.ModEq L (m : ℤ) b then scaledPaperPsi V m else 0) =
      (V / (L : ℝ)) • (𝓕 paperPsiComplex) 0 +
        ∑' h : ℤ,
          paperPsiNonzeroMode (V / (L : ℝ)) ((b : ℝ) / L) h := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  calc
    _ = ∑' z : ℤ, scaledPaperPsi V ((b : ℝ) + L * z) :=
      paperPsi_finite_progression_eq_tsum hV hL b
    _ = _ := paperPsi_poisson_zero_add_nonzero hV hLr b

/-- At an omitted physical frequency, the packet coefficient has the
actual Gevrey Fourier order bound. Lattice summation of these bounds is
left to the Gevrey tail source. -/
theorem omitted_physical_packet_mode_order
    {band Q R S V L : ℝ} {D : ℕ} {h : ℤ}
    (hband : 0 < band) (hQ : 0 < Q) (hR : 0 < R) (hS : 0 < S)
    (hV : 0 < V) (hL : 0 < L) (hD : 0 < D)
    (hDL : (D : ℝ) * L ≤ 32 * Q * R ^ 2 * S ^ 2)
    (homit : physicalH band Q R S V D < h.natAbs)
    (x : ℝ) (j : ℕ) :
    ‖paperPsiNonzeroMode (V / L) x h‖ ≤
      (V / L) *
        (3 * (((16 / Real.pi : ℝ) /
          |(V / L) * (h : ℝ)|) ^ j) * ((j.factorial : ℝ) ^ 2)) := by
  have hne : h ≠ 0 := by
    intro hz
    subst h
    simp at homit
  have hb := omitted_actual_paperPsi_fourier_order
    hband hQ hR hS hV hL hD hDL homit j
  unfold paperPsiNonzeroMode
  simp only [if_neg hne, norm_mul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hV hL), fourier_apply, Circle.norm_coe, mul_one]
  exact mul_le_mul_of_nonneg_left hb (div_pos hV hL).le

end ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
