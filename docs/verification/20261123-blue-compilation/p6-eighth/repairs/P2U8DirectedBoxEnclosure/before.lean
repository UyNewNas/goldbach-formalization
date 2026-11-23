import ImbalancedChen.P2NegativeDomainCover
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
SOURCE ONLY / UNCOMPILED. The companion draft directory must be a source
search root when these candidates are eventually installed or compiled.

Rational whole-box enclosures for the original U8 harmonic density. A
boundary cell is charged its entire closed rectangle. The finite-cover
theorem permits overlaps and never requires that a box lie in U8.
The adopted fine-cell table is not present and no adopted endpoint is
claimed. The final coarse instance is a genuine, deliberately loose bound.
-/

namespace ImbalancedChen.P2U8DirectedBoxEnclosure

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open Classical
open P2NegativeDomainCover

abbrev Point := Fin 2 → ℝ

structure Box where
  xl : ℚ
  xu : ℚ
  yl : ℚ
  yu : ℚ
  deriving DecidableEq

def Box.Valid (B : Box) : Prop :=
  0 < B.xl ∧ B.xl ≤ B.xu ∧ 0 < B.yl ∧ B.yl ≤ B.yu ∧ B.xu + B.yu < 1

instance (B : Box) : Decidable B.Valid := by unfold Box.Valid; infer_instance

def Box.check (B : Box) : Bool := decide B.Valid

theorem Box.check_sound (B : Box) (h : B.check = true) : B.Valid := by
  exact of_decide_eq_true h

def Box.lo (B : Box) : Point := ![(B.xl : ℝ), (B.yl : ℝ)]
def Box.hi (B : Box) : Point := ![(B.xu : ℝ), (B.yu : ℝ)]
def Box.region (B : Box) : Set Point := Icc B.lo B.hi

/-- Both enclosures are exact rational expressions in the stored corners. -/
def Box.upper (B : Box) : ℚ := 1 / (B.xl * B.yl * (1 - B.xu - B.yu))
def Box.lower (B : Box) : ℚ := 1 / (B.xu * B.yu * (1 - B.xl - B.yl))
def Box.area (B : Box) : ℚ := (B.xu - B.xl) * (B.yu - B.yl)

theorem Box.real_guards {B : Box} (hB : B.Valid) :
    0 < (B.xl : ℝ) ∧ (B.xl : ℝ) ≤ B.xu ∧
      0 < (B.yl : ℝ) ∧ (B.yl : ℝ) ≤ B.yu ∧ (B.xu : ℝ) + B.yu < 1 := by
  dsimp only [Box.Valid] at hB
  exact_mod_cast hB

theorem Box.mem_region {B : Box} {x : Point} :
    x ∈ B.region ↔
      (B.xl : ℝ) ≤ x 0 ∧ x 0 ≤ B.xu ∧ (B.yl : ℝ) ≤ x 1 ∧ x 1 ≤ B.yu := by
  constructor
  · intro hx
    exact ⟨hx.1 0, hx.2 0, hx.1 1, hx.2 1⟩
  · rintro ⟨hx0, hx1, hy0, hy1⟩
    constructor <;> intro i <;> fin_cases i
    · exact hx0
    · exact hy0
    · exact hx1
    · exact hy1

theorem density_eq_reciprocal (x : Point) :
    eighthDensity x = 1 / (x 0 * x 1 * (1 - x 0 - x 1)) := by
  simp only [eighthDensity, Fin.prod_univ_two, one_div, mul_inv_rev]
  ring

theorem Box.density_enclosure {B : Box} (hB : B.Valid) {x : Point}
    (hx : x ∈ B.region) :
    (B.lower : ℝ) ≤ eighthDensity x ∧ eighthDensity x ≤ (B.upper : ℝ) := by
  obtain ⟨ha, hab, hc, hcd, hbd⟩ := Box.real_guards hB
  obtain ⟨hax, hxb, hcy, hyd⟩ := Box.mem_region.mp hx
  have hxpos : 0 < x 0 := ha.trans_le hax
  have hypos : 0 < x 1 := hc.trans_le hcy
  have hbpos : 0 < (B.xu : ℝ) := ha.trans_le hab
  have hdpos : 0 < (B.yu : ℝ) := hc.trans_le hcd
  have hgap0 : 0 < 1 - (B.xu : ℝ) - B.yu := by linarith only [hbd]
  have hgap : 0 < 1 - x 0 - x 1 := by linarith only [hgap0, hxb, hyd]
  have hgapUpper : 0 < 1 - (B.xl : ℝ) - B.yl := by
    linarith only [hgap0, hab, hcd]
  have hlo : (B.xl : ℝ) * B.yl * (1 - B.xu - B.yu) ≤
      x 0 * x 1 * (1 - x 0 - x 1) := by
    calc
      _ ≤ x 0 * x 1 * (1 - B.xu - B.yu) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hax hcy hc.le hxpos.le) hgap0.le
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by linarith only [hxb, hyd]) (mul_nonneg hxpos.le hypos.le)
  have hhi : x 0 * x 1 * (1 - x 0 - x 1) ≤
      (B.xu : ℝ) * B.yu * (1 - B.xl - B.yl) := by
    calc
      _ ≤ (B.xu : ℝ) * B.yu * (1 - x 0 - x 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hxb hyd hypos.le hbpos.le) hgap.le
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by linarith only [hax, hcy]) (mul_nonneg hbpos.le hdpos.le)
  rw [density_eq_reciprocal]
  constructor
  · simpa only [Box.lower, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_sub] using
      one_div_le_one_div_of_le (mul_pos (mul_pos hxpos hypos) hgap) hhi
  · simpa only [Box.upper, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_sub] using
      one_div_le_one_div_of_le (mul_pos (mul_pos ha hc) hgap0) hlo

theorem Box.upper_nonneg {B : Box} (hB : B.Valid) : 0 ≤ (B.upper : ℝ) := by
  obtain ⟨ha, _, hc, _, hbd⟩ := Box.real_guards hB
  have hgap : 0 < 1 - (B.xu : ℝ) - B.yu := by linarith only [hbd]
  simp only [Box.upper, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_sub]
  exact (one_div_pos.mpr (mul_pos (mul_pos ha hc) hgap)).le

theorem Box.lo_le_hi {B : Box} (hB : B.Valid) : B.lo ≤ B.hi := by
  obtain ⟨_, hab, _, hcd, _⟩ := Box.real_guards hB
  intro i
  fin_cases i
  · exact hab
  · exact hcd

/-- Exact rational area, with closed walls included in the set. -/
theorem Box.volume_real {B : Box} (hB : B.Valid) :
    (volume B.region).toReal = (B.area : ℝ) := by
  rw [Box.region, Real.volume_Icc_pi_toReal (Box.lo_le_hi hB)]
  simp only [Fin.prod_univ_two, Box.lo, Box.hi, Matrix.cons_val_zero,
    Matrix.cons_val_one, Box.area, Rat.cast_mul, Rat.cast_sub]

def Box.majorant (B : Box) : Point → ℝ := B.region.indicator (fun _ => (B.upper : ℝ))

theorem Box.majorant_nonneg {B : Box} (hB : B.Valid) (x : Point) :
    0 ≤ B.majorant x := by
  by_cases hx : x ∈ B.region
  · simpa only [Box.majorant, indicator_of_mem hx] using Box.upper_nonneg hB
  · simp only [Box.majorant, indicator_of_notMem hx, le_refl]

theorem Box.integrable_majorant (B : Box) : Integrable B.majorant := by
  have hconst : IntegrableOn (fun _ : Point => (B.upper : ℝ)) B.region :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  exact hconst.integrable_indicator measurableSet_Icc

theorem Box.integral_const {B : Box} (hB : B.Valid) (q : ℚ) :
    (∫ _x : Point in B.region, (q : ℝ)) = ((q * B.area : ℚ) : ℝ) := by
  rw [MeasureTheory.integral_const]
  simp only [Measure.real, Measure.restrict_apply measurableSet_univ, univ_inter,
    smul_eq_mul, Box.volume_real hB, Rat.cast_mul]
  ring

/-- A boundary cell is charged the whole rational rectangle area. -/
theorem Box.integral_majorant {B : Box} (hB : B.Valid) :
    (∫ x, B.majorant x) = ((B.upper * B.area : ℚ) : ℝ) := by
  rw [Box.majorant, integral_indicator measurableSet_Icc]
  exact Box.integral_const hB B.upper

theorem Box.integrable_density {B : Box} (hB : B.Valid) :
    IntegrableOn eighthDensity B.region := by
  have hc : ContinuousOn eighthDensity B.region := by
    change ContinuousOn (fun x => eighthDensity x) B.region
    simp_rw [density_eq_reciprocal]
    apply continuousOn_const.div (by fun_prop)
    intro x hx
    obtain ⟨ha, _, hc, _, hbd⟩ := Box.real_guards hB
    obtain ⟨hax, hxb, hcy, hyd⟩ := Box.mem_region.mp hx
    have hxpos : 0 < x 0 := ha.trans_le hax
    have hypos : 0 < x 1 := hc.trans_le hcy
    have hgap : 0 < 1 - x 0 - x 1 := by linarith only [hbd, hxb, hyd]
    exact (mul_pos (mul_pos hxpos hypos) hgap).ne'
  exact hc.integrableOn_compact isCompact_Icc

/-- Both directions enclose the true full-box integral. Only the upper
direction is used when a box crosses the U8 boundary. -/
theorem Box.integral_density_enclosure {B : Box} (hB : B.Valid) :
    ((B.lower * B.area : ℚ) : ℝ) ≤ (∫ x in B.region, eighthDensity x) ∧
      (∫ x in B.region, eighthDensity x) ≤ ((B.upper * B.area : ℚ) : ℝ) := by
  have hconst (q : ℚ) : IntegrableOn (fun _ : Point => (q : ℝ)) B.region :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  constructor
  · rw [← Box.integral_const hB B.lower]
    exact setIntegral_mono_on (hconst B.lower) (Box.integrable_density hB)
      measurableSet_Icc (fun x hx => (Box.density_enclosure hB hx).1)
  · rw [← Box.integral_const hB B.upper]
    exact setIntegral_mono_on (Box.integrable_density hB) (hconst B.upper)
      measurableSet_Icc (fun x hx => (Box.density_enclosure hB hx).2)

theorem integrableOn_eighthDensity : IntegrableOn eighthDensity eighthDomain := by
  have h := (integrableOn_logPrimeBox_test_cube
    (by norm_num : (0 : ℝ) < 417 / 5000) currentChenUpsilon8HarmonicKernel
    continuous_currentChenUpsilon8HarmonicKernel.continuousOn).mono_set
      (show eighthDomain ⊆ logPrimeBox (fun _ : Fin 2 => (417 / 5000 : ℝ))
        (fun _ => (1 / 2 : ℝ)) from inter_subset_left)
  apply h.congr_fun ?_ measurableSet_eighthDomain
  intro x hx
  change currentChenUpsilon8HarmonicKernel x * (∏ i, 1 / x i) = eighthDensity x
  rw [currentChenUpsilon8HarmonicKernel_eq hx.2]
  rfl

/-- Finite whole-box cover to a rational upper bound. Overlap and cells
crossing an affine U8 wall are allowed; every such cell pays its full cap.
The hypotheses are geometric coverage and decidable rational guards,
with no integral estimate among the assumptions. -/
theorem eighthIntegral_le_box_cover {ι : Type*} (s : Finset ι) (B : ι → Box)
    (hvalid : ∀ i ∈ s, (B i).Valid)
    (hcover : ∀ x ∈ eighthDomain, ∃ i ∈ s, x ∈ (B i).region) :
    currentChenUpsilon8HarmonicIntegral ≤
      ((∑ i ∈ s, (B i).upper * (B i).area : ℚ) : ℝ) := by
  have hf : Integrable (eighthDomain.indicator eighthDensity) :=
    integrableOn_eighthDensity.integrable_indicator measurableSet_eighthDomain
  have hg : Integrable (fun x => ∑ i ∈ s, (B i).majorant x) :=
    integrable_finsetSum s (fun i _ => Box.integrable_majorant (B i))
  have hpoint (x : Point) : eighthDomain.indicator eighthDensity x ≤
      ∑ i ∈ s, (B i).majorant x := by
    by_cases hx : x ∈ eighthDomain
    · obtain ⟨i, hi, hix⟩ := hcover x hx
      rw [indicator_of_mem hx]
      calc
        eighthDensity x ≤ ((B i).upper : ℝ) := ((B i).density_enclosure (hvalid i hi) hix).2
        _ = (B i).majorant x := (indicator_of_mem hix _).symm
        _ ≤ _ := Finset.single_le_sum (fun j hj => Box.majorant_nonneg (hvalid j hj) x) hi
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun i hi => Box.majorant_nonneg (hvalid i hi) x)
  calc
    currentChenUpsilon8HarmonicIntegral =
        ∫ x, eighthDomain.indicator eighthDensity x :=
      (integral_indicator measurableSet_eighthDomain).symm
    _ ≤ ∫ x, ∑ i ∈ s, (B i).majorant x := integral_mono hf hg hpoint
    _ = ∑ i ∈ s, ∫ x, (B i).majorant x :=
      integral_finsetSum s (fun i _ => Box.integrable_majorant (B i))
    _ = ∑ i ∈ s, (((B i).upper * (B i).area : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Box.integral_majorant (hvalid i hi)
    _ = _ := by
      push_cast

/-- A rational sufficient test for one rectangle to cover the entire U8.
It retains the maximal moving-slice height at the left original endpoint. -/
def Box.CoversOriginal (B : Box) : Prop :=
  B.xl ≤ 417 / 5000 ∧ (1 / 3 : ℚ) ≤ B.xu ∧
    B.yl ≤ 1 / 3 ∧ (1 - (417 / 5000 : ℚ)) / 2 ≤ B.yu

instance (B : Box) : Decidable B.CoversOriginal := by
  unfold Box.CoversOriginal
  infer_instance

theorem Box.coversOriginal_sound {B : Box} (hB : B.CoversOriginal) :
    eighthDomain ⊆ B.region := by
  have hBr : (B.xl : ℝ) ≤ 417 / 5000 ∧ (1 / 3 : ℝ) ≤ B.xu ∧
      (B.yl : ℝ) ≤ 1 / 3 ∧ (1 - (417 / 5000 : ℝ)) / 2 ≤ B.yu := by
    dsimp only [Box.CoversOriginal] at hB
    exact_mod_cast hB
  intro x hx
  have hx0 := mem_logPrimeBox.mp hx.1 (0 : Fin 2)
  have hr := hx.2
  change x 0 < 1 / 3 ∧ 1 / 3 ≤ x 1 ∧ x 0 + 2 * x 1 < 1 at hr
  apply Box.mem_region.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hBr.1.trans hx0.1
  · exact hr.1.le.trans hBr.2.1
  · exact hBr.2.2.1.trans hr.2.1
  · linarith only [hx0.1, hr.2.2, hBr.2.2.2]

/-- An actual coarse rectangle. This is not the adopted fine-cell table. -/
def coarseBox : Box := ⟨417 / 5000, 1 / 3, 1 / 3, 4583 / 10000⟩

theorem coarseBox_valid : coarseBox.Valid := by norm_num [Box.Valid, coarseBox]
theorem coarseBox_covers : coarseBox.CoversOriginal := by
  norm_num [Box.CoversOriginal, coarseBox]

theorem eighthIntegral_le_coarse_rational :
    currentChenUpsilon8HarmonicIntegral ≤ ((coarseBox.upper * coarseBox.area : ℚ) : ℝ) := by
  have hcover : ∀ x ∈ eighthDomain, ∃ i ∈ ({()} : Finset Unit), x ∈ coarseBox.region := by
    intro x hx
    exact ⟨(), by simp, Box.coversOriginal_sound coarseBox_covers hx⟩
  simpa using eighthIntegral_le_box_cover ({()} : Finset Unit) (fun _ => coarseBox)
    (fun _ _ => coarseBox_valid) hcover

end

end ImbalancedChen.P2U8DirectedBoxEnclosure
