import ImbalancedChen.P2GuardedReciprocalRounding
import ImbalancedChen.P2NegativeDomainCover
import ImbalancedChen.LogPrimeBoxIntegral

/-!
# U8 box bounds with exact reciprocal-prime log mass

SOURCE ONLY / UNCOMPILED.  Sibling draft modules must be on the source
search path.  The full half-open box is charged, including cells crossing
an original U8 affine wall.  Only the residual reciprocal is capped;
both prime-coordinate reciprocals are integrated exactly by the existing
`integral_logPrimeBox_const_mul_one_div` theorem.  Thus the analytic charge
is `residualCap * log(xU/xL) * log(yU/yL)`, not area times the full
pointwise density cap.  Checked rational log certificates and Q80 outward
rounding then supply a finite rational upper endpoint.

No adopted cell table, final upper endpoint, or box integral inequality is
assumed.  A finite cover must still supply actual geometric coverage.
-/

namespace ImbalancedChen.P2WeightedBoxLogCertificate

open MeasureTheory Set
open scoped BigOperators
open Classical
open Certificates.P2DirectedLogRounding
open P2NegativeDomainCover

abbrev Point := Fin 2 → ℝ

structure WeightedBox where
  xl : ℚ
  xu : ℚ
  yl : ℚ
  yu : ℚ
  deriving DecidableEq, Repr

def WeightedBox.Valid (B : WeightedBox) : Prop :=
  0 < B.xl ∧ B.xl ≤ B.xu ∧ 0 < B.yl ∧ B.yl ≤ B.yu ∧ B.xu + B.yu < 1

instance (B : WeightedBox) : Decidable B.Valid := by
  unfold WeightedBox.Valid
  infer_instance

noncomputable def WeightedBox.lo (B : WeightedBox) : Point := ![(B.xl : ℝ), (B.yl : ℝ)]
noncomputable def WeightedBox.hi (B : WeightedBox) : Point := ![(B.xu : ℝ), (B.yu : ℝ)]

noncomputable def WeightedBox.region (B : WeightedBox) : Set Point := logPrimeBox B.lo B.hi

def WeightedBox.residualBox (B : WeightedBox) : Enclosure :=
  ⟨1 - B.xu - B.yu, 1 - B.xl - B.yl⟩

def WeightedBox.residualCap (B : WeightedBox) : ℚ := 1 / (1 - B.xu - B.yu)

noncomputable def WeightedBox.logMass (B : WeightedBox) : ℝ :=
  Real.log ((B.xu : ℝ) / B.xl) * Real.log ((B.yu : ℝ) / B.yl)

theorem WeightedBox.real_guards (B : WeightedBox) (hB : B.Valid) :
    0 < (B.xl : ℝ) ∧ (B.xl : ℝ) ≤ B.xu ∧
      0 < (B.yl : ℝ) ∧ (B.yl : ℝ) ≤ B.yu ∧ (B.xu : ℝ) + B.yu < 1 := by
  dsimp only [WeightedBox.Valid] at hB
  exact_mod_cast hB

theorem WeightedBox.lo_pos (B : WeightedBox) (hB : B.Valid) (i : Fin 2) :
    0 < B.lo i := by
  obtain ⟨hx, _, hy, _, _⟩ := B.real_guards hB
  fin_cases i
  · exact hx
  · exact hy

theorem WeightedBox.lo_le_hi (B : WeightedBox) (hB : B.Valid) (i : Fin 2) :
    B.lo i ≤ B.hi i := by
  obtain ⟨_, hx, _, hy, _⟩ := B.real_guards hB
  fin_cases i
  · exact hx
  · exact hy

theorem WeightedBox.mem_region {B : WeightedBox} {x : Point} :
    x ∈ B.region ↔
      (B.xl : ℝ) ≤ x 0 ∧ x 0 < B.xu ∧ (B.yl : ℝ) ≤ x 1 ∧ x 1 < B.yu := by
  constructor
  · intro hx
    have h := mem_logPrimeBox.mp hx
    exact ⟨(h 0).1, (h 0).2, (h 1).1, (h 1).2⟩
  · rintro ⟨hxl, hxu, hyl, hyu⟩
    apply mem_logPrimeBox.mpr
    intro i
    fin_cases i
    · exact ⟨hxl, hxu⟩
    · exact ⟨hyl, hyu⟩

theorem WeightedBox.measurable_region (B : WeightedBox) : MeasurableSet B.region :=
  measurableSet_logPrimeBox B.lo B.hi

/-- The positive residual branch is certified by the signed reciprocal
checker; neither a zero-crossing nor an entirely negative residual passes. -/
theorem WeightedBox.residual_guard (B : WeightedBox) (hB : B.Valid) :
    B.residualBox.reciprocalCheck = true ∧ 0 < B.residualBox.lower := by
  rcases hB with ⟨_, hxx, _, hyy, hsum⟩
  have hl : 0 < B.residualBox.lower := by
    dsimp [WeightedBox.residualBox]
    linarith
  have hv : B.residualBox.ReciprocalValid := by
    constructor
    · dsimp [WeightedBox.residualBox]
      linarith
    · exact Or.inl hl
  exact ⟨by simp [Enclosure.reciprocalCheck, hv], hl⟩

theorem WeightedBox.residualCap_nonneg (B : WeightedBox) (hB : B.Valid) :
    0 ≤ (B.residualCap : ℝ) := by
  have hgap : (0 : ℚ) < 1 - B.xu - B.yu := (B.residual_guard hB).2
  have hq : 0 ≤ B.residualCap := (one_div_pos.mpr hgap).le
  exact_mod_cast hq

theorem WeightedBox.region_subset_closed (B : WeightedBox) :
    B.region ⊆ Icc B.lo B.hi := by
  intro x hx
  have h := mem_logPrimeBox.mp hx
  exact ⟨fun i => (h i).1, fun i => (h i).2.le⟩

theorem density_eq_reciprocal (x : Point) :
    eighthDensity x = 1 / (x 0 * x 1 * (1 - x 0 - x 1)) := by
  simp only [eighthDensity, Fin.prod_univ_two, one_div, mul_inv_rev]
  ring

theorem WeightedBox.density_nonneg (B : WeightedBox) (hB : B.Valid)
    {x : Point} (hx : x ∈ B.region) : 0 ≤ eighthDensity x := by
  obtain ⟨ha, _, hc, _, hsum⟩ := B.real_guards hB
  obtain ⟨hax, hxb, hcy, hyd⟩ := WeightedBox.mem_region.mp hx
  have hxpos : 0 < x 0 := ha.trans_le hax
  have hypos : 0 < x 1 := hc.trans_le hcy
  have hgap : 0 < 1 - x 0 - x 1 := by linarith
  rw [density_eq_reciprocal]
  exact (one_div_pos.mpr (mul_pos (mul_pos hxpos hypos) hgap)).le

theorem WeightedBox.integrable_density (B : WeightedBox) (hB : B.Valid) :
    IntegrableOn eighthDensity B.region := by
  have hcontinuous : ContinuousOn eighthDensity (Icc B.lo B.hi) := by
    simp_rw [density_eq_reciprocal]
    apply continuousOn_const.div (by fun_prop)
    intro x hx
    have hax : (B.xl : ℝ) ≤ x 0 := hx.1 0
    have hxb : x 0 ≤ (B.xu : ℝ) := hx.2 0
    have hcy : (B.yl : ℝ) ≤ x 1 := hx.1 1
    have hyd : x 1 ≤ (B.yu : ℝ) := hx.2 1
    obtain ⟨ha, _, hc, _, hsum⟩ := B.real_guards hB
    have hxpos : 0 < x 0 := ha.trans_le hax
    have hypos : 0 < x 1 := hc.trans_le hcy
    have hgap : 0 < 1 - x 0 - x 1 := by linarith
    exact (mul_pos (mul_pos hxpos hypos) hgap).ne'
  exact (hcontinuous.integrableOn_compact isCompact_Icc).mono_set B.region_subset_closed

theorem WeightedBox.primeWeight_nonneg (B : WeightedBox) (hB : B.Valid)
    {x : Point} (hx : x ∈ B.region) : 0 ≤ ∏ i, 1 / x i := by
  apply Finset.prod_nonneg
  intro i _
  exact one_div_nonneg.mpr ((B.lo_pos hB i).trans_le (mem_logPrimeBox.mp hx i).1).le

/-- The cap bounds only the residual.  The original two reciprocal-prime
weights remain present in the pointwise majorant. -/
theorem WeightedBox.density_le_weightedCap (B : WeightedBox) (hB : B.Valid)
    {x : Point} (hx : x ∈ B.region) :
    eighthDensity x ≤ (B.residualCap : ℝ) * ∏ i, 1 / x i := by
  obtain ⟨_, _, _, _, hsum⟩ := B.real_guards hB
  obtain ⟨_, hxb, _, hyd⟩ := WeightedBox.mem_region.mp hx
  have hgap : 0 < 1 - (B.xu : ℝ) - B.yu := by linarith
  have hle : 1 - (B.xu : ℝ) - B.yu ≤ 1 - x 0 - x 1 := by linarith
  have hr : 1 / (1 - x 0 - x 1) ≤ (B.residualCap : ℝ) := by
    simpa only [WeightedBox.residualCap, Rat.cast_div, Rat.cast_one, Rat.cast_sub] using
      one_div_le_one_div_of_le hgap hle
  exact mul_le_mul_of_nonneg_right hr (B.primeWeight_nonneg hB hx)

/-- Exact reciprocal-prime mass of the actual half-open box. -/
theorem WeightedBox.integral_primeWeight (B : WeightedBox) (hB : B.Valid) :
    (∫ x in B.region, ∏ i, 1 / x i) = B.logMass := by
  rw [WeightedBox.region, integral_logPrimeBox_one_div B.lo B.hi
    (B.lo_pos hB) (B.lo_le_hi hB)]
  simp only [WeightedBox.logMass, Fin.prod_univ_two, WeightedBox.lo, WeightedBox.hi,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The weighted majorant is evaluated by the actual product integral
identity, rather than by separately capped coordinate reciprocals. -/
theorem WeightedBox.integral_weightedCap (B : WeightedBox) (hB : B.Valid) :
    (∫ x in B.region, (B.residualCap : ℝ) * ∏ i, 1 / x i) =
      (B.residualCap : ℝ) * B.logMass := by
  rw [WeightedBox.region, integral_logPrimeBox_const_mul_one_div (B.residualCap : ℝ)
    B.lo B.hi (B.lo_pos hB) (B.lo_le_hi hB)]
  simp only [WeightedBox.logMass, Fin.prod_univ_two, WeightedBox.lo, WeightedBox.hi,
    Matrix.cons_val_zero, Matrix.cons_val_one]

theorem WeightedBox.integral_density_le_logMass (B : WeightedBox) (hB : B.Valid) :
    (∫ x in B.region, eighthDensity x) ≤ (B.residualCap : ℝ) * B.logMass := by
  rw [← B.integral_weightedCap hB]
  exact setIntegral_mono_on (B.integrable_density hB)
    (integrableOn_logPrimeBox_const_mul_one_div (B.residualCap : ℝ) B.lo B.hi (B.lo_pos hB))
    B.measurable_region (fun x hx => B.density_le_weightedCap hB hx)

/-- The full-density rectangular cap, retained only for comparing accuracy. -/
def WeightedBox.areaDensityCap (B : WeightedBox) : ℚ :=
  B.residualCap * (B.xu - B.xl) * (B.yu - B.yl) / (B.xl * B.yl)

private theorem log_ratio_upper {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) :
    Real.log (u / l) ≤ (u - l) / l := by
  calc
    Real.log (u / l) ≤ u / l - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hl.trans_le hlu) hl)
    _ = (u - l) / l := by field_simp [ne_of_gt hl] <;> ring

private theorem log_ratio_nonneg {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) :
    0 ≤ Real.log (u / l) := by
  apply Real.log_nonneg
  apply (le_div_iff₀ hl).mpr
  simpa only [one_mul] using hlu

/-- Exact log mass always improves or equals the full pointwise-density
cap integrated against ordinary rectangular area. -/
theorem WeightedBox.logMass_bound_le_areaDensityCap (B : WeightedBox) (hB : B.Valid) :
    (B.residualCap : ℝ) * B.logMass ≤ (B.areaDensityCap : ℝ) := by
  obtain ⟨ha, hab, hc, hcd, _⟩ := B.real_guards hB
  have hprod := mul_le_mul (log_ratio_upper ha hab) (log_ratio_upper hc hcd)
    (log_ratio_nonneg hc hcd) (div_nonneg (sub_nonneg.mpr hab) ha.le)
  calc
    (B.residualCap : ℝ) * B.logMass ≤
        (B.residualCap : ℝ) *
          (((B.xu : ℝ) - B.xl) / B.xl * (((B.yu : ℝ) - B.yl) / B.yl)) :=
      mul_le_mul_of_nonneg_left hprod (B.residualCap_nonneg hB)
    _ = (B.areaDensityCap : ℝ) := by
      simp only [WeightedBox.areaDensityCap, Rat.cast_div, Rat.cast_mul, Rat.cast_sub,
        div_eq_mul_inv, mul_inv_rev]
      ring

/-- Strict improvement before outward numerical rounding on every box
with positive width in both prime coordinates. -/
theorem WeightedBox.logMass_bound_lt_areaDensityCap (B : WeightedBox) (hB : B.Valid)
    (hx : B.xl < B.xu) (hy : B.yl < B.yu) :
    (B.residualCap : ℝ) * B.logMass < (B.areaDensityCap : ℝ) := by
  obtain ⟨ha, hab, hc, hcd, hsum⟩ := B.real_guards hB
  have hxR : (B.xl : ℝ) < B.xu := by exact_mod_cast hx
  have hyR : (B.yl : ℝ) < B.yu := by exact_mod_cast hy
  have hxr : (1 : ℝ) < (B.xu : ℝ) / B.xl := by
    apply (lt_div_iff₀ ha).mpr
    simpa only [one_mul] using hxR
  have hyr : (1 : ℝ) < (B.yu : ℝ) / B.yl := by
    apply (lt_div_iff₀ hc).mpr
    simpa only [one_mul] using hyR
  have hxlog : Real.log ((B.xu : ℝ) / B.xl) < ((B.xu : ℝ) - B.xl) / B.xl := by
    calc
      Real.log ((B.xu : ℝ) / B.xl) < (B.xu : ℝ) / B.xl - 1 :=
        Real.log_lt_sub_one_of_pos (div_pos (ha.trans_le hab) ha) (ne_of_gt hxr)
      _ = ((B.xu : ℝ) - B.xl) / B.xl := by field_simp [ne_of_gt ha] <;> ring
  have hprod := (mul_lt_mul_of_pos_right hxlog (Real.log_pos hyr)).trans_le
    (mul_le_mul_of_nonneg_left (log_ratio_upper hc hcd)
      (div_nonneg (sub_nonneg.mpr hab) ha.le))
  have hcap : (0 : ℝ) < (B.residualCap : ℝ) := by
    simp only [WeightedBox.residualCap, Rat.cast_div, Rat.cast_one, Rat.cast_sub]
    apply one_div_pos.mpr
    linarith
  calc
    (B.residualCap : ℝ) * B.logMass <
        (B.residualCap : ℝ) *
          (((B.xu : ℝ) - B.xl) / B.xl * (((B.yu : ℝ) - B.yl) / B.yl)) :=
      mul_lt_mul_of_pos_left hprod hcap
    _ = (B.areaDensityCap : ℝ) := by
      simp only [WeightedBox.areaDensityCap, Rat.cast_div, Rat.cast_mul, Rat.cast_sub,
        div_eq_mul_inv, mul_inv_rev]
      ring

/-- Boundary-safe version: a cell can cross any original U8 wall.  Its
entire positive box is charged; no clipped-domain integral is assumed. -/
theorem WeightedBox.integral_u8_piece_le_logMass (B : WeightedBox) (hB : B.Valid) :
    (∫ x in B.region ∩ eighthDomain, eighthDensity x) ≤
      (B.residualCap : ℝ) * B.logMass := by
  apply le_trans ?_ (B.integral_density_le_logMass hB)
  apply setIntegral_mono_set (B.integrable_density hB)
  · filter_upwards [ae_restrict_mem B.measurable_region] with x hx
    exact B.density_nonneg hB hx
  · exact Filter.Eventually.of_forall (fun _ hx => hx.1)

structure Certificate where
  box : WeightedBox
  logX : Certificates.RationalLogCertificate
  logY : Certificates.RationalLogCertificate
  deriving DecidableEq, Repr

def Certificate.Valid (c : Certificate) : Prop :=
  c.box.Valid ∧ c.logX.argument = c.box.xu / c.box.xl ∧
    c.logY.argument = c.box.yu / c.box.yl ∧ c.logX.check = true ∧ c.logY.check = true

instance (c : Certificate) : Decidable c.Valid := by
  unfold Certificate.Valid
  infer_instance

def Certificate.check (c : Certificate) : Bool := decide c.Valid

def Certificate.expr (c : Certificate) : Expr :=
  .mul (.rational c.box.residualCap) (.mul (.logarithm c.logX) (.logarithm c.logY))

def Certificate.upper (c : Certificate) : ℚ := (c.expr.enclosure.round 80).upper

theorem Certificate.checked_logMass_upper (c : Certificate) (hc : c.check = true) :
    (c.box.residualCap : ℝ) * c.box.logMass ≤ (c.upper : ℝ) := by
  have hv : c.Valid := of_decide_eq_true hc
  rcases hv with ⟨_, hxarg, hyarg, hx, hy⟩
  have he : c.expr.Valid := by simp [Certificate.expr, Expr.Valid, hx, hy]
  have h := (Expr.q80_sound c.expr he).2
  simpa only [Certificate.upper, Certificate.expr, Expr.eval, WeightedBox.logMass,
    hxarg, hyarg, Rat.cast_div] using h

/-- Acceptance consists solely of rational geometric guards, ratio
identities and the two proved rational log checks. -/
theorem Certificate.check_sound (c : Certificate) (hc : c.check = true) :
    (∫ x in c.box.region, eighthDensity x) ≤ (c.upper : ℝ) := by
  have hv : c.Valid := of_decide_eq_true hc
  exact (c.box.integral_density_le_logMass hv.1).trans (c.checked_logMass_upper hc)

theorem Certificate.boundary_piece_sound (c : Certificate) (hc : c.check = true) :
    (∫ x in c.box.region ∩ eighthDomain, eighthDensity x) ≤ (c.upper : ℝ) := by
  have hv : c.Valid := of_decide_eq_true hc
  exact (c.box.integral_u8_piece_le_logMass hv.1).trans (c.checked_logMass_upper hc)

/-- Optional rational quality gate: the fully rounded certificate itself,
including its chosen log truncations, must beat the rectangular-area cap. -/
def Certificate.improvesAreaCheck (c : Certificate) : Bool :=
  c.check && decide (c.upper < c.box.areaDensityCap)

theorem Certificate.improvesAreaCheck_sound (c : Certificate)
    (hc : c.improvesAreaCheck = true) :
    (∫ x in c.box.region, eighthDensity x) ≤ (c.upper : ℝ) ∧
      (c.upper : ℝ) < (c.box.areaDensityCap : ℝ) := by
  have hp : c.check = true ∧ c.upper < c.box.areaDensityCap := by
    simpa only [Certificate.improvesAreaCheck, Bool.and_eq_true, decide_eq_true_eq] using hc
  exact ⟨c.check_sound hp.1, by exact_mod_cast hp.2⟩

noncomputable def WeightedBox.majorant (B : WeightedBox) : Point → ℝ :=
  B.region.indicator (fun x => (B.residualCap : ℝ) * ∏ i, 1 / x i)

theorem WeightedBox.majorant_nonneg (B : WeightedBox) (hB : B.Valid) (x : Point) :
    0 ≤ B.majorant x := by
  by_cases hx : x ∈ B.region
  · rw [WeightedBox.majorant, indicator_of_mem hx]
    exact mul_nonneg (B.residualCap_nonneg hB) (B.primeWeight_nonneg hB hx)
  · simp only [WeightedBox.majorant, indicator_of_notMem hx, le_refl]

theorem WeightedBox.integrable_majorant (B : WeightedBox) (hB : B.Valid) :
    Integrable B.majorant := by
  exact (integrableOn_logPrimeBox_const_mul_one_div (B.residualCap : ℝ)
    B.lo B.hi (B.lo_pos hB)).integrable_indicator B.measurable_region

theorem WeightedBox.integral_majorant (B : WeightedBox) (hB : B.Valid) :
    (∫ x, B.majorant x) = (B.residualCap : ℝ) * B.logMass := by
  rw [WeightedBox.majorant, integral_indicator B.measurable_region]
  exact B.integral_weightedCap hB

theorem integrableOn_original_density : IntegrableOn eighthDensity eighthDomain := by
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

/-- Complete finite-cover upper certificate for the literal original U8
integral.  Overlap is allowed and every boundary box pays its full weighted
mass.  No disjointness or assertion that boxes lie inside U8 is required. -/
theorem original_u8_le_checked_weighted_cover {ι : Type*} (s : Finset ι)
    (c : ι → Certificate) (hchecks : ∀ i ∈ s, (c i).check = true)
    (hcover : ∀ x ∈ eighthDomain, ∃ i ∈ s, x ∈ (c i).box.region) :
    currentChenUpsilon8HarmonicIntegral ≤ ((∑ i ∈ s, (c i).upper : ℚ) : ℝ) := by
  have hvalid (i) (hi : i ∈ s) : (c i).box.Valid :=
    (show (c i).Valid from of_decide_eq_true (hchecks i hi)).1
  have hf : Integrable (eighthDomain.indicator eighthDensity) :=
    integrableOn_original_density.integrable_indicator measurableSet_eighthDomain
  have hg : Integrable (fun x => ∑ i ∈ s, (c i).box.majorant x) :=
    integrable_finsetSum s (fun i hi => (c i).box.integrable_majorant (hvalid i hi))
  have hp (x : Point) : eighthDomain.indicator eighthDensity x ≤
      ∑ i ∈ s, (c i).box.majorant x := by
    by_cases hx : x ∈ eighthDomain
    · obtain ⟨i, hi, hix⟩ := hcover x hx
      rw [indicator_of_mem hx]
      calc
        eighthDensity x ≤ ((c i).box.residualCap : ℝ) * ∏ j, 1 / x j :=
          (c i).box.density_le_weightedCap (hvalid i hi) hix
        _ = (c i).box.majorant x := (indicator_of_mem hix _).symm
        _ ≤ _ := Finset.single_le_sum
          (fun j hj => (c j).box.majorant_nonneg (hvalid j hj) x) hi
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun i hi => (c i).box.majorant_nonneg (hvalid i hi) x)
  calc
    currentChenUpsilon8HarmonicIntegral =
        ∫ x, eighthDomain.indicator eighthDensity x :=
      (integral_indicator measurableSet_eighthDomain).symm
    _ ≤ ∫ x, ∑ i ∈ s, (c i).box.majorant x := integral_mono hf hg hp
    _ = ∑ i ∈ s, ∫ x, (c i).box.majorant x :=
      integral_finsetSum s (fun i hi => (c i).box.integrable_majorant (hvalid i hi))
    _ = ∑ i ∈ s, ((c i).box.residualCap : ℝ) * (c i).box.logMass := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (c i).box.integral_majorant (hvalid i hi)
    _ ≤ ∑ i ∈ s, ((c i).upper : ℝ) :=
      Finset.sum_le_sum (fun i hi => (c i).checked_logMass_upper (hchecks i hi))
    _ = _ := by push_cast

end ImbalancedChen.P2WeightedBoxLogCertificate
