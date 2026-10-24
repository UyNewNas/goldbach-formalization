import ImbalancedChen.ActualThirdOriginalSymmetricMassCeil
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / OPEN30.
Proposed installation: ImbalancedChen.P4ASymmetricNewOnlyLeaf.

The original mean_upper Python branch returns `out` when high<=2, BEFORE
computing the symmetric OLD max moment, OLD weight or endpoint chord.
This module proves the actual full symmetric leaf bound for that branch.
The OLD factor is only dropped using its proved nonnegativity. NEW Jensen
uses the actual ordered-prism probability and existing exact affine mean.
No OLD chord/range/span/mean or target integral bound is an input.

Factor4 is retained in prismWeight/prismMass. The original half mass and
integer UP are reused from literalSymmetricMass/literalSymmetricUpper;
there is exactly ONE /2, already inside literalSymmetricMass.
-/

namespace ImbalancedChen.P4ASymmetricNewOnlyLeafSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalThirdBoxMomentsSourceOnly OriginalThirdTriangleMomentsSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdSymmetricJensenSourceOnly OriginalThirdClippedChordSourceOnly
open OriginalThirdRoundedNewSourceOnly OriginalThirdPositiveLogSourceOnly
open OriginalThirdRoundedOldWeightSourceOnly OriginalThirdIntegerGuardedLeafSourceOnly
open OriginalThirdSymmetricMassCeilSourceOnly

theorem symmetric_positive_coordinates {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) : 0 < a ∧ 0 < c := by
  have hc : 0 < c := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/100) hg.cutoff
  exact ⟨hc.trans_le (hg.width_z.le.trans hg.z_below_xy), hc⟩

theorem symmetric_prismMass_pos {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) : 0 < prismMass a b c d := by
  have hp := symmetric_positive_coordinates hg
  exact mul_pos (mul_pos (by norm_num) (triangleMass_pos hp.1 hg.width_xy))
    (div_pos (sub_pos.mpr hg.width_z) (mul_pos hp.2 (hp.2.trans hg.width_z)))

theorem symmetric_prism_ae_mem (a b c d : ℝ) :
    ∀ᵐ p ∂prismProbability a b c d, p ∈ prismRegion a b c d := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem ((measurableSet_xyTriangle a b).prod measurableSet_Icc))

/-- Every measurable argument has integrable actual sieve factor under a
finite measure, by the already proved global normalization bound. -/
theorem actual_factor_integrable_of_measurable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {q : α → ℝ} (hq : Measurable q) :
    Integrable (fun p => actualExtendedThirdLowerFactor (q p)) μ := by
  apply Integrable.of_bound
    (measurable_actualExtendedThirdLowerFactor.comp hq).aestronglyMeasurable
    (1 / (2 * Real.exp Real.eulerMascheroniConstant))
  exact Filter.Eventually.of_forall (fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (actualExtendedThirdLowerFactor_nonneg _)]
    exact actualExtendedThirdLowerFactor_le_normalization _)

theorem measurable_actualPrismOld : Measurable actualPrismOld := by
  have hm : Measurable (prismPoint : PrismPoint → Fin 3 → ℝ) := by
    apply measurable_pi_iff.2
    intro i
    fin_cases i
    · exact measurable_fst.fst
    · exact measurable_fst.snd
    · exact measurable_snd
  have hcap := (measurable_actualExtendedThirdBufferedCap 0).comp hm
  exact (((hcap.sub measurable_fst.fst).sub measurable_fst.snd).sub
    measurable_snd).div measurable_snd

/-- NEW support and a boundedness estimate are derived from full raw-domain
geometry. The second component supplies integrability of the argument. -/
theorem symmetric_new_argument_range {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) {p : PrismPoint}
    (hp : p ∈ prismRegion a b c d) :
    2 ≤ prismAffine thirdPrefixTheta (-1) (-1) (-1) p ∧
      prismAffine thirdPrefixTheta (-1) (-1) (-1) p ≤ thirdPrefixTheta / c := by
  have hpos := symmetric_positive_coordinates hg
  have hx : 0 < p.1.1 := hpos.1.trans_le hp.1.1.1.1
  have hy : 0 < p.1.2 := hpos.1.trans_le hp.1.1.2.1
  have hz : 0 < p.2 := hpos.2.trans_le hp.2.1
  have hraw : p.1.1 + p.1.2 + 3*p.2 ≤ thirdPrefixTheta := by
    linarith [hp.1.1.1.2, hp.1.1.2.2, hp.2.2, hg.raw_full]
  have hlow : 3 ≤ (thirdPrefixTheta-p.1.1-p.1.2)/p.2 :=
    (le_div_iff₀ hz).mpr (by linarith)
  have htheta : 0 ≤ thirdPrefixTheta / c := by
    exact div_nonneg (by norm_num [thirdPrefixTheta]) hpos.2.le
  have hscale : thirdPrefixTheta ≤ (thirdPrefixTheta / c)*p.2 := by
    calc
      thirdPrefixTheta = (thirdPrefixTheta / c)*c := by field_simp [hpos.2.ne']
      _ ≤ (thirdPrefixTheta / c)*p.2 := mul_le_mul_of_nonneg_left hp.2.1 htheta
  have hhigh : (thirdPrefixTheta-p.1.1-p.1.2)/p.2 ≤ thirdPrefixTheta/c :=
    (div_le_iff₀ hz).mpr (by linarith)
  simp only [prismAffine, neg_one_mul, ← sub_eq_add_neg]
  constructor <;> linarith

/-- Genuine NEW-only Jensen on the original ordered triangle probability.
This does not invoke any OLD chord or assume equality of OLD/NEW means. -/
theorem symmetric_prism_new_only_mean_upper {a b c d out : ℝ}
    (hg : SymmetricFullBox a b c d)
    (hout : actualExtendedThirdLowerFactor (newMean a b c d) ≤ out) :
    (∫ p, actualExtendedThirdLowerFactor
        (prismAffine thirdPrefixTheta (-1) (-1) (-1) p) -
      actualExtendedThirdLowerFactor (actualPrismOld p) ∂prismProbability a b c d) ≤ out := by
  have hp := symmetric_positive_coordinates hg
  letI := prismProbability_isProbability hp.1 hg.width_xy hp.2 hg.width_z
  have hm : Measurable (prismAffine thirdPrefixTheta (-1) (-1) (-1)) := by
    unfold prismAffine
    fun_prop
  have hi : Integrable (prismAffine thirdPrefixTheta (-1) (-1) (-1))
      (prismProbability a b c d) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (thirdPrefixTheta / c)
    filter_upwards [symmetric_prism_ae_mem a b c d] with p h
    have hr := symmetric_new_argument_range hg h
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hr.1])]
    exact hr.2
  have hfn := actual_factor_integrable_of_measurable (prismProbability a b c d) hm
  have hfo := actual_factor_integrable_of_measurable (prismProbability a b c d)
    measurable_actualPrismOld
  have hrange : ∀ᵐ p ∂prismProbability a b c d,
      2 ≤ prismAffine thirdPrefixTheta (-1) (-1) (-1) p := by
    filter_upwards [symmetric_prism_ae_mem a b c d] with p h
    exact (symmetric_new_argument_range hg h).1
  have hJ := actual_lower_Jensen_probability (prismProbability a b c d)
    (prismAffine thirdPrefixTheta (-1) (-1) (-1)) hrange hi hfn
  rw [prism_affine_mean hg] at hJ
  have hmean : (thirdPrefixTheta+(-1)*maxMean a b+(-1)*minMean a b)*invZMean c d+(-1) =
      newMean a b c d := by unfold newMean minMean; ring
  rw [hmean] at hJ
  calc
    _ ≤ ∫ p, actualExtendedThirdLowerFactor
        (prismAffine thirdPrefixTheta (-1) (-1) (-1) p) ∂prismProbability a b c d := by
      exact integral_mono (hfn.sub hfo) hfn
        (fun p => sub_le_self _ (actualExtendedThirdLowerFactor_nonneg _))
    _ ≤ out := hJ.trans hout

/-- Remove the true ordered-prism probability denominator with the actual
kernel identity. Factor4 remains inside the original reciprocal mass. -/
theorem symmetric_prism_new_only_integral_upper {a b c d out : ℝ}
    (hg : SymmetricFullBox a b c d)
    (hout : actualExtendedThirdLowerFactor (newMean a b c d) ≤ out) :
    (∫ p in prismRegion a b c d, compactKernel (prismPoint p)) ≤
      prismMass a b c d * out := by
  have hp := symmetric_positive_coordinates hg
  let g : PrismPoint → ℝ := fun p => actualExtendedThirdLowerFactor
      (prismAffine thirdPrefixTheta (-1) (-1) (-1) p) -
    actualExtendedThirdLowerFactor (actualPrismOld p)
  have heq : (∫ p in prismRegion a b c d, compactKernel (prismPoint p)) =
      ∫ p in prismRegion a b c d, prismWeight p*g p := by
    apply setIntegral_congr_fun ((measurableSet_xyTriangle a b).prod measurableSet_Icc)
    intro p h
    have hz := (hp.2.trans_le h.2.1).ne'
    have ha : (thirdPrefixTheta-2*0-p.1.1-p.1.2-p.2)/p.2 =
        prismAffine thirdPrefixTheta (-1) (-1) (-1) p := by
      unfold prismAffine
      field_simp [hz] <;> ring
    simp only [compactKernel, prismPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, actualExtendedThirdOrderedKernel]
    rw [ha]
    change 4*g p/(p.1.1*p.1.2*p.2^2) = prismWeight p*g p
    simp only [prismWeight, xyWeight, div_eq_mul_inv, mul_inv_rev]
    ring
  have hmean := symmetric_prism_new_only_mean_upper hg hout
  have hprob := integral_prismProbability hp.1 hg.width_xy hp.2 hg.width_z g
  rw [heq, ← (eq_div_iff (symmetric_prismMass_pos hg).ne').mp hprob]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_right hmean (symmetric_prismMass_pos hg).le

theorem original_symmetric_new_only_leaf_upper {a b c d out : ℝ}
    (hg : SymmetricFullBox a b c d)
    (hout : actualExtendedThirdLowerFactor (newMean a b c d) ≤ out) :
    (∫ t in compactRegion ∩ symmetricBox a b c d, compactKernel t) ≤
      prismMass a b c d * out := by
  rw [compact_inter_symmetricBox a b c d hg, ← prism_actual_integral_eq_ordered]
  exact symmetric_prism_new_only_integral_upper hg hout

/-- Original NEW interval operations, true triangle Jensen, literal mass.hi
including its ONE /2, and final UP. No OLD query/chord/mean premise. -/
theorem original_stored_symmetric_new_only_integer_upper
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (out : ℤ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : VariableEnvelope.mu ≤ (a:ℝ))
    (hquery : actualExtendedThirdLowerFactor
      (symmetricNewQuery (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)
        (originalLnUnit ((b:ℝ)/(a:ℝ))):ℝ) ≤ value out) :
    (∫ t in compactRegion ∩ symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ), compactKernel t) ≤
      value (literalSymmetricUpper x0 x1 z0 z1 out) := by
  have hmuScalar : (25:ℝ)/128 ≤ (a:ℝ) := by simpa only [VariableEnvelope.mu] using hmu
  have hrhoScalar : (b:ℝ) ≤ (19:ℝ)/96 := by simpa only [thirdPrefixRho] using hg.upper_rho
  have hguards := original_stored_above_mu_log_guards x0 x1 a b ha hb
    hg.width_xy hmuScalar hrhoScalar
  have hlog := original_above_mu_log_sound hg.width_xy hmuScalar hrhoScalar
  have hout := actual_new_factor_upper_of_original_query hlog hguards.1 hquery
  have hout0 : 0 ≤ value out := (actualExtendedThirdLowerFactor_nonneg _).trans hout
  have hmass := (literal_symmetric_mass_encloses x0 x1 z0 z1 a b c d
    ha hb hc hd hg hmu).2
  calc
    _ ≤ prismMass (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)*value out :=
      original_symmetric_new_only_leaf_upper hg hout
    _ ≤ value (literalSymmetricMass x0 x1 z0 z1).hi*value out :=
      mul_le_mul_of_nonneg_right hmass hout0
    _ = value out*value (literalSymmetricMass x0 x1 z0 z1).hi := by ring
    _ ≤ value (literalSymmetricUpper x0 x1 z0 z1 out) := literal_product_UP_ge _ _

/-- Literal high numerator for the original above-mu minorant
(57,-96,0,0,64), with y0=x0 in the symmetric branch. -/
def literalSymmetricOldHigh (x0 z0 : ℤ) : ℚ :=
  ((57*(48000*2^24)-160*x0-64*x0-64*z0 : ℤ) : ℚ) /
    ((64*z0 : ℤ) : ℚ)

theorem literalSymmetricOldHigh_eq_oldHighQ
    (x0 z0 : ℤ) (a c : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ)) (hcpos : 0 < c) :
    literalSymmetricOldHigh x0 z0 = oldHighQ a c := by
  have hz : (z0 : ℚ) ≠ 0 := by
    intro hzero
    have hc0 : c = 0 := by rw [hc, hzero]; simp
    linarith
  unfold literalSymmetricOldHigh oldHighQ
  rw [ha, hc]
  push_cast
  field_simp [hz] <;> ring

/-- The exact `if high<=2:return out` suffix after the original eligibility
checks and NEW query. The continuing result is left untouched. This does
not purport to redefine minorant selection or the whole box dispatcher. -/
def literalSymmetricMeanHighDispatch (x0 z0 : ℤ) (out continuing : ℤ) : ℤ :=
  if literalSymmetricOldHigh x0 z0 ≤ 2 then out else continuing

theorem literalSymmetricMeanHighDispatch_early {x0 z0 : ℤ} (out continuing : ℤ)
    (hhigh : literalSymmetricOldHigh x0 z0 ≤ 2) :
    literalSymmetricMeanHighDispatch x0 z0 out continuing = out := by
  exact if_pos hhigh

theorem original_stored_symmetric_high_le_two_integer_upper
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (out continuing : ℤ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : VariableEnvelope.mu ≤ (a:ℝ)) (hhigh : literalSymmetricOldHigh x0 z0 ≤ 2)
    (hquery : actualExtendedThirdLowerFactor
      (symmetricNewQuery (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)
        (originalLnUnit ((b:ℝ)/(a:ℝ))):ℝ) ≤ value out) :
    (∫ t in compactRegion ∩ symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ), compactKernel t) ≤
      value (literalSymmetricUpper x0 x1 z0 z1
        (literalSymmetricMeanHighDispatch x0 z0 out continuing)) := by
  rw [literalSymmetricMeanHighDispatch_early out continuing hhigh]
  exact original_stored_symmetric_new_only_integer_upper x0 x1 z0 z1 a b c d out
    ha hb hc hd hg hmu hquery

end
end ImbalancedChen.P4ASymmetricNewOnlyLeafSourceOnly
