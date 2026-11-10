import ImbalancedChen.P4AOriginalFull87EighthKernelControl
import ImbalancedChen.P4AOriginalFull87DescAscPairInteriors
import ImbalancedChen.P2OriginalSaving16JensenFloor
import ImbalancedChen.P2OriginalSaving16SimplexBinding
import Mathlib.Analysis.Convex.Measure

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Stage17's actual fifteen descending129 sources, not a new interior box.
Only neutral canonical Dirichlet/Jacobian moments, the proved log tangent
bound and the rational edge map are reused from saving16/19. Their caps,
source families, archived rows and numerical endpoints are not reused.
-/
namespace ImbalancedChen.P2OriginalSaving17DescendingGeometry
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators ENNReal
open VariableEnvelope
open P2OriginalDescendingEighthLogSemantics

abbrev Cell := Fin 15
abbrev AffineRow := Fin 9 → ℚ
abbrev evalRow := P2OriginalSaving16FourteenPhysicalAtlas.evalRow
abbrev continuous_evalRow := P2OriginalSaving16FourteenPhysicalAtlas.continuous_evalRow
abbrev evalRow_convexCombination :=
  P2OriginalSaving16FourteenPhysicalAtlas.evalRow_convexCombination

def rows (c : Cell) (k : Fin 96) : String × AffineRow :=
  ("", OriginalDescendingFifteenLiteralAffineRows.exportedCoefficients c k)
def sourceRows (c : Cell) (t : Point) : Prop := ∀ k : Fin 96, 0 < evalRow (rows c k).2 t
def cell (c : Cell) : Set Point := {t | sourceRows c t}
def sourceDensity (t : Point) : ℝ := physicalKernel t

theorem cell_eq_original_source (c : Cell) :
    cell c = P4AOriginalFull87StrictActionTrim.sourceSet (.descending c) := rfl

theorem sourceDensity_eq_kernel (c : Cell) (t : Point) :
    sourceDensity t = P4AOriginalFull87EighthKernelControl.kernel (.descending c) t := by
  rw [sourceDensity, physicalKernel_eq_literal]
  rfl

theorem integrableOn_sourceDensity_cell (c : Cell) : IntegrableOn sourceDensity (cell c) := by
  simp_rw [sourceDensity_eq_kernel c]
  rw [cell_eq_original_source]
  exact P4AOriginalFull87EighthKernelControl.integrableOn_kernel _

theorem isOpen_cell (c : Cell) : IsOpen (cell c) := by
  have heq : cell c = ⋂ k : Fin 96, {t : Point | 0 < evalRow (rows c k).2 t} := by
    ext t
    simp [cell, sourceRows]
  rw [heq]
  exact isOpen_iInter_of_finite (fun k =>
    isOpen_lt continuous_const (continuous_evalRow (rows c k).2))

theorem convex_cell (c : Cell) : Convex ℝ (cell c) := by
  intro x hx y hy a b ha hb hab k
  rw [evalRow_convexCombination _ x y a b hab]
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa only [ha0, hb1, zero_mul, zero_add, one_mul] using hy k
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    exact add_pos_of_pos_of_nonneg (mul_pos hapos (hx k)) (mul_nonneg hb (hy k).le)

theorem volume_frontier_cell (c : Cell) : (volume : Measure Point) (frontier (cell c)) = 0 :=
  (convex_cell c).addHaar_frontier volume

def closedRows (c : Cell) (t : Point) : Prop := ∀ k : Fin 96, 0 ≤ evalRow (rows c k).2 t

theorem closedRows_mem_closure (c : Cell) (z : Point) (hz : sourceRows c z)
    {t : Point} (ht : closedRows c t) : t ∈ closure (cell c) := by
  let f : ℝ → Point := fun a => a • z + (1 - a) • t
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hpos : ∀ a ∈ Set.Ioo (0 : ℝ) 1, f a ∈ cell c := by
    intro a ha k
    rw [show f a = a • z + (1 - a) • t from rfl,
      evalRow_convexCombination _ _ _ _ _ (by ring)]
    exact add_pos_of_pos_of_nonneg (mul_pos ha.1 (hz k))
      (mul_nonneg (sub_nonneg.mpr ha.2.le) (ht k))
  have hzero : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, by norm_num⟩
  have hm : f 0 ∈ closure (f '' Set.Ioo (0 : ℝ) 1) :=
    image_closure_subset_closure_image hf ⟨0, hzero, rfl⟩
  have himage : f '' Set.Ioo (0 : ℝ) 1 ⊆ cell c := by
    rintro _ ⟨a, ha, rfl⟩
    exact hpos a ha
  simpa [f] using closure_mono himage hm

namespace Bary
export P2OriginalSaving19SimplexMoments
  (canonical bary interpolate pointInterpolate bary_nonneg bary_sum
   interpolate_const interpolate_add interpolate_sub interpolate_div
   interpolate_sum pointInterpolate_apply integral_interpolate
   integral_interpolate_mul vertices support jacobian physicalVolume
   jacobian_pos physicalVolume_pos vertices_interpolate support_compact
   support_measurable integral_support)
end Bary

def gap (t : Point) : ℝ := newCap t - oldRaw t
abbrev factors := denominatorFactors
theorem continuous_newCap : Continuous newCap := by unfold newCap C selectedSum; fun_prop
theorem continuous_oldRaw : Continuous oldRaw := by unfold oldRaw C d; fun_prop
theorem continuous_total : Continuous total := by unfold total; fun_prop
theorem continuous_gap : Continuous gap := continuous_newCap.sub continuous_oldRaw
theorem continuous_factor (j : Fin 10) : Continuous (fun t => factors t j) := by
  fin_cases j <;> simp only [factors, denominatorFactors, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact continuous_oldRaw.sub continuous_total
  · exact continuous_newCap.sub continuous_total
  all_goals exact continuous_apply _

theorem sourceDensity_nonneg_on_cell {c : Cell} {t : Point} (ht : t ∈ cell c) :
    0 ≤ sourceDensity t := by
  have hs : P4AOriginalFull87SourceDictionary.Source (.descending c) t := ht
  rw [sourceDensity_eq_kernel c]
  exact (P4AOriginalFull87EighthKernelControl.kernel_bounds hs).1

theorem closure_cell_gap_nonneg (c : Cell) {t : Point}
    (ht : t ∈ closure (cell c)) : 0 ≤ gap t := by
  apply (closure_minimal (s := cell c) (t := {x | 0 ≤ gap x}) ?_
    (isClosed_le continuous_const continuous_gap)) ht
  intro x hx
  have hs : P4AOriginalFull87SourceDictionary.Source (.descending c) x := hx
  exact (sub_pos.mpr (P4AOriginalFull87SourceDictionary.source_improvement_terminal hs).1).le

theorem closure_cell_factor_pos (c : Cell) {t : Point}
    (ht : t ∈ closure (cell c)) (j : Fin 10) : 0 < factors t j := by
  have hf : P4AOriginalFull87EighthKernelControl.cutoff ≤ factors t j := by
    apply (closure_minimal (s := cell c)
      (t := {x | P4AOriginalFull87EighthKernelControl.cutoff ≤ factors x j}) ?_
      (isClosed_le continuous_const (continuous_factor j))) ht
    intro x hx
    have hs : P4AOriginalFull87SourceDictionary.Source (.descending c) x := hx
    have hr := P4AOriginalFull87EighthKernelControl.source_residual_range hs
    have hc := P4AOriginalFull87EighthKernelControl.source_coordinate_lower hs
    fin_cases j <;> simp only [factors, denominatorFactors, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · exact (hr.1.trans hr.2.1).le
    · have hi := hr.2.2.1
      change oldRaw x < newCap x at hi
      have hP := hr.1.trans hr.2.1
      change P4AOriginalFull87EighthKernelControl.cutoff < oldRaw x - total x at hP
      linarith
    all_goals exact (hc _).le
  exact P4AOriginalFull87EighthKernelControl.cutoff_pos.trans_le hf

theorem density_eq_on_closure (c : Cell) {t : Point}
    (_ht : t ∈ closure (cell c)) :
    sourceDensity t = 4 * gap t / ∏ j : Fin 10, factors t j := by
  rw [sourceDensity, physicalKernel_eq_literal, denominatorFactors_product]
  rfl

open P2PositiveAffineSimplexLogJensenSourceOnly
open P2OriginalSaving16JensenFloor (weighted_log_le_log_mean q96Floor q96Floor_le)
theorem interpolate_mul_const (v : Fin 9 → ℝ) (a : ℝ) (x : Point) :
    Bary.interpolate (fun i => a * v i) x = a * Bary.interpolate v x := by
  simp only [Bary.interpolate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem oldRaw_interpolate (v : Fin 9 → Point) (x : Point) :
    oldRaw (Bary.pointInterpolate v x) = Bary.interpolate (fun i => oldRaw (v i)) x := by
  simp only [oldRaw, d, C, Bary.interpolate_sub, Bary.interpolate_const,
    Bary.interpolate_add, interpolate_mul_const, Bary.pointInterpolate_apply]

theorem newCap_interpolate (v : Fin 9 → Point) (x : Point) :
    newCap (Bary.pointInterpolate v x) =
      Bary.interpolate (fun i => newCap (v i)) x := by
  simp only [newCap, selectedSum, C, Bary.interpolate_sub,
    Bary.interpolate_div, Bary.interpolate_add, Bary.interpolate_const,
    interpolate_mul_const, Bary.pointInterpolate_apply]

theorem total_interpolate (v : Fin 9 → Point) (x : Point) :
    total (Bary.pointInterpolate v x) = Bary.interpolate (fun i => total (v i)) x := by
  simp only [total, Bary.pointInterpolate_apply, Bary.interpolate_sum]

theorem gap_interpolate (v : Fin 9 → Point) (x : Point) :
    gap (Bary.pointInterpolate v x) = Bary.interpolate (fun i => gap (v i)) x := by
  simp only [gap, newCap_interpolate, oldRaw_interpolate, Bary.interpolate_sub]

theorem factors_interpolate (v : Fin 9 → Point) (x : Point) (j : Fin 10) :
    factors (Bary.pointInterpolate v x) j =
      Bary.interpolate (fun i => factors (v i) j) x := by
  fin_cases j <;> simp only [factors, denominatorFactors, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · rw [oldRaw_interpolate, total_interpolate, Bary.interpolate_sub]
  · rw [newCap_interpolate, total_interpolate, Bary.interpolate_sub]
  all_goals exact Bary.pointInterpolate_apply v x _

def gapTotal (v : Fin 9 → Point) : ℝ := ∑ i : Fin 9, gap (v i)
def factorMean (v : Fin 9 → Point) (j : Fin 10) : ℝ :=
  ((∑ i : Fin 9, factors (v i) j) +
    (∑ i : Fin 9, gap (v i) * factors (v i) j) / gapTotal v) / 10

/-- The same nine physical vertices give the mass; G/9 is proved. -/
theorem integral_gap (L : Point ≃L[ℝ] Point) (b : Point) :
    (∫ t in Bary.support L b, gap t) =
      Bary.physicalVolume L * gapTotal (Bary.vertices L b) / 9 := by
  rw [Bary.integral_support]
  simp_rw [← Bary.vertices_interpolate L b, gap_interpolate]
  rw [Bary.integral_interpolate]
  norm_num [Bary.physicalVolume, gapTotal]
  ring

theorem integral_gap_factor (L : Point ≃L[ℝ] Point) (b : Point) (j : Fin 10) :
    (∫ t in Bary.support L b, gap t * factors t j) =
      Bary.jacobian L *
        (gapTotal (Bary.vertices L b) * (∑ i : Fin 9, factors (Bary.vertices L b i) j) +
          ∑ i : Fin 9, gap (Bary.vertices L b i) * factors (Bary.vertices L b i) j) /
          (10.factorial : ℝ) := by
  rw [Bary.integral_support]
  simp_rw [← Bary.vertices_interpolate L b, gap_interpolate, factors_interpolate]
  rw [Bary.integral_interpolate_mul]
  dsimp [gapTotal]
  ring

/-- The second barycentric moment proves exactly the producer's
(sum factor + sum(gap*factor)/G)/10, including the diagonal contribution. -/
theorem normalized_factor_mean (L : Point ≃L[ℝ] Point) (b : Point) (j : Fin 10)
    (hG : 0 < gapTotal (Bary.vertices L b)) :
    (∫ t in Bary.support L b, gap t * factors t j) /
      (∫ t in Bary.support L b, gap t) = factorMean (Bary.vertices L b) j := by
  rw [integral_gap_factor, integral_gap]
  have hJ := (Bary.jacobian_pos L).ne'
  norm_num [Bary.physicalVolume, factorMean]
  field_simp [hJ, hG.ne']
  ring

theorem support_subset_closure (c : Cell) (L : Point ≃L[ℝ] Point) (b : Point)
    (hv : ∀ i, Bary.vertices L b i ∈ closure (cell c)) :
    Bary.support L b ⊆ closure (cell c) := by
  rintro t ⟨x, hx, rfl⟩
  rw [← Bary.vertices_interpolate L b x]
  exact (convex_cell c).closure.sum_mem (fun i _ => Bary.bary_nonneg hx i)
    (Bary.bary_sum x) (fun i _ => hv i)

theorem factorMean_pos (c : Cell) (v : Fin 9 → Point)
    (hv : ∀ i, v i ∈ closure (cell c)) (hG : 0 < gapTotal v) (j : Fin 10) :
    0 < factorMean v j := by
  have hp : 0 < ∑ i : Fin 9, factors (v i) j :=
    Finset.sum_pos (fun i _ => closure_cell_factor_pos c (hv i) j) Finset.univ_nonempty
  have hn : 0 ≤ ∑ i : Fin 9, gap (v i) * factors (v i) j :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (closure_cell_gap_nonneg c (hv i))
      (closure_cell_factor_pos c (hv i) j).le)
  exact div_pos (add_pos_of_pos_of_nonneg hp (div_nonneg hn hG.le)) (by norm_num)

/-- The original rational Jensen expression bounds the actual physical
simplex integral. The only geometric input is its actual vertex location;
the positive determinant is embodied by the invertible edge map. -/
theorem original_simplex_jensen (c : Cell) (L : Point ≃L[ℝ] Point) (b : Point)
    (hv : ∀ i, Bary.vertices L b i ∈ closure (cell c))
    (hG : 0 < gapTotal (Bary.vertices L b)) :
    4 * Bary.physicalVolume L * (gapTotal (Bary.vertices L b) / 9) /
      (∏ j : Fin 10, factorMean (Bary.vertices L b) j) ≤
        ∫ t in Bary.support L b, sourceDensity t := by
  let μ : Measure Point := volume.restrict (Bary.support L b)
  let means := factorMean (Bary.vertices L b)
  have hs := support_subset_closure c L b hv
  have hg : Integrable gap μ :=
    continuous_gap.continuousOn.integrableOn_compact (Bary.support_compact L b)
  have hg0 : ∀ᵐ t ∂μ, 0 ≤ gap t := by
    filter_upwards [ae_restrict_mem (Bary.support_measurable L b)] with t ht
    exact closure_cell_gap_nonneg c (hs ht)
  have hl : ∀ᵐ t ∂μ, ∀ j : Fin 10, 0 < factors t j := by
    filter_upwards [ae_restrict_mem (Bary.support_measurable L b)] with t ht
    exact closure_cell_factor_pos c (hs ht)
  have hmass : 0 < mass μ gap := by
    change 0 < ∫ t in Bary.support L b, gap t
    rw [integral_gap]
    exact div_pos (mul_pos (Bary.physicalVolume_pos L) hG) (by norm_num)
  have hprod : Continuous (fun t : Point => ∏ j : Fin 10, factors t j) :=
    continuous_finsetProd _ (fun j _ => continuous_factor j)
  have hrec : Integrable (fun t => gap t / ∏ j : Fin 10, factors t j) μ :=
    (continuous_gap.continuousOn.div hprod.continuousOn
      (fun t ht => (Finset.prod_pos
        (fun j _ => closure_cell_factor_pos c (hs ht) j)).ne')).integrableOn_compact
      (Bary.support_compact L b)
  have hlog (j : Fin 10) : Integrable (fun t => gap t * Real.log (factors t j)) μ :=
    (continuous_gap.continuousOn.mul ((continuous_factor j).continuousOn.log
      (fun t ht => (closure_cell_factor_pos c (hs ht) j).ne'))).integrableOn_compact
      (Bary.support_compact L b)
  have hmeans (j : Fin 10) : 0 < means j := factorMean_pos c _ hv hG j
  have hbound (j : Fin 10) :
      (∫ t, gap t * Real.log (factors t j) ∂μ) / mass μ gap ≤ Real.log (means j) := by
    apply weighted_log_le_log_mean μ gap (fun t => factors t j) (means j) hg
      ((continuous_gap.mul (continuous_factor j)).continuousOn.integrableOn_compact
        (Bary.support_compact L b)) (hlog j) hg0 (hl.mono fun t ht => ht j) hmass
      (hmeans j)
    exact normalized_factor_mean L b j hG
  have hj := weighted_probability_log_jensen μ gap (fun j t => factors t j)
    (fun j => Real.log (means j)) continuous_gap.measurable hg hg0 hmass hl hlog hrec hbound
  have hp : 0 < ∏ j : Fin 10, means j := Finset.prod_pos (fun j _ => hmeans j)
  rw [← Real.log_prod (fun j _ => (hmeans j).ne'), Real.exp_neg,
    Real.exp_log hp] at hj
  have hj4 := mul_le_mul_of_nonneg_left hj (by norm_num : (0 : ℝ) ≤ 4)
  have he : (∫ t in Bary.support L b, sourceDensity t) =
      4 * ∫ t, gap t / ∏ j : Fin 10, factors t j ∂μ := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (Bary.support_measurable L b)
    intro t ht
    rw [density_eq_on_closure c (hs ht)]
    ring
  rw [he]
  have hm : mass μ gap = Bary.physicalVolume L * gapTotal (Bary.vertices L b) / 9 :=
    integral_gap L b
  rw [hm] at hj4
  simpa only [means, div_eq_mul_inv, mul_assoc] using hj4



end
end ImbalancedChen.P2OriginalSaving17DescendingGeometry
