import ImbalancedChen.P2OriginalSaving16CellOwnership
import ImbalancedChen.P2OriginalSaving19SimplexMoments
import ImbalancedChen.P2PositiveAffineSimplexLogJensen
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original saving16 affine functions are used here. Only the neutral
Delta8 barycentric integrals, affine-image Jacobian and nine-vertex map
are reused from K's saving19 module. Its saving19 gap, factors, row family,
floor evaluator and endpoint are NOT used. No T10 or eleven-cell saving
is substituted. Means and masses below are actual Lebesgue integrals.

The Jensen step proves the log-moment bound from log(x/m) <= x/m-1;
it takes neither a log-bound premise nor a reciprocal-integral premise.
All analytic regularity is derived on the actual original cell closure.
-/
namespace ImbalancedChen.P2OriginalSaving16JensenFloor

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open VariableEnvelope P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16CellOwnership
open P2PositiveAffineSimplexLogJensenSourceOnly

namespace Bary
export P2OriginalSaving19SimplexMoments
  (canonical bary interpolate pointInterpolate bary_nonneg bary_sum
   interpolate_const interpolate_add interpolate_sub interpolate_div
   interpolate_sum pointInterpolate_apply integral_interpolate
   integral_interpolate_mul vertices support jacobian physicalVolume
   jacobian_pos physicalVolume_pos vertices_interpolate support_compact
   support_measurable integral_support)
end Bary

/-- Original ascending formula, valid on every saving16 cell closure. -/
def ascendingCap (t : Point) : ℝ := A (selectedSum t) - eta
def gap (t : Point) : ℝ := ascendingCap t - R t
def factors (t : Point) : Fin 10 → ℝ :=
  ![R t - S t, ascendingCap t - S t,
    t 0, t 1, t 2, t 3, t 4, t 5, t 6, t 7]

theorem continuous_ascendingCap : Continuous ascendingCap := by
  unfold ascendingCap A selectedSum eta
  fun_prop
theorem continuous_gap : Continuous gap := continuous_ascendingCap.sub continuous_R
theorem continuous_factor (j : Fin 10) : Continuous (fun t => factors t j) := by
  fin_cases j <;> simp only [factors, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact continuous_R.sub continuous_S
  · exact continuous_ascendingCap.sub continuous_S
  all_goals exact continuous_apply _

theorem closure_cell_ascending (c : Cell) {t : Point}
    (ht : t ∈ closure (cell c)) : M t = ascendingCap t := by
  have hhalf : A (selectedSum t) ≤ C (selectedSum t) := by
    apply (closure_minimal (s := cell c)
      (t := {x | A (selectedSum x) ≤ C (selectedSum x)}) ?_
      (isClosed_le (by unfold selectedSum A; fun_prop)
        (by unfold selectedSum C; fun_prop))) ht
    intro x hx
    exact (sourceRows_cellGuard c x hx).new_ascending.le
  simp only [M, ascendingCap, min_eq_left hhalf]

theorem closure_cell_gap_nonneg (c : Cell) {t : Point}
    (ht : t ∈ closure (cell c)) : 0 ≤ gap t := by
  apply (closure_minimal (s := cell c) (t := {x | 0 ≤ gap x}) ?_
    (isClosed_le continuous_const continuous_gap)) ht
  intro x hx
  have hm := closure_cell_ascending c (subset_closure hx)
  have hi := (sourceRows_cellGuard c x hx).improvement
  dsimp [gap]
  linarith

theorem closure_cell_factor_pos (c : Cell) {t : Point}
    (ht : t ∈ closure (cell c)) (j : Fin 10) : 0 < factors t j := by
  have hr : t ∈ closure region := closure_mono (subset_iUnion cell c) ht
  have hden := closure_region_denominator_floors hr
  have hm := closure_cell_ascending c ht
  fin_cases j <;> simp only [factors, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact cutoff_pos.trans_le hden.1
  · rw [← hm]
    exact cutoff_pos.trans_le hden.2.1
  all_goals exact cutoff_pos.trans_le (hden.2.2 _)

theorem density_eq_on_closure (c : Cell) {t : Point}
    (ht : t ∈ closure (cell c)) :
    sourceDensity t = 4 * gap t / ∏ j : Fin 10, factors t j := by
  have hm := closure_cell_ascending c ht
  norm_num [sourceDensity, gap, factors, Fin.prod_univ_succ, hm]
  ring

theorem interpolate_mul_const (v : Fin 9 → ℝ) (a : ℝ) (x : Point) :
    Bary.interpolate (fun i => a * v i) x = a * Bary.interpolate v x := by
  simp only [Bary.interpolate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem R_interpolate (v : Fin 9 → Point) (x : Point) :
    R (Bary.pointInterpolate v x) = Bary.interpolate (fun i => R (v i)) x := by
  simp only [R, d, C, Bary.interpolate_sub, Bary.interpolate_const,
    Bary.interpolate_add, interpolate_mul_const, Bary.pointInterpolate_apply]

theorem ascendingCap_interpolate (v : Fin 9 → Point) (x : Point) :
    ascendingCap (Bary.pointInterpolate v x) =
      Bary.interpolate (fun i => ascendingCap (v i)) x := by
  simp only [ascendingCap, selectedSum, A, Bary.interpolate_sub,
    Bary.interpolate_div, Bary.interpolate_add, Bary.interpolate_const,
    Bary.pointInterpolate_apply]

theorem S_interpolate (v : Fin 9 → Point) (x : Point) :
    S (Bary.pointInterpolate v x) = Bary.interpolate (fun i => S (v i)) x := by
  simp only [S, Bary.pointInterpolate_apply, Bary.interpolate_sum]

theorem gap_interpolate (v : Fin 9 → Point) (x : Point) :
    gap (Bary.pointInterpolate v x) = Bary.interpolate (fun i => gap (v i)) x := by
  simp only [gap, ascendingCap_interpolate, R_interpolate, Bary.interpolate_sub]

theorem factors_interpolate (v : Fin 9 → Point) (x : Point) (j : Fin 10) :
    factors (Bary.pointInterpolate v x) j =
      Bary.interpolate (fun i => factors (v i) j) x := by
  fin_cases j <;> simp only [factors, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · rw [R_interpolate, S_interpolate, Bary.interpolate_sub]
  · rw [ascendingCap_interpolate, S_interpolate, Bary.interpolate_sub]
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

/-- No target integral or log-moment bound is assumed. The tangent
inequality for log is integrated against the actual positive gap weight. -/
theorem weighted_log_le_log_mean {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (g l : α → ℝ) (m : ℝ)
    (hg : Integrable g μ) (hgl : Integrable (fun x => g x * l x) μ)
    (hlog : Integrable (fun x => g x * Real.log (l x)) μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hl : ∀ᵐ x ∂μ, 0 < l x)
    (hmass : 0 < mass μ g) (hm : 0 < m)
    (hmean : (∫ x, g x * l x ∂μ) / mass μ g = m) :
    (∫ x, g x * Real.log (l x) ∂μ) / mass μ g ≤ Real.log m := by
  have ht : ∀ᵐ x ∂μ, g x * Real.log (l x) ≤
      g x * Real.log m + (g x * l x) / m - g x := by
    filter_upwards [hg0, hl] with x hgx hlx
    have h := Real.log_le_sub_one_of_pos (div_pos hlx hm)
    rw [Real.log_div hlx.ne' hm.ne'] at h
    have hh := mul_le_mul_of_nonneg_left h hgx
    nlinarith
  have hi : Integrable
      (fun x => g x * Real.log m + (g x * l x) / m - g x) μ :=
    ((hg.mul_const _).add (hgl.div_const _)).sub hg
  have hbound := integral_mono_ae hlog hi ht
  rw [integral_sub ((hg.mul_const _).add (hgl.div_const _)) hg,
    integral_add (hg.mul_const _) (hgl.div_const _), integral_mul_const, integral_div]
    at hbound
  have hmean' : (∫ x, g x * l x ∂μ) = m * mass μ g :=
    (div_eq_iff hmass.ne').1 hmean
  have hc : (∫ x, g x * l x ∂μ) / m = mass μ g := by
    rw [hmean']
    field_simp [hm.ne']
  rw [hc] at hbound
  apply (div_le_iff₀ hmass).2
  dsimp [mass] at hmass hbound ⊢
  nlinarith

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

/-- Exact Python operation `bound.numerator * 2**96 // bound.denominator`.
This is integer floor division, including its sign convention. -/
def q96Floor (q : ℚ) : ℤ := (q.num * (2 ^ 96 : ℤ)) / q.den

theorem q96Floor_eq_floor (q : ℚ) : q96Floor q = ⌊q * (2 : ℚ) ^ 96⌋ := by
  rw [q96Floor, ← Rat.floor_intCast_div_natCast]
  congr 1
  push_cast
  rw [mul_div_right_comm, Rat.num_div_den]

theorem q96Floor_le (q : ℚ) :
    (q96Floor q : ℝ) / (2 : ℝ) ^ 96 ≤ (q : ℝ) := by
  rw [q96Floor_eq_floor]
  have h : (⌊q * (2 : ℚ) ^ 96⌋ : ℚ) ≤ q * (2 : ℚ) ^ 96 := Int.floor_le _
  have hc : (⌊q * (2 : ℚ) ^ 96⌋ : ℝ) ≤ (q : ℝ) * (2 : ℝ) ^ 96 := by
    exact_mod_cast h
  exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ 96)).2 hc

/-- Per-simplex floor transport retains the original rational expression.
The equality is a rational vertex/determinant encoding obligation, not an
assumed integral enclosure. No closed archive instance is claimed here. -/
theorem original_simplex_q96 (c : Cell) (L : Point ≃L[ℝ] Point) (b : Point)
    (hv : ∀ i, Bary.vertices L b i ∈ closure (cell c))
    (hG : 0 < gapTotal (Bary.vertices L b)) (q : ℚ)
    (hq : (q : ℝ) =
      4 * Bary.physicalVolume L * (gapTotal (Bary.vertices L b) / 9) /
        ∏ j : Fin 10, factorMean (Bary.vertices L b) j) :
    (q96Floor q : ℝ) / (2 : ℝ) ^ 96 ≤
      ∫ t in Bary.support L b, sourceDensity t := by
  apply (q96Floor_le q).trans
  rw [hq]
  exact original_simplex_jensen c L b hv hG

end
end ImbalancedChen.P2OriginalSaving16JensenFloor
