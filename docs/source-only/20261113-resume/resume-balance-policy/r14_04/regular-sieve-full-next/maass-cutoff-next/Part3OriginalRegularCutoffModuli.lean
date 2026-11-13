import ImbalancedChen.Part3OriginalRegularCutoffPlane
import ImbalancedChen.Part3OriginalSameInfinityScalarGeometry
import ImbalancedChen.Part3OriginalRegularPreKuznetsovAverage

/-! The actual compact exponential probe tends to the Gaussian orbital
sum on every level. The intermediate Euler majorant is uniform in r
and in the cutoff for each fixed positive pair. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularCutoffModuli20261113
open Real Set Filter MeasureTheory
open scoped Topology
open OriginalRegularCutoffAngularMass20261113 (tilt tilt_lt_quarter)
open OriginalRegularCutoffPlane20261113 (value fullValue constant constant_nonnegative value_price measurable_value)
open OriginalInfinitySwitchedGeometry20261113 (argument)
open OriginalSameInfinityScalarGeometry20261113 (term)
open FixedMarkTail (price price_nonneg majorant majorant_nonneg physical_le_majorant summable_majorant_price)
open OriginalRegularPreKuznetsovGaussian20261113 (weight weight_nonnegative)
open OriginalRegularPreKuznetsovAverage20261113 (gaussianOrbit weight_integrable)

private def scale (m n : ℕ+) := 4*π*sqrt ((m.val:ℝ)*n.val)
private theorem scale_pos (m n : ℕ+) : 0<scale m n := by
  have m0 : 0<(m.val:ℝ) := by exact_mod_cast m.property
  have n0 : 0<(n.val:ℝ) := by exact_mod_cast n.property
  unfold scale;positivity

private theorem argument_pos (m n c : ℕ+) : 0<argument m n c :=
  div_pos (scale_pos m n) (by exact_mod_cast c.property)

private def major (m n c : ℕ+) := (constant*(scale m n)^(1-tilt))*price (m.val:ℤ) tilt c.val

private theorem major_nonnegative (m n c : ℕ+) : 0≤major m n c :=
  mul_nonneg (mul_nonneg constant_nonnegative (rpow_nonneg (scale_pos m n).le _)) (price_nonneg _ _ _)

private theorem major_summable (m n : ℕ+) : Summable (major m n) := by
  have hm : (m.val:ℤ)≠0 := by exact_mod_cast m.property.ne'
  exact ((summable_majorant_price hm tilt_lt_quarter).comp_injective PNat.coe_injective).const_mul _

theorem term_bound (q m n c : ℕ+) (j : Option ℕ) (r : ℝ) :
    ‖term (value j r) q m n c‖≤major m n c := by
  have c0 : 0<(c.val:ℝ) := by exact_mod_cast c.property
  by_cases d : q.val∣c.val
  · rw [term,if_pos d,norm_mul,norm_div,Complex.norm_natCast]
    have w := mul_le_mul (div_le_div_of_nonneg_right
      (physical_le_majorant (m.val:ℤ) c.val (n.val:ℤ)) c0.le)
      (value_price (argument_pos m n c) j r) (norm_nonneg _)
      (div_nonneg (majorant_nonneg _ _) c0.le)
    apply w.trans_eq
    change majorant (m.val:ℤ) c.val/c.val*(constant*(scale m n/c.val)^(1-tilt))=_
    rw [div_rpow (scale_pos m n).le c0.le,major,price,if_neg c.property.ne',
      show -2+tilt= -(1-tilt)-1 by ring,rpow_sub_one c0.ne',rpow_neg c0.le]
    ring
  · simp only [term,if_neg d,norm_zero]
    exact major_nonnegative _ _ _

private theorem term_measurable (q m n c : ℕ+) (j : Option ℕ) :
    Measurable (fun r => term (value j r) q m n c) := by
  by_cases d : q.val∣c.val
  · simp only [term,if_pos d]
    exact measurable_const.mul (measurable_value (argument_pos m n c) j)
  · simp only [term,if_neg d]
    exact measurable_const

theorem term_limit (q m n c : ℕ+) (r : ℝ) :
    Tendsto (fun j => term (value (some j) r) q m n c) atTop (𝓝 (term (value none r) q m n c)) := by
  by_cases d : q.val∣c.val
  · simp only [term,if_pos d]
    exact (OriginalRegularCutoffPlane20261113.cutoff_limit (argument_pos m n c) r).const_mul _
  · simp only [term,if_neg d];exact tendsto_const_nhds

def series (q m n : ℕ+) (j : Option ℕ) (r : ℝ) := ∑' c,term (value j r) q m n c

theorem modulus_limit (q m n : ℕ+) (r : ℝ) :
    Tendsto (fun j : ℕ => series q m n (some j) r) atTop (𝓝 (series q m n none r)) :=
  tendsto_tsum_of_dominated_convergence (major_summable m n) (fun c => term_limit q m n c r)
    (Eventually.of_forall (fun j c => term_bound q m n c (some j) r))

private theorem series_measurable (q m n : ℕ+) (j : Option ℕ) : Measurable (series q m n j) :=
  Measurable.tsum (fun c => term_measurable q m n c j)

private theorem series_price (q m n : ℕ+) (j : Option ℕ) (r : ℝ) :
    ‖series q m n j r‖≤∑' c,major m n c := by
  let f := fun c => term (value j r) q m n c
  have h : Summable (fun c => ‖f c‖) := (major_summable m n).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun c => term_bound q m n c j r)
  exact (norm_tsum_le_tsum_norm h).trans (h.tsum_le_tsum (fun c => term_bound q m n c j r) (major_summable m n))

theorem weighted_integrable {K : ℝ} (hp : 0<K) (q m n : ℕ+) (j : Option ℕ) :
    Integrable (fun r => (weight K r:ℂ)*series q m n j r) := by
  apply ((weight_integrable hp).mul_const (∑' c,major m n c)).mono'
  · exact ((show Measurable (fun r : ℝ => (weight K r:ℂ)) by unfold weight;fun_prop).mul
      (series_measurable q m n j)).aestronglyMeasurable
  · exact ae_of_all _ (fun r => by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (weight_nonnegative _ _)]
      exact mul_le_mul_of_nonneg_left (series_price q m n j r) (weight_nonnegative _ _))

theorem full_average {K : ℝ} (hp : 0<K) (q m n : ℕ+) :
    Summable (fun c => ‖term (gaussianOrbit K) q m n c‖) ∧
    (∫ r : ℝ,(weight K r:ℂ)*series q m n none r)=∑' c,term (gaussianOrbit K) q m n c := by
  let F := fun (c : ℕ+) (r : ℝ) => (weight K r:ℂ)*term (value none r) q m n c
  have b (c : ℕ+) (r : ℝ) : ‖F c r‖≤weight K r*major m n c := by
    rw [F,norm_mul,Complex.norm_real,Real.norm_of_nonneg (weight_nonnegative K r)]
    exact mul_le_mul_of_nonneg_left (term_bound q m n c none r) (weight_nonnegative _ _)
  have Fi (c : ℕ+) : Integrable (F c) := by
    apply ((weight_integrable hp).mul_const (major m n c)).mono'
    · exact ((show Measurable (fun r : ℝ => (weight K r:ℂ)) by unfold weight;fun_prop).mul
        (term_measurable q m n c none)).aestronglyMeasurable
    · exact ae_of_all _ (b c)
  have mass (c : ℕ+) : (∫ r : ℝ,‖F c r‖)≤(∫ r : ℝ,weight K r)*major m n c := by
    have h := integral_mono (Fi c).norm ((weight_integrable hp).mul_const _) (b c)
    rwa [integral_mul_const] at h
  have hsum : Summable (fun c => ∫ r : ℝ,‖F c r‖) := ((major_summable m n).const_mul _).of_nonneg_of_le
    (fun c => integral_nonneg (fun r => norm_nonneg _)) mass
  have E (c : ℕ+) : (∫ r : ℝ,F c r)=term (gaussianOrbit K) q m n c := by
    by_cases d : q.val∣c.val
    · simp only [F,term,if_pos d,gaussianOrbit,←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with r
      dsimp only [value,fullValue,OriginalRegularCutoffPlane20261113.fullPair]
      ring
    · simp [F,term,d]
  refine ⟨?_,?_⟩
  · apply hsum.of_nonneg_of_le (fun c => norm_nonneg _)
    intro c;rw [←E];exact norm_integral_le_integral_norm _
  · calc
      _=∫ r : ℝ,∑' c,F c r := by simp only [F,series,tsum_mul_left]
      _=∑' c,∫ r : ℝ,F c r := (integral_tsum_of_summable_integral_norm Fi hsum).symm
      _=_ := tsum_congr E

/-- The compact Gaussian integral converges to the sum of the actual
Gaussian orbit with the original divisibility gate at every level. -/
theorem compact_average_limit {K : ℝ} (hp : 0<K) (q m n : ℕ+) :
    Tendsto (fun j : ℕ => ∫ r : ℝ,(weight K r:ℂ)*series q m n (some j) r) atTop
      (𝓝 (∑' c,term (gaussianOrbit K) q m n c)) := by
  rw [←(full_average hp q m n).2]
  apply tendsto_integral_of_dominated_convergence (fun r => weight K r*(∑' c,major m n c))
  · exact fun j => (weighted_integrable hp q m n (some j)).aestronglyMeasurable
  · exact (weight_integrable hp).mul_const _
  · intro j
    exact ae_of_all _ (fun r => by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (weight_nonnegative K r)]
      exact mul_le_mul_of_nonneg_left (series_price q m n (some j) r) (weight_nonnegative K r))
  · exact ae_of_all _ (fun r => (modulus_limit q m n r).const_mul _)

end ImbalancedChen.Part3.OriginalRegularCutoffModuli20261113
end

