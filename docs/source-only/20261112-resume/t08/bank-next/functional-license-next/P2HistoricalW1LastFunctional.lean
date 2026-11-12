import ImbalancedChen.P2HistoricalLowTargetEdges
import MathlibNt.Wu2008DoubleSieve.ClassicalPositiveBounds
import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainSource

/-! The historical W1 row (3,5), including its whole signed base and all
per-product Q80 floors, is dominated by its own preceding H(5) anchor. -/
namespace ImbalancedChen.P2HistoricalW1LastFunctional

noncomputable section
open Set MeasureTheory Wu2008DoubleSieve
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open P2Historical248Authentication P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2HistoricalHighPointAncestry P2HistoricalLowerBankAncestry P2HistoricalLowTargetEdges
open P2TableActionSourceOnly P2SimultaneousTableSourceOnly
open scoped Interval

private theorem upper_coefficient_at_ten_thirds : wuUpperCoefficient (10/3) ≤ 19/18 := by
  have he := firstFunctionalGain_coefficient_eq_log (s := (3 : ℝ)) (t := 10/3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show wuUpperCoefficient 3 = 1 from jr1965F_normalized_initial (by norm_num) (by norm_num),
    show (10/3 : ℝ)-1 = 7/3 by norm_num] at he
  have hc : ContinuousOn (fun u : ℝ => Real.log (u-1)/u) (Icc 2 (7/3)) := by
    apply ContinuousOn.div
    · apply (continuous_id.sub continuous_const).continuousOn.log
      intro u hu
      change u-1 ≠ 0
      linarith [hu.1]
    · exact continuous_id.continuousOn
    · intro u hu
      change u ≠ 0
      linarith [hu.1]
  have hb : (∫ u in (2 : ℝ)..(7/3), Real.log (u-1)/u) ≤ ∫ _u in (2 : ℝ)..(7/3), (1/6 : ℝ) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hc.intervalIntegrable_of_Icc (by norm_num)) intervalIntegrable_const
    intro u hu
    apply (div_le_iff₀ (by linarith [hu.1] : 0<u)).2
    have hl := Real.log_le_sub_one_of_pos (by linarith [hu.1] : 0 < u-1)
    linarith [hu.1,hu.2]
  rw [intervalIntegral.integral_const, smul_eq_mul] at hb
  linarith only [he,hb]

/-- An upper bound on the actual lower improvement used by this row. -/
theorem lower_gain_cap {δ u : ℝ} (hd : 0<δ) (hd' : δ≤1/10)
    (hu : 10/3≤u) (hu' : u≤10) : h δ u ≤ 4/15 := by
  have hm := wuImprovementLimit_lower_antitone hd hd'
    ⟨by norm_num, by norm_num : (10/3 : ℝ) ≤ 10⟩ ⟨by linarith,hu'⟩ hu
  have he := (wuImprovementLimit_bounds hd (by linarith : δ<1/2)
    (by norm_num : (1 : ℝ) ≤ 10/3) (by norm_num : (10/3 : ℝ) ≤ 10)).2.2.2
  have hf := ClassicalPositiveBounds.lower_seed_four_fifths (le_rfl : (10/3 : ℝ) ≤ 10/3)
  change wuImprovementLimit false δ u ≤ 4/15
  linarith only [hm, he, hf, upper_coefficient_at_ten_thirds]

abbrev Weight := P2OriginalW2CandidateIntegerABI.WeightRow
def lastRow (a : SourceW1) : Bool := decide (a.s=3 ∧ a.s0=5)
def weightTotal (rs : List Weight) : ℤ := (rs.map (fun r => r.lower)).sum
def rowCheck (a : SourceW1) : Bool := decide
  (a.pointIndex.val=199 ∧ 10*a.effectiveBase ≤ -(tableQ : ℤ) ∧
    8*weightTotal a.feedback ≤ 3*(tableQ : ℤ)) &&
  a.feedback.all (fun r => decide (116 ≤ r.index.val ∧ 0 ≤ r.lower))

/-- Only signs and aggregate sizes of this one physical archive row.
The guard does not inspect any H/h table, iteration or saved result. -/
private theorem archive :
    w1Original.any lastRow = true ∧ w1Retained.any lastRow = true ∧
    w1Original.all (fun a => !lastRow a || rowCheck a) = true ∧
    w1Retained.all (fun a => !lastRow a || rowCheck a) = true := by decide

theorem last_row_present (g : ℕ) : ∃ a ∈ sourceW1Schedule g, lastRow a=true := by
  apply List.any_eq_true.mp
  unfold sourceW1Schedule
  split <;> first | exact archive.1 | exact archive.2.1

private theorem last_row_check (g : ℕ) {a : SourceW1} (ha : a ∈ sourceW1Schedule g)
    (hl : lastRow a=true) : rowCheck a=true := by
  have hall : (sourceW1Schedule g).all (fun v => !lastRow v || rowCheck v) = true := by
    unfold sourceW1Schedule
    split <;> first | exact archive.2.2.1 | exact archive.2.2.2
  simpa only [hl, Bool.not_true, Bool.false_or] using List.all_eq_true.mp hall a ha

private theorem scaled_weights (old : Table) (rs : List Weight)
    (hb : ∀ r ∈ rs, 0 ≤ r.lower ∧ 15*old false r.index ≤ 4*(tableQ : ℤ)) :
    15*sourceWeightSum old false rs ≤ 4*weightTotal rs := by
  induction rs with
  | nil => simp [sourceWeightSum,weightTotal]
  | cons r rs ih =>
    obtain ⟨hr,hx⟩ := hb r List.mem_cons_self
    have hd : (0 : ℤ) < tableQ := by exact_mod_cast tableQ_pos
    let x := old false r.index
    let w := r.lower
    let d : ℤ := tableQ
    have hfloor : x*w/d*d ≤ x*w := Int.ediv_mul_le (x*w) hd.ne'
    have hprod : 15*(x*w/d)*d ≤ 4*w*d := by
      calc
        15*(x*w/d)*d = 15*(x*w/d*d) := by ring
        _ ≤ 15*(x*w) := mul_le_mul_of_nonneg_left hfloor (by norm_num)
        _ = (15*x)*w := by ring
        _ ≤ (4*d)*w := mul_le_mul_of_nonneg_right hx hr
        _ = 4*w*d := by ring
    have hsingle : 15*(x*w/d) ≤ 4*w := by
      by_contra hn
      exact (not_lt_of_ge hprod) (mul_lt_mul_of_pos_right (lt_of_not_ge hn) (show 0<d from hd))
    have hrest := ih (fun u hu => hb u (List.mem_cons_of_mem r hu))
    change 15*(x*w/d + sourceWeightSum old false rs) ≤ 4*weightTotal (r::rs)
    rw [show weightTotal (r::rs) = w+weightTotal rs by simp [weightTotal,w]]
    linarith only [hsingle,hrest]

/-- Every product of the actual historical old table is rounded down before
summation. The old h enclosures are needed only on the listed upper strip. -/
theorem complete_row_le_own_point (g : ℕ) {δ : ℝ} (hd : 0<δ) (hd' : δ≤1/10)
    {a : SourceW1} (ha : a ∈ sourceW1Schedule g) (hl : lastRow a=true)
    (hprev : ∀ i : Fin 200, 116≤i.val → (outputAt g false i : ℝ)/tableQ ≤ h δ (tableGrid (i.val+1))) :
    sourceW1Value (outputAt g) a ≤ outputAt g true a.pointIndex := by
  obtain ⟨hfields,hrs⟩ := Bool.and_eq_true.mp (last_row_check g ha hl)
  obtain ⟨_,hbase,hmass⟩ := of_decide_eq_true hfields
  have hQ : 0 < (tableQ : ℝ) := by exact_mod_cast tableQ_pos
  have hweights := scaled_weights (outputAt g) a.feedback (by
    intro r hr
    obtain ⟨hs,hw⟩ := of_decide_eq_true (List.all_eq_true.mp hrs r hr)
    refine ⟨hw,?_⟩
    have hleft : 10/3 ≤ tableGrid (r.index.val+1) := by
      have hgrid := tableGrid_mono (show 117 ≤ r.index.val+1 by omega)
      exact (show (10/3 : ℝ) ≤ tableGrid 117 by norm_num [tableGrid]).trans hgrid
    have hright := (tableGrid_bounds (show r.index.val+1 ≤ 200 by omega)).2
    have hx := (hprev r.index hs).trans (lower_gain_cap hd hd' hleft (hright.trans (by norm_num)))
    have hxr := (div_le_iff₀ hQ).mp hx
    have hcast : (15 : ℝ)*(outputAt g false r.index : ℝ) ≤ 4*(tableQ : ℝ) := by linarith only [hxr]
    exact_mod_cast hcast)
  unfold sourceW1Value
  omega

/-- At old generation n+2, its h strip is paid by H at n+1. Its H(5)
anchor is paid by H at n after the two original Buchstab transfers. -/
theorem complete_row_from_earlier_edges (n : ℕ) {δ : ℝ} (hd : 0<δ) (hd' : δ≤1/10)
    (he : ∀ i : Fin 200, i.val ∈ edges → readGain (n+1) i ≤ H δ (tableGrid (i.val+1)))
    {a : SourceW1} (ha : a ∈ sourceW1Schedule (n+2)) (hl : lastRow a=true)
    (j : Fin 200) : (sourceW1Value (outputAt (n+2)) a : ℝ)/tableQ ≤ H δ (tableGrid (j.val+1)) := by
  have hlow := low_of_edges (n+1) hd hd' he
  have prev := upper_endpoints_from_low designatedW1 designatedW2 hd hd' designated_low_writes (n+1) hlow
  have hrow := complete_row_le_own_point (n+2) hd hd' ha hl (fun i _ =>
    iterate_lower_endpoints hd hd' designatedW1 designatedW2 (n+1) (prev (n+1) le_rfl) i)
  have hright : a.pointIndex.val=199 := (of_decide_eq_true (Bool.and_eq_true.mp (last_row_check _ ha hl)).1).1
  have hhigh := high_endpoint_two_generations designatedW1 designatedW2 hd hd' designated_low_writes
    n (prev n (Nat.le_succ n)) a.pointIndex (by omega)
  rw [hright, show tableGrid (199+1)=(5 : ℝ) by norm_num [tableGrid]] at hhigh
  have hj := tableGrid_bounds (show j.val+1≤200 by omega)
  have hm := wuImprovementLimit_upper_antitone hd hd'
    ⟨hj.1,hj.2.trans (by norm_num)⟩ ⟨by norm_num,by norm_num⟩ hj.2
  have hcast : (sourceW1Value (outputAt (n+2)) a : ℝ) ≤ (outputAt (n+2) true a.pointIndex : ℝ) := by exact_mod_cast hrow
  exact (div_le_div_of_nonneg_right hcast (Nat.cast_nonneg tableQ)).trans (hhigh.trans hm)

/-- The literal archive operation, including retention of any previous
candidate in the same upper cell. -/
theorem complete_row_preserves_at (n : ℕ) {δ : ℝ} (hd : 0<δ) (hd' : δ≤1/10)
    (he : ∀ i : Fin 200, i.val ∈ edges → readGain (n+1) i ≤ H δ (tableGrid (i.val+1)))
    {a : SourceW1} (ha : a ∈ sourceW1Schedule (n+2)) (hl : lastRow a=true)
    (cur : Table) (j : Fin 200) (hcur : (cur true j : ℝ)/tableQ ≤ H δ (tableGrid (j.val+1))) :
    (sourceW1Apply (outputAt (n+2)) cur a true j : ℝ)/tableQ ≤ H δ (tableGrid (j.val+1)) := by
  by_cases hj : j ∈ a.targets
  · rw [show sourceW1Apply (outputAt (n+2)) cur a true j =
        max (cur true j) (sourceW1Value (outputAt (n+2)) a) by simp [sourceW1Apply,hj]]
    rcases le_total (cur true j) (sourceW1Value (outputAt (n+2)) a) with hc | hc
    · rw [max_eq_right hc]
      exact complete_row_from_earlier_edges n hd hd' he ha hl j
    · rw [max_eq_left hc]
      exact hcur
  · simpa [sourceW1Apply,hj] using hcur

end
end ImbalancedChen.P2HistoricalW1LastFunctional
