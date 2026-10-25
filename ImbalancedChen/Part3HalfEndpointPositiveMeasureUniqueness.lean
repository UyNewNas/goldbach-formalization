import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/-!
# Half-endpoint interval identities determine positive finite measures

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Endpoint atoms are eliminated first by shrinking the interval to its fixed
left endpoint; the right-hand open interval shrinks to the empty set.
Only afterwards are closed interval values identified. Logarithmic transport
places positive intervals in a genuine whole-real-line generating class.
No atomlessness conclusion or measure equality is assumed for the first
measure. The later actual KL caller must prove the displayed half-interval
identity using its two genuine Stone limits.
-/

namespace ImbalancedChen.Part3.HalfEndpointPositiveMeasureUniqueness20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

theorem positive_atom_zero_of_half_interval
    (mu sigma : Measure ℝ) [IsFiniteMeasure mu] [IsFiniteMeasure sigma]
    (hhalf : ∀ a b : ℝ, 0 < a → a < b →
      mu.real (Ioo a b) + (mu.real {a} + mu.real {b}) / 2 = sigma.real (Ioo a b))
    {x : ℝ} (hx : 0 < x) : mu ({x} : Set ℝ) = 0 := by
  let v : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let S : ℕ → Set ℝ := fun n => Ioo x (x + v n)
  have hvpos (n : ℕ) : 0 < v n := by dsimp only [v]; positivity
  have hvlim : Tendsto v atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop.add_const 1).const_div_atTop 1
  have hanti : Antitone S := by
    intro n m hnm y hy
    refine ⟨hy.1, hy.2.trans_le ?_⟩
    apply add_le_add_left
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hInter : (⋂ n, S n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hyx : x < y := (mem_iInter.mp hy 0).1
    have hsmall : ∀ᶠ n : ℕ in atTop, v n < y - x :=
      hvlim.eventually (gt_mem_nhds (sub_pos.mpr hyx))
    obtain ⟨n, hn⟩ := hsmall.exists
    have hupper := (mem_iInter.mp hy n).2
    change y < x + v n at hupper
    linarith only [hn, hupper]
  have hmeasure : Tendsto (fun n => sigma (S n)) atTop (nhds 0) := by
    have h := tendsto_measure_iInter_atTop
      (fun n => (measurableSet_Ioo : MeasurableSet (S n)).nullMeasurableSet)
      hanti ⟨0, measure_ne_top sigma (S 0)⟩
    simpa only [hInter, measure_empty, Function.comp_def] using h
  have hreal : Tendsto (fun n => sigma.real (S n)) atTop (nhds 0) := by
    have h := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hmeasure
    simpa only [measureReal_def, ENNReal.toReal_zero] using h
  have hle (n : ℕ) : mu.real {x} / 2 ≤ sigma.real (S n) := by
    have heq := hhalf x (x + v n) hx (by linarith only [hvpos n])
    have hi : 0 ≤ mu.real (Ioo x (x + v n)) := ENNReal.toReal_nonneg
    have hb : 0 ≤ mu.real {x + v n} := ENNReal.toReal_nonneg
    change mu.real {x} / 2 ≤ sigma.real (Ioo x (x + v n))
    linarith only [heq, hi, hb]
  have hzero : mu.real {x} = 0 := by
    have h := ge_of_tendsto' hreal hle
    have hn : 0 ≤ mu.real {x} := ENNReal.toReal_nonneg
    linarith only [h, hn]
  exact ((ENNReal.toReal_eq_zero_iff _).mp hzero).resolve_right (measure_ne_top mu {x})

private theorem measure_Icc_eq_Ioo_of_endpoint_atoms
    (mu : Measure ℝ) (a b : ℝ) (ha : mu ({a} : Set ℝ) = 0) (hb : mu ({b} : Set ℝ) = 0) :
    mu (Icc a b) = mu (Ioo a b) := by
  have hae : ∀ᵐ x ∂mu, x ≠ a := by rw [ae_iff]; simpa only [not_not] using ha
  have hbe : ∀ᵐ x ∂mu, x ≠ b := by rw [ae_iff]; simpa only [not_not] using hb
  apply measure_congr
  filter_upwards [hae, hbe] with x hxa hxb
  constructor
  · intro h
    exact ⟨lt_of_le_of_ne h.1 hxa.symm, lt_of_le_of_ne h.2 hxb⟩
  · intro h
    exact ⟨h.1.le, h.2.le⟩

/-- The actual half-endpoint formula implies exact equality on every
positive closed interval, after deriving the first measure's atoms vanish. -/
theorem positive_Icc_eq_of_half_interval
    (mu sigma : Measure ℝ) [IsFiniteMeasure mu] [IsFiniteMeasure sigma]
    (hsigma : ∀ x : ℝ, sigma ({x} : Set ℝ) = 0)
    (hhalf : ∀ a b : ℝ, 0 < a → a < b →
      mu.real (Ioo a b) + (mu.real {a} + mu.real {b}) / 2 = sigma.real (Ioo a b))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : mu (Icc a b) = sigma (Icc a b) := by
  have hb : 0 < b := ha.trans_le hab
  have hma := positive_atom_zero_of_half_interval mu sigma hhalf ha
  have hmb := positive_atom_zero_of_half_interval mu sigma hhalf hb
  by_cases heq : a = b
  · subst b
    simpa only [Icc_self] using hma.trans (hsigma a).symm
  have hlt : a < b := lt_of_le_of_ne hab heq
  have hopen : mu (Ioo a b) = sigma (Ioo a b) := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top mu _) (measure_ne_top sigma _)).mp
    have h := hhalf a b ha hlt
    simpa only [measureReal_def, hma, hmb, ENNReal.toReal_zero, add_zero, zero_add, zero_div] using h
  rw [measure_Icc_eq_Ioo_of_endpoint_atoms mu a b hma hmb,
    measure_Icc_eq_Ioo_of_endpoint_atoms sigma a b (hsigma a) (hsigma b), hopen]

private theorem positive_log_Icc (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hpos : mu (Iic 0) = 0) (a b : ℝ) :
    Measure.map Real.log mu (Icc a b) = mu (Icc (Real.exp a) (Real.exp b)) := by
  rw [Measure.map_apply Real.measurable_log measurableSet_Icc]
  have hae : ∀ᵐ x ∂mu, 0 < x := by rw [ae_iff]; simpa only [not_lt] using hpos
  apply measure_congr
  filter_upwards [hae] with x hx
  constructor
  · intro h
    constructor
    · have hh := Real.exp_le_exp.mpr h.1
      simpa only [Real.exp_log hx] using hh
    · have hh := Real.exp_le_exp.mpr h.2
      simpa only [Real.exp_log hx] using hh
  · intro h
    constructor
    · have hh := Real.log_le_log (Real.exp_pos a) h.1
      simpa only [Real.log_exp] using hh
    · have hh := Real.log_le_log hx h.2
      simpa only [Real.log_exp] using hh

private theorem map_exp_log_positive (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hpos : mu (Iic 0) = 0) : Measure.map Real.exp (Measure.map Real.log mu) = mu := by
  rw [Measure.map_map Real.measurable_exp Real.measurable_log]
  have hae : ∀ᵐ x ∂mu, 0 < x := by rw [ae_iff]; simpa only [not_lt] using hpos
  calc
    Measure.map (Real.exp ∘ Real.log) mu = Measure.map id mu := by
      apply Measure.map_congr
      filter_upwards [hae] with x hx
      exact Real.exp_log hx
    _ = mu := Measure.map_id

/-- Log transport supplies a whole-line interval generating class, so
positive-axis interval data give equality of the actual finite measures. -/
theorem positive_measure_eq_of_half_interval
    (mu sigma : Measure ℝ) [IsFiniteMeasure mu] [IsFiniteMeasure sigma]
    (hmuPos : mu (Iic 0) = 0) (hsigmaPos : sigma (Iic 0) = 0)
    (hsigma : ∀ x : ℝ, sigma ({x} : Set ℝ) = 0)
    (hhalf : ∀ a b : ℝ, 0 < a → a < b →
      mu.real (Ioo a b) + (mu.real {a} + mu.real {b}) / 2 = sigma.real (Ioo a b)) :
    mu = sigma := by
  have hlog : Measure.map Real.log mu = Measure.map Real.log sigma := by
    apply Measure.ext_of_Icc
    intro a b hab
    rw [positive_log_Icc mu hmuPos, positive_log_Icc sigma hsigmaPos]
    exact positive_Icc_eq_of_half_interval mu sigma hsigma hhalf (Real.exp_pos a)
      (Real.exp_le_exp.mpr hab)
  have h := congrArg (Measure.map Real.exp) hlog
  rw [map_exp_log_positive mu hmuPos, map_exp_log_positive sigma hsigmaPos] at h
  exact h

end
end ImbalancedChen.Part3.HalfEndpointPositiveMeasureUniqueness20261025a
