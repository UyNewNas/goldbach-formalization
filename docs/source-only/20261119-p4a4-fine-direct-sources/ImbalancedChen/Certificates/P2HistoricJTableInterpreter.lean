import ImbalancedChen.P2HistoricI80DivisionSoundness
import ImbalancedChen.Certificates.RationalLogCertificate
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact Q80 JTable prefix sums and outward clamped lookup

SOURCE ONLY / UNCOMPILED.  Literal source: `certify_conservative_chen.py`,
SHA256 67b9429667e18786058e0fe58676fbe09d556868468f1281166cac2b55f8604e.
The source stores integer prefix sums of per-cell rounded products, with
left sample initially I(0), right samples log(v-1)/v, and step I(2/n).
Queries clamp BOTH fixed-point endpoints before floor/ceiling indexing.

The logarithm algorithm is an explicit semantic input contract on I80
arguments.  There is no assumed JTable endpoint or target integral bound.
The actual function enclosed is J(min(s,5)) for every real s>=3.
-/

namespace ImbalancedChen.Certificates.P2HistoricJTableInterpreter

open P2HistoricQ80DefectLookup P2HistoricI80DivisionSoundness
open MeasureTheory Set
open scoped Interval BigOperators

noncomputable def q (v : ℝ) : ℝ := Real.log (v - 1) / v

noncomputable def J (s : ℝ) : ℝ := ∫ v in (2 : ℝ)..(s - 1), q v

theorem log_three_lt_four_thirds : Real.log (3 : ℝ) < 4 / 3 := by
  let c : RationalLogCertificate := ⟨3, 2, 0, 7 / 6⟩
  have hc : c.check = true := by
    norm_num [c, RationalLogCertificate.check, RationalLogCertificate.Valid,
      logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ]
  have hu := (c.check_sound hc).2
  norm_num [c] at hu
  linarith

theorem continuousOn_q : ContinuousOn q (Icc (2 : ℝ) 4) := by
  apply ((continuousOn_id.sub continuousOn_const).log ?_).div continuousOn_id ?_
  · intro v hv
    exact ne_of_gt (by linarith [hv.1] : 0 < v - 1)
  · intro v hv
    exact ne_of_gt (by linarith [hv.1] : 0 < v)

theorem hasDerivAt_q {v : ℝ} (hv : v ∈ Icc (2 : ℝ) 4) :
    HasDerivAt q ((v / (v - 1) - Real.log (v - 1)) / v ^ 2) v := by
  have hv0 : v ≠ 0 := ne_of_gt (by linarith [hv.1] : 0 < v)
  have hv1 : v - 1 ≠ 0 := ne_of_gt (by linarith [hv.1] : 0 < v - 1)
  have hd := ((Real.hasDerivAt_log hv1).comp v ((hasDerivAt_id v).sub_const 1)).div
    (hasDerivAt_id v) hv0
  apply hd.congr_deriv
  dsimp
  field_simp [hv0, hv1] <;> ring

theorem q_derivative_nonneg {v : ℝ} (hv : v ∈ Icc (2 : ℝ) 4) :
    0 ≤ (v / (v - 1) - Real.log (v - 1)) / v ^ 2 := by
  have hv1 : 0 < v - 1 := by linarith [hv.1]
  have hl : Real.log (v - 1) ≤ Real.log 3 :=
    Real.log_le_log hv1 (by linarith [hv.2])
  have hr : (4 / 3 : ℝ) ≤ v / (v - 1) := by
    apply (le_div_iff₀ hv1).mpr
    linarith [hv.2]
  exact div_nonneg (by linarith [log_three_lt_four_thirds]) (sq_nonneg v)

theorem q_monotone : MonotoneOn q (Icc (2 : ℝ) 4) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (2 : ℝ) 4) continuousOn_q
    (f' := fun v => (v / (v - 1) - Real.log (v - 1)) / v ^ 2)
  · intro v hv
    exact (hasDerivAt_q (interior_subset hv)).hasDerivWithinAt
  · intro v hv
    exact q_derivative_nonneg (interior_subset hv)

theorem q_nonneg {v : ℝ} (hv : v ∈ Icc (2 : ℝ) 4) : 0 ≤ q v := by
  exact div_nonneg (Real.log_nonneg (by linarith [hv.1])) (by linarith [hv.1])

theorem q_intervalIntegrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 4) :
    IntervalIntegrable q volume a b := by
  apply (continuousOn_q.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab

def node (n j : ℕ) : ℚ := 2 + 2 * (j : ℚ) / n

theorem node_zero (n : ℕ) : node n 0 = 2 := by simp [node]

theorem node_bounds {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (2 : ℚ) ≤ node n j ∧ node n j ≤ 4 := by
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have hjQ : (j : ℚ) ≤ n := by exact_mod_cast hj
  constructor
  · dsimp [node]
    have h : (0 : ℚ) ≤ 2 * (j : ℚ) / n := by positivity
    linarith
  · dsimp [node]
    have h := (div_le_iff₀ hnQ).mpr (show (2 : ℚ) * j ≤ 2 * n by linarith)
    linarith

theorem node_mono {n : ℕ} (hn : 0 < n) {i j : ℕ} (hij : i ≤ j) :
    node n i ≤ node n j := by
  unfold node
  apply add_le_add_left
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (by norm_num))
    (by exact_mod_cast hn.le)

theorem node_step (n j : ℕ) : node n (j + 1) - node n j = 2 / (n : ℚ) := by
  simp only [node, Nat.cast_add, Nat.cast_one]
  ring

theorem node_real_bounds {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (node n j : ℝ) ∈ Icc (2 : ℝ) 4 := by exact_mod_cast node_bounds hn hj

/-- Precisely the external logarithm obligation; no J endpoint occurs. -/
def LogContract (logI : I80 → I80) : Prop :=
  ∀ (a : I80) (x : ℝ), 0 < a.lo → 0 < x → a.Contains x →
    (logI a).Contains (Real.log x)

def step (n : ℕ) : I80 := I80.point (2 / (n : ℚ))
def gridPoint (n j : ℕ) : I80 := I80.point (node n j)

def right (logI : I80 → I80) (n j : ℕ) : I80 :=
  historicalDiv (logI ((gridPoint n j).sub (I80.point 1))) (gridPoint n j)

def left (logI : I80 → I80) (n j : ℕ) : I80 :=
  if j = 0 then I80.point 0 else right logI n j

def lowerCell (logI : I80 → I80) (n j : ℕ) : ℤ :=
  ((left logI n j).mul (step n)).lo

def upperCell (logI : I80 → I80) (n j : ℕ) : ℤ :=
  ((right logI n (j + 1)).mul (step n)).hi

def cell (logI : I80 → I80) (n j : ℕ) : I80 :=
  ⟨lowerCell logI n j, upperCell logI n j⟩

/-- Literal arrays are represented by their common integer prefix state. -/
def prefix (logI : I80 → I80) (n : ℕ) : ℕ → I80
  | 0 => ⟨0, 0⟩
  | k + 1 => (prefix logI n k).add (cell logI n k)

theorem prefix_lower_sum (logI : I80 → I80) (n k : ℕ) :
    (prefix logI n k).lo = ∑ j ∈ Finset.range k, lowerCell logI n j := by
  induction k with
  | zero => simp [prefix]
  | succ k hk => simp [prefix, I80.add, hk, Finset.sum_range_succ]

theorem prefix_upper_sum (logI : I80 → I80) (n k : ℕ) :
    (prefix logI n k).hi = ∑ j ∈ Finset.range k, upperCell logI n j := by
  induction k with
  | zero => simp [prefix]
  | succ k hk => simp [prefix, I80.add, hk, Finset.sum_range_succ]

theorem gridPoint_guards {n : ℕ} (hn : 0 < n) (j : ℕ) :
    0 < (gridPoint n j).lo ∧ 0 < ((gridPoint n j).sub (I80.point 1)).lo := by
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have hnode : (2 : ℚ) ≤ node n j := by
    dsimp [node]
    have h : (0 : ℚ) ≤ 2 * (j : ℚ) / n := by positivity
    linarith
  have hf := Int.floor_mono (mul_le_mul_of_nonneg_right hnode Q_pos.le)
  have htwo : ⌊(2 : ℚ) * (Q : ℚ)⌋ = 2 * (Q : ℤ) := by norm_num [Q]
  rw [htwo] at hf
  have hone : (I80.point 1).hi = (Q : ℤ) := by
    norm_num [I80.point, I80.ofEnclosure, P2DirectedLogRounding.Enclosure.point, Q]
  have hQ : (0 : ℤ) < (Q : ℤ) := by norm_num [Q]
  change 2 * (Q : ℤ) ≤ (gridPoint n j).lo at hf
  constructor
  · linarith
  · simp only [I80.sub, I80.add, I80.neg, hone]
    linarith

theorem right_contains (logI : I80 → I80) (hlog : LogContract logI)
    {n j : ℕ} (hn : 0 < n) :
    (right logI n j).Contains (q (node n j : ℝ)) := by
  have hp := I80.point_contains (node n j)
  have hx := I80.sub_contains hp (I80.point_contains 1)
  have hnode : (2 : ℚ) ≤ node n j := by
    have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
    dsimp [node]
    have h : (0 : ℚ) ≤ 2 * (j : ℚ) / n := by positivity
    linarith
  have hnr : (2 : ℝ) ≤ (node n j : ℝ) := by exact_mod_cast hnode
  have hl := hlog ((gridPoint n j).sub (I80.point 1)) ((node n j : ℝ) - 1)
    (gridPoint_guards hn j).2 (by linarith) (by simpa only [Rat.cast_one] using hx)
  exact historicalDiv_contains hl hp (gridPoint_guards hn j).1

theorem left_contains (logI : I80 → I80) (hlog : LogContract logI)
    {n j : ℕ} (hn : 0 < n) : (left logI n j).Contains (q (node n j : ℝ)) := by
  by_cases hj : j = 0
  · subst j
    simpa [left, node, q] using I80.point_contains 0
  · simpa only [left, if_neg hj] using right_contains logI hlog hn

theorem cell_contains (logI : I80 → I80) (hlog : LogContract logI)
    {n j : ℕ} (hn : 0 < n) (hj : j < n) :
    (cell logI n j).Contains (∫ v in (node n j : ℝ)..(node n (j + 1) : ℝ), q v) := by
  have hl := I80.mul_contains (left_contains logI hlog hn (j := j))
    (I80.point_contains (2 / (n : ℚ)))
  have hu := I80.mul_contains (right_contains logI hlog hn (j := j + 1))
    (I80.point_contains (2 / (n : ℚ)))
  have ha := node_real_bounds hn hj.le
  have hb := node_real_bounds hn (Nat.succ_le_of_lt hj)
  have hab : (node n j : ℝ) ≤ (node n (j + 1) : ℝ) := by
    exact_mod_cast node_mono hn (Nat.le_succ j)
  have hint := q_intervalIntegrable ha.1 hab hb.2
  have hstep : (node n (j + 1) : ℝ) - (node n j : ℝ) = ((2 / (n : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast node_step n j
  have hleft : q (node n j : ℝ) * ((2 / (n : ℚ) : ℚ) : ℝ) ≤
      ∫ v in (node n j : ℝ)..(node n (j + 1) : ℝ), q v := by
    have h := intervalIntegral.integral_mono_on hab
      (continuous_const.intervalIntegrable _ _) hint
      (fun v hv => q_monotone ha ⟨ha.1.trans hv.1, hv.2.trans hb.2⟩ hv.1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, hstep, mul_comm] using h
  have hright : (∫ v in (node n j : ℝ)..(node n (j + 1) : ℝ), q v) ≤
      q (node n (j + 1) : ℝ) * ((2 / (n : ℚ) : ℚ) : ℝ) := by
    have h := intervalIntegral.integral_mono_on hab hint
      (continuous_const.intervalIntegrable _ _)
      (fun v hv => q_monotone ⟨ha.1.trans hv.1, hv.2.trans hb.2⟩ hb hv.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, hstep, mul_comm] using h
  exact ⟨hl.1.trans hleft, hright.trans hu.2⟩

theorem prefix_contains (logI : I80 → I80) (hlog : LogContract logI)
    {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    (prefix logI n k).Contains (∫ v in (2 : ℝ)..(node n k : ℝ), q v) := by
  revert hk
  induction k with
  | zero => intro _; simp [prefix, node, I80.Contains, I80.enclosure, I80.decodeLo, I80.decodeHi,
      P2DirectedLogRounding.Enclosure.Contains]
  | succ k ih =>
      intro hk
      have hkn : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hprev := ih (Nat.le_of_lt hkn)
      have hcell := cell_contains logI hlog hn hkn
      have ha := node_real_bounds hn (Nat.le_of_lt hkn)
      have hb := node_real_bounds hn hk
      have hab : (node n k : ℝ) ≤ (node n (k + 1) : ℝ) := by
        exact_mod_cast node_mono hn (Nat.le_succ k)
      have heq := intervalIntegral.integral_add_adjacent_intervals
        (q_intervalIntegrable le_rfl ha.1 ha.2) (q_intervalIntegrable ha.1 hab hb.2)
      rw [← heq]
      exact I80.add_contains hprev hcell

theorem Q_real_pos : (0 : ℝ) < (Q : ℝ) := by norm_num [Q]

theorem contains_iff (a : I80) (x : ℝ) : a.Contains x ↔
    (a.lo : ℝ) / (Q : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ) / (Q : ℝ) := by
  simp [I80.Contains, I80.enclosure, I80.decodeLo, I80.decodeHi,
    P2DirectedLogRounding.Enclosure.Contains]

def clamp (z : ℤ) : ℤ := max 0 (min (2 * (Q : ℤ)) (z - 3 * (Q : ℤ)))

def lowerIndex (n : ℕ) (s : I80) : ℕ :=
  (clamp s.lo * (n : ℤ) / (2 * (Q : ℤ))).toNat

def upperIndex (n : ℕ) (s : I80) : ℕ :=
  (ceilDiv (clamp s.hi * (n : ℤ)) (2 * (Q : ℤ))).toNat

def lookup (logI : I80 → I80) (n : ℕ) (s : I80) : I80 :=
  ⟨(prefix logI n (lowerIndex n s)).lo, (prefix logI n (upperIndex n s)).hi⟩

def buildCheck (logI : I80 → I80) (n : ℕ) : Bool :=
  decide (0 < n ∧ (logI (I80.point 3)).hi < (I80.point (4 / 3)).lo)

theorem clamp_bounds (z : ℤ) : 0 ≤ clamp z ∧ clamp z ≤ 2 * (Q : ℤ) := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num [Q]) (min_le_left _ _)

private theorem floor_ceil_index_arithmetic (n : ℕ) (a d : ℤ)
    (hd : 0 < d) (ha : 0 ≤ a) (han : a ≤ (n : ℤ) * d) :
    (((a / d).toNat : ℕ) : ℤ) * d ≤ a ∧
      a ≤ (((ceilDiv a d).toNat : ℕ) : ℤ) * d ∧
      (a / d).toNat ≤ n ∧ (ceilDiv a d).toNat ≤ n := by
  have hl0 : 0 ≤ a / d := Int.ediv_nonneg ha hd.le
  have hlf : a / d * d ≤ a := Int.ediv_mul_le a hd.ne'
  have huf : a ≤ ceilDiv a d * d := by
    have h := Int.ediv_mul_le (-a) hd.ne'
    dsimp [ceilDiv]
    nlinarith
  have hu0 : 0 ≤ ceilDiv a d := by
    by_contra hneg
    have hh : ceilDiv a d * d < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hd
    linarith
  have hln : a / d ≤ (n : ℤ) := Int.ediv_le_of_le_mul hd han
  have hun : ceilDiv a d ≤ (n : ℤ) := by
    have hneg : -(n : ℤ) ≤ (-a) / d := (Int.le_ediv_iff_mul_le hd).mpr (by nlinarith)
    dsimp [ceilDiv]
    linarith
  have hcl : (((a / d).toNat : ℕ) : ℤ) = a / d := Int.toNat_of_nonneg hl0
  have hcu : (((ceilDiv a d).toNat : ℕ) : ℤ) = ceilDiv a d := Int.toNat_of_nonneg hu0
  refine ⟨by simpa only [hcl] using hlf, by simpa only [hcu] using huf, ?_, ?_⟩
  · have h : (((a / d).toNat : ℕ) : ℤ) ≤ (n : ℤ) := by rw [hcl]; exact hln
    exact_mod_cast h
  · have h : (((ceilDiv a d).toNat : ℕ) : ℤ) ≤ (n : ℤ) := by rw [hcu]; exact hun
    exact_mod_cast h

/-- Both actual array indices are within [0,n], including the endpoint5. -/
theorem index_arithmetic (n : ℕ) (s : I80) :
    lowerIndex n s ≤ n ∧ upperIndex n s ≤ n ∧
      (lowerIndex n s : ℤ) * (2 * (Q : ℤ)) ≤ clamp s.lo * (n : ℤ) ∧
      clamp s.hi * (n : ℤ) ≤ (upperIndex n s : ℤ) * (2 * (Q : ℤ)) := by
  have hD : (0 : ℤ) < 2 * (Q : ℤ) := by norm_num [Q]
  have hn : (0 : ℤ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hlow := floor_ceil_index_arithmetic n (clamp s.lo * (n : ℤ)) (2 * (Q : ℤ))
    hD (mul_nonneg (clamp_bounds s.lo).1 hn)
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right (clamp_bounds s.lo).2 hn)
  have hhigh := floor_ceil_index_arithmetic n (clamp s.hi * (n : ℤ)) (2 * (Q : ℤ))
    hD (mul_nonneg (clamp_bounds s.hi).1 hn)
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right (clamp_bounds s.hi).2 hn)
  exact ⟨hlow.2.2.1, hhigh.2.2.2, hlow.1, hhigh.2.1⟩

private theorem int_cast_min (a b : ℤ) : ((min a b : ℤ) : ℝ) = min (a : ℝ) (b : ℝ) := by
  rcases le_total a b with h | h
  · have hr : (a : ℝ) ≤ b := by exact_mod_cast h
    simp only [min_eq_left h, min_eq_left hr]
  · have hr : (b : ℝ) ≤ a := by exact_mod_cast h
    simp only [min_eq_right h, min_eq_right hr]

private theorem int_cast_max (a b : ℤ) : ((max a b : ℤ) : ℝ) = max (a : ℝ) (b : ℝ) := by
  rcases le_total a b with h | h
  · have hr : (a : ℝ) ≤ b := by exact_mod_cast h
    simp only [max_eq_right h, max_eq_right hr]
  · have hr : (b : ℝ) ≤ a := by exact_mod_cast h
    simp only [max_eq_left h, max_eq_left hr]

noncomputable def realClamp (z : ℝ) : ℝ :=
  max 0 (min (2 * (Q : ℝ)) (z - 3 * (Q : ℝ)))

theorem cast_clamp (z : ℤ) : (clamp z : ℝ) = realClamp (z : ℝ) := by
  simp [clamp, realClamp, int_cast_min, int_cast_max]

theorem realClamp_mono : Monotone realClamp := by
  intro a b hab
  exact max_le_max le_rfl (min_le_min le_rfl (sub_le_sub_right hab _))

theorem realClamp_scaled {s : ℝ} (hs : 3 ≤ s) :
    realClamp (s * (Q : ℝ)) = (min s 5 - 3) * (Q : ℝ) := by
  by_cases h5 : s ≤ 5
  · have hzero : 0 ≤ s * (Q : ℝ) - 3 * (Q : ℝ) :=
      sub_nonneg.mpr (mul_le_mul_of_nonneg_right hs Q_real_pos.le)
    have htwo : s * (Q : ℝ) - 3 * (Q : ℝ) ≤ 2 * (Q : ℝ) := by
      have h := mul_le_mul_of_nonneg_right h5 Q_real_pos.le
      linarith
    rw [realClamp, min_eq_right htwo, max_eq_right hzero, min_eq_left h5]
    ring
  · have htwo : 2 * (Q : ℝ) ≤ s * (Q : ℝ) - 3 * (Q : ℝ) := by
      have h := mul_le_mul_of_nonneg_right (le_of_not_ge h5) Q_real_pos.le
      linarith
    rw [realClamp, min_eq_left htwo, max_eq_right (by positivity),
      min_eq_right (le_of_not_ge h5)]
    ring

theorem clamped_endpoints_enclose {sI : I80} {s : ℝ} (hsI : sI.Contains s) (hs : 3 ≤ s) :
    (clamp sI.lo : ℝ) ≤ (min s 5 - 3) * (Q : ℝ) ∧
      (min s 5 - 3) * (Q : ℝ) ≤ (clamp sI.hi : ℝ) := by
  obtain ⟨hl, hu⟩ := (contains_iff sI s).mp hsI
  have hlow := realClamp_mono ((div_le_iff₀ Q_real_pos).mp hl)
  have hhigh := realClamp_mono ((le_div_iff₀ Q_real_pos).mp hu)
  rw [← cast_clamp, realClamp_scaled hs] at hlow
  rw [realClamp_scaled hs, ← cast_clamp] at hhigh
  exact ⟨hlow, hhigh⟩

theorem lookup_node_bracket {n : ℕ} (hn : 0 < n) {sI : I80} {s : ℝ}
    (hsI : sI.Contains s) (hs : 3 ≤ s) :
    (node n (lowerIndex n sI) : ℝ) ≤ min s 5 - 1 ∧
      min s 5 - 1 ≤ (node n (upperIndex n sI) : ℝ) := by
  obtain ⟨_, _, hil, hih⟩ := index_arithmetic n sI
  have hilR : (lowerIndex n sI : ℝ) * (2 * (Q : ℝ)) ≤
      (clamp sI.lo : ℝ) * (n : ℝ) := by exact_mod_cast hil
  have hihR : (clamp sI.hi : ℝ) * (n : ℝ) ≤
      (upperIndex n sI : ℝ) * (2 * (Q : ℝ)) := by exact_mod_cast hih
  have hcl := clamped_endpoints_enclose hsI hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo : 2 * (lowerIndex n sI : ℝ) ≤ (min s 5 - 3) * (n : ℝ) := by
    apply (mul_le_mul_right Q_real_pos).mp
    calc
      (2 * (lowerIndex n sI : ℝ)) * (Q : ℝ) =
          (lowerIndex n sI : ℝ) * (2 * (Q : ℝ)) := by ring
      _ ≤ (clamp sI.lo : ℝ) * (n : ℝ) := hilR
      _ ≤ ((min s 5 - 3) * (Q : ℝ)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hcl.1 hnR.le
      _ = ((min s 5 - 3) * (n : ℝ)) * (Q : ℝ) := by ring
  have hhi : (min s 5 - 3) * (n : ℝ) ≤ 2 * (upperIndex n sI : ℝ) := by
    apply (mul_le_mul_right Q_real_pos).mp
    calc
      ((min s 5 - 3) * (n : ℝ)) * (Q : ℝ) =
          ((min s 5 - 3) * (Q : ℝ)) * (n : ℝ) := by ring
      _ ≤ (clamp sI.hi : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_right hcl.2 hnR.le
      _ ≤ (upperIndex n sI : ℝ) * (2 * (Q : ℝ)) := hihR
      _ = (2 * (upperIndex n sI : ℝ)) * (Q : ℝ) := by ring
  have hlo' := (div_le_iff₀ hnR).mpr hlo
  have hhi' := (le_div_iff₀ hnR).mpr hhi
  constructor <;> simp only [node, Rat.cast_add, Rat.cast_div, Rat.cast_mul,
    Rat.cast_ofNat, Rat.cast_natCast]
  · linarith
  · linarith

theorem integral_mono_endpoint {a b : ℝ} (ha : a ∈ Icc (2 : ℝ) 4)
    (hb : b ∈ Icc (2 : ℝ) 4) (hab : a ≤ b) :
    (∫ v in (2 : ℝ)..a, q v) ≤ ∫ v in (2 : ℝ)..b, q v := by
  apply intervalIntegral.integral_mono_interval le_rfl ha.1 hab
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact q_nonneg ⟨hv.1.le, hv.2.trans hb.2⟩
  · exact q_intervalIntegrable le_rfl hb.1 hb.2

/-- The exact original lookup includes entire endpoint cells.  It encloses
the clamped monotone extension even if Q80 outward input rounding passes5. -/
theorem lookup_contains (logI : I80 → I80) (hlog : LogContract logI)
    {n : ℕ} (hn : 0 < n) {sI : I80} {s : ℝ} (hsI : sI.Contains s) (hs : 3 ≤ s) :
    (lookup logI n sI).Contains (J (min s 5)) := by
  obtain ⟨hil, hih, _, _⟩ := index_arithmetic n sI
  have hl := prefix_contains logI hlog hn hil
  have hu := prefix_contains logI hlog hn hih
  have hnodes := lookup_node_bracket hn hsI hs
  have htarget : min s 5 - 1 ∈ Icc (2 : ℝ) 4 := by
    have hmin : 3 ≤ min s 5 := le_min hs (by norm_num)
    exact ⟨by linarith, by linarith [min_le_right s (5 : ℝ)]⟩
  exact ⟨hl.1.trans (integral_mono_endpoint (node_real_bounds hn hil) htarget hnodes.1),
    (integral_mono_endpoint htarget (node_real_bounds hn hih) hnodes.2).trans hu.2⟩

theorem lookup_contains_original_domain (logI : I80 → I80) (hlog : LogContract logI)
    {n : ℕ} (hn : 0 < n) {sI : I80} {s : ℝ} (hsI : sI.Contains s)
    (hs : s ∈ Icc (3 : ℝ) 5) : (lookup logI n sI).Contains (J s) := by
  simpa only [min_eq_left hs.2] using lookup_contains logI hlog hn hsI hs.1

theorem checked_lookup_contains (logI : I80 → I80) (hlog : LogContract logI)
    {n : ℕ} (hcheck : buildCheck logI n = true) {sI : I80} {s : ℝ}
    (hsI : sI.Contains s) (hs : 3 ≤ s) :
    (lookup logI n sI).Contains (J (min s 5)) := by
  have hv : 0 < n ∧ (logI (I80.point 3)).hi < (I80.point (4 / 3)).lo :=
    of_decide_eq_true hcheck
  exact lookup_contains logI hlog hv.1 hsI hs

end ImbalancedChen.Certificates.P2HistoricJTableInterpreter
