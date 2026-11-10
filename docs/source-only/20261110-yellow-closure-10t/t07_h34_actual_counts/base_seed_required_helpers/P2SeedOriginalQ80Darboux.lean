import ImbalancedChen.P2HistoricLogPointInterpreter
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
SOURCE ONLY / UNCOMPILED / FINITE BODIES UNEVALUATED.

The original Q80 `integrate1` rule, with its actual logarithm backend.
This module proves expression and Darboux soundness. No real integral
bound, saved endpoint, adopted seed, or arithmetic count is an input.
The guards are rational/integer facts about the evaluated expressions.
The source is certify_conservative_chen.py:28-183 at its recorded pin.
-/

namespace ImbalancedChen.P2SeedOriginalQ80Darboux

noncomputable section
open Set MeasureTheory
open scoped Interval
open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricLogPointInterpreter
open Certificates.P2DirectedLogRounding

def intervalLog (x : I80) : I80 :=
  ⟨(logPoint x.lo).lo, (logPoint x.hi).hi⟩

theorem intervalLog_contains {x : I80} {v : ℝ}
    (hx : x.Contains v) (hlo : 0 < x.lo) :
    (intervalLog x).Contains (Real.log v) := by
  obtain ⟨hl, hu⟩ := (contains_iff x v).1 hx
  have hl0 : 0 < decode x.lo := div_pos (by exact_mod_cast hlo) Q_real_pos
  have hv0 : 0 < v := hl0.trans_le hl
  have hhi : 0 < x.hi := by
    have h := (lt_div_iff₀ Q_real_pos).1 (hv0.trans_le hu)
    exact_mod_cast (show (0 : ℝ) < x.hi by simpa [decode] using h)
  have hL := (contains_iff _ _).1 (logPoint_contains hlo)
  have hU := (contains_iff _ _).1 (logPoint_contains hhi)
  exact (contains_iff _ _).2
    ⟨hL.1.trans (Real.log_le_log hl0 hl),
      (Real.log_le_log hv0 hu).trans hU.2⟩

/-- Only the source operations used in the two seed certificates. -/
inductive Expr where
  | var : Expr
  | rat : ℚ → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  | log : Expr → Expr
  deriving DecidableEq, Repr

def Expr.real : Expr → ℝ → ℝ
  | .var, u => u
  | .rat q, _ => q
  | .add a b, u => a.real u + b.real u
  | .sub a b, u => a.real u - b.real u
  | .mul a b, u => a.real u * b.real u
  | .div a b, u => a.real u / b.real u
  | .log a, u => Real.log (a.real u)

def Expr.eval : Expr → I80 → I80
  | .var, x => x
  | .rat q, _ => I80.point q
  | .add a b, x => (a.eval x).add (b.eval x)
  | .sub a b, x => (a.eval x).sub (b.eval x)
  | .mul a b, x => (a.eval x).mul (b.eval x)
  | .div a b, x => (a.eval x).div (b.eval x)
  | .log a, x => intervalLog (a.eval x)

def Expr.Valid : Expr → I80 → Prop
  | .var, _ => True
  | .rat _, _ => True
  | .add a b, x => a.Valid x ∧ b.Valid x
  | .sub a b, x => a.Valid x ∧ b.Valid x
  | .mul a b, x => a.Valid x ∧ b.Valid x
  | .div a b, x => a.Valid x ∧ b.Valid x ∧ 0 < (b.eval x).lo
  | .log a, x => a.Valid x ∧ 0 < (a.eval x).lo

instance (e : Expr) (x : I80) : Decidable (e.Valid x) := by
  induction e <;> simp only [Expr.Valid] <;> infer_instance

theorem Expr.eval_contains (e : Expr) {x : I80} {u : ℝ}
    (hx : x.Contains u) (h : e.Valid x) : (e.eval x).Contains (e.real u) := by
  revert h
  induction e with
  | var => exact fun _ => hx
  | rat q => exact fun _ => I80.point_contains q
  | add a b ha hb => exact fun h => I80.add_contains (ha h.1) (hb h.2)
  | sub a b ha hb => exact fun h => I80.sub_contains (ha h.1) (hb h.2)
  | mul a b ha hb => exact fun h => I80.mul_contains (ha h.1) (hb h.2)
  | div a b ha hb => exact fun h => I80.div_contains (ha h.1) (hb h.2.1) h.2.2
  | log a ha => exact fun h => intervalLog_contains (ha h.1) h.2

theorem Expr.eval_positive (e : Expr) {x : I80} {u : ℝ}
    (hx : x.Contains u) (h : e.Valid x) (hlo : 0 < (e.eval x).lo) :
    0 < e.real u := by
  have hl := ((contains_iff _ _).1 (e.eval_contains hx h)).1
  exact (div_pos (by exact_mod_cast hlo) Q_real_pos).trans_le hl

theorem Expr.continuousOn (e : Expr) (K : Set ℝ) (x : I80)
    (hx : ∀ u ∈ K, x.Contains u) (h : e.Valid x) : ContinuousOn e.real K := by
  revert h
  induction e with
  | var => exact fun _ => continuousOn_id
  | rat q => exact fun _ => continuousOn_const
  | add a b ha hb => exact fun h => (ha h.1).add (hb h.2)
  | sub a b ha hb => exact fun h => (ha h.1).sub (hb h.2)
  | mul a b ha hb => exact fun h => (ha h.1).mul (hb h.2)
  | div a b ha hb =>
      intro h
      exact (ha h.1).div (hb h.2.1)
        (fun u hu => (b.eval_positive (hx u hu) h.2.1 h.2.2).ne')
  | log a ha =>
      intro h
      exact (ha h.1).log
        (fun u hu => (a.eval_positive (hx u hu) h.1 h.2).ne')

def node (a b : ℚ) (n j : ℕ) : ℚ := a + (b-a)*(j:ℚ)/n
def step (a b : ℚ) (n : ℕ) : ℚ := (b-a)/n
def gridBox (a b : ℚ) (n j : ℕ) : I80 :=
  I80.ofEnclosure ⟨node a b n j, node a b n (j+1)⟩

def CellsValid (e : Expr) (a b : ℚ) (n : ℕ) : Prop :=
  ∀ j : Fin n, e.Valid (gridBox a b n j.val)

instance (e : Expr) (a b : ℚ) (n : ℕ) : Decidable (CellsValid e a b n) := by
  unfold CellsValid
  infer_instance

def rawSum (e : Expr) (a b : ℚ) (n : ℕ) : ℕ → I80
  | 0 => I80.raw 0
  | j+1 => (rawSum e a b n j).add (e.eval (gridBox a b n j))

/-- The source multiplies the SUM of interval endpoints by the common
rational width once. It does not round every cell integral separately. -/
def darboux (e : Expr) (a b : ℚ) (n : ℕ) : I80 :=
  (rawSum e a b n n).mul (I80.point (step a b n))

theorem node_zero (a b : ℚ) (n : ℕ) : node a b n 0 = a := by simp [node]
theorem node_top (a b : ℚ) {n : ℕ} (hn : 0 < n) : node a b n n = b := by
  have hn0 : (n:ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp [node]
  field_simp [hn0]
  ring

theorem node_step (a b : ℚ) (n j : ℕ) :
    node a b n (j+1)-node a b n j = step a b n := by
  simp only [node,step,Nat.cast_add,Nat.cast_one]
  ring

theorem step_pos {a b : ℚ} {n : ℕ} (hab : a < b) (hn : 0 < n) :
    0 < step a b n := div_pos (sub_pos.mpr hab) (by exact_mod_cast hn)

theorem gridBox_contains (a b : ℚ) (n j : ℕ) {u : ℝ}
    (hu : u ∈ Icc (node a b n j:ℝ) (node a b n (j+1):ℝ)) :
    (gridBox a b n j).Contains u := I80.ofEnclosure_contains hu

theorem positive_cell_integrable (e : Expr) (a b : ℚ) (n j : ℕ)
    (hab : a < b) (hn : 0 < n) (h : e.Valid (gridBox a b n j)) :
    IntervalIntegrable e.real volume (node a b n j:ℝ) (node a b n (j+1):ℝ) := by
  have hd : (0:ℝ) < (step a b n:ℝ) := by exact_mod_cast step_pos hab hn
  have hs : (node a b n (j+1):ℝ)-(node a b n j:ℝ) = (step a b n:ℝ) := by
    exact_mod_cast node_step a b n j
  have hle : (node a b n j:ℝ) ≤ (node a b n (j+1):ℝ) := by linarith
  exact (e.continuousOn _ (gridBox a b n j)
    (fun u hu => gridBox_contains a b n j hu) h).intervalIntegrable_of_Icc hle

theorem cell_mean_contains (e : Expr) (a b : ℚ) (n j : ℕ)
    (hab : a < b) (hn : 0 < n) (h : e.Valid (gridBox a b n j)) :
    (e.eval (gridBox a b n j)).Contains
      ((∫ u in (node a b n j:ℝ)..(node a b n (j+1):ℝ), e.real u) /
        (step a b n:ℝ)) := by
  have hd : (0:ℝ) < (step a b n:ℝ) := by exact_mod_cast step_pos hab hn
  have hs : (node a b n (j+1):ℝ)-(node a b n j:ℝ) = (step a b n:ℝ) := by
    exact_mod_cast node_step a b n j
  have hle : (node a b n j:ℝ) ≤ (node a b n (j+1):ℝ) := by linarith
  have hi := positive_cell_integrable e a b n j hab hn h
  have hp (u : ℝ) (hu : u ∈ Icc (node a b n j:ℝ) (node a b n (j+1):ℝ)) :=
    (contains_iff _ _).1 (e.eval_contains (gridBox_contains a b n j hu) h)
  have hl := intervalIntegral.integral_mono_on hle intervalIntegrable_const hi
    (fun u hu => (hp u hu).1)
  have hh := intervalIntegral.integral_mono_on hle hi intervalIntegrable_const
    (fun u hu => (hp u hu).2)
  rw [intervalIntegral.integral_const,smul_eq_mul,hs] at hl hh
  exact (contains_iff _ _).2
    ⟨(le_div_iff₀ hd).2 (by nlinarith only [hl]),
      (div_le_iff₀ hd).2 (by nlinarith only [hh])⟩

theorem rawSum_contains (e : Expr) (a b : ℚ) (n : ℕ)
    (hab : a < b) (hn : 0 < n) (hv : CellsValid e a b n)
    (j : ℕ) (hj : j ≤ n) :
    IntervalIntegrable e.real volume a (node a b n j:ℝ) ∧
      (rawSum e a b n j).Contains
        ((∫ u in (a:ℝ)..(node a b n j:ℝ),e.real u)/(step a b n:ℝ)) := by
  revert hj
  induction j with
  | zero =>
      intro hj
      simp only [node_zero,rawSum,intervalIntegral.integral_same,zero_div]
      exact ⟨IntervalIntegrable.refl,by
        simpa [I80.raw,I80.Contains,I80.enclosure,I80.decodeLo,I80.decodeHi,
          Enclosure.Contains]⟩
  | succ j ih =>
      intro hj
      have hjn : j < n := by omega
      obtain ⟨hi,hs⟩ := ih (by omega)
      have hval := hv ⟨j,hjn⟩
      have hc := positive_cell_integrable e a b n j hab hn hval
      have hmean := cell_mean_contains e a b n j hab hn hval
      refine ⟨hi.trans hc,?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals hi hc,add_div]
      exact I80.add_contains hs hmean

/-- Actual real integral enclosure from only a finite integer/rational
expression validity check. The output endpoint is computed, not assumed. -/
theorem darboux_contains (e : Expr) (a b : ℚ) (n : ℕ)
    (hab : a < b) (hn : 0 < n) (hv : CellsValid e a b n) :
    (darboux e a b n).Contains (∫ u in (a:ℝ)..(b:ℝ),e.real u) := by
  have hs := (rawSum_contains e a b n hab hn hv n le_rfl).2
  rw [node_top a b hn] at hs
  have hp := I80.mul_contains hs (I80.point_contains (step a b n))
  have hd : (step a b n:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast step_pos hab hn)
  simpa only [darboux,div_mul_cancel₀ _ hd] using hp

end
end ImbalancedChen.P2SeedOriginalQ80Darboux
