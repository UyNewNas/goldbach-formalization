import ImbalancedChen.P2DirectedLogRounding

/-!
SOURCE ONLY. UNCOMPILED. All finite proof terms in clients are UNEVALUATED.
A Q80 signed interval backend with exact 64-term odd-series logarithms.
This proves enclosure semantics; it does not assert equality with the
historical bit_length/log32 integer algorithm. No stored real value is used.
-/
namespace ImbalancedChen.P5U7Q80Backend

open Certificates Certificates.P2DirectedLogRounding
open scoped BigOperators

def qpoint (q : ℚ) : Enclosure := (Enclosure.point q).round 80
def qrange (l r : ℚ) : Enclosure := (⟨l, r⟩ : Enclosure).round 80
def qmul (a b : Enclosure) : Enclosure := (a.mul b).round 80
def invBox (a : Enclosure) : Enclosure := ⟨1 / a.upper, 1 / a.lower⟩
def qdiv (a b : Enclosure) : Enclosure := (a.mul (invBox b)).round 80

def qpow (a : Enclosure) : ℕ → Enclosure
  | 0 => qpoint 1
  | n + 1 => qmul (qpow a n) a

theorem qpoint_contains (q : ℚ) : (qpoint q).Contains (q : ℝ) :=
  Enclosure.round_contains (Enclosure.point_contains q) 80

theorem qrange_contains {l r : ℚ} {x : ℝ}
    (hx : (l : ℝ) ≤ x ∧ x ≤ (r : ℝ)) : (qrange l r).Contains x :=
  Enclosure.round_contains hx 80

theorem qmul_contains {a b : Enclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (qmul a b).Contains (x * y) :=
  Enclosure.round_contains (Enclosure.mul_contains hx hy) 80

theorem qdiv_contains {a b : Enclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) (hb : 0 < b.lower) :
    (qdiv a b).Contains (x / y) := by
  have hbR : (0 : ℝ) < (b.lower : ℝ) := by exact_mod_cast hb
  have hy0 : 0 < y := hbR.trans_le hy.1
  have hi : (invBox b).Contains (1 / y) := by
    constructor
    · simpa [invBox, Enclosure.Contains] using one_div_le_one_div_of_le hy0 hy.2
    · simpa [invBox, Enclosure.Contains] using one_div_le_one_div_of_le hbR hy.1
  simpa [qdiv, div_eq_mul_inv, one_div] using
    Enclosure.round_contains (Enclosure.mul_contains hx hi) 80

theorem qpow_contains {a : Enclosure} {x : ℝ} (hx : a.Contains x) (n : ℕ) :
    (qpow a n).Contains (x ^ n) := by
  induction n with
  | zero => simpa [qpow] using qpoint_contains 1
  | succ n ih => simpa [qpow, pow_succ] using qmul_contains ih hx

/-- Explicit finite rational endpoints, with the Mathlib remainder. -/
def positiveLogBox (q : ℚ) : Enclosure :=
  ⟨logSeriesLower q 64, logSeriesUpper q 64⟩

theorem positiveLogBox_contains {q : ℚ} (hq : 1 ≤ q) :
    (positiveLogBox q).Contains (Real.log (q : ℝ)) := by
  let c : RationalLogCertificate :=
    ⟨q, 64, logSeriesLower q 64, logSeriesUpper q 64⟩
  have hc : c.check = true := by
    simp [RationalLogCertificate.check, RationalLogCertificate.Valid, c, hq]
  exact c.check_sound hc

/-- Reciprocal reduction handles positive arguments below one, including
outward-rounded intervals at the prime right wall and correction left wall. -/
def pointLogBox (q : ℚ) : Enclosure :=
  (if 1 ≤ q then positiveLogBox q else (positiveLogBox (1 / q)).neg).round 80

theorem pointLogBox_contains {q : ℚ} (hq : 0 < q) :
    (pointLogBox q).Contains (Real.log (q : ℝ)) := by
  apply Enclosure.round_contains (bits := 80)
  by_cases hq1 : 1 ≤ q
  · simpa [pointLogBox, hq1] using positiveLogBox_contains hq1
  · have hqi : 1 ≤ 1 / q := (le_div_iff₀ hq).mpr (by linarith)
    have h := Enclosure.neg_contains (positiveLogBox_contains hqi)
    simpa [pointLogBox, hq1, Rat.cast_div, Real.log_inv, one_div] using h

def qlog (a : Enclosure) : Enclosure :=
  ⟨(pointLogBox a.lower).lower, (pointLogBox a.upper).upper⟩

theorem qlog_contains {a : Enclosure} {x : ℝ} (hx : a.Contains x)
    (ha : 0 < a.lower) : (qlog a).Contains (Real.log x) := by
  have haR : (0 : ℝ) < (a.lower : ℝ) := by exact_mod_cast ha
  have hx0 : 0 < x := haR.trans_le hx.1
  have hu : 0 < a.upper := by
    have huR : (0 : ℝ) < (a.upper : ℝ) := hx0.trans_le hx.2
    exact_mod_cast huR
  exact ⟨(pointLogBox_contains ha).1.trans (Real.log_le_log haR hx.1),
    (Real.log_le_log hx0 hx.2).trans (pointLogBox_contains hu).2⟩

/-- Syntax is the literal rational/log operation graph. Validity checks
only positive denominator/log arguments, never a target containment. -/
inductive Expr where
  | variable : Expr
  | rational : ℚ → Expr
  | add : Expr → Expr → Expr
  | neg : Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  | pow : Expr → ℕ → Expr
  | log : Expr → Expr
  deriving Repr

def Expr.box (X : Enclosure) : Expr → Enclosure
  | .variable => X
  | .rational q => qpoint q
  | .add a b => (a.box X).add (b.box X)
  | .neg a => (a.box X).neg
  | .mul a b => qmul (a.box X) (b.box X)
  | .div a b => qdiv (a.box X) (b.box X)
  | .pow a n => qpow (a.box X) n
  | .log a => qlog (a.box X)

noncomputable def Expr.eval (x : ℝ) : Expr → ℝ
  | .variable => x
  | .rational q => q
  | .add a b => a.eval x + b.eval x
  | .neg a => -a.eval x
  | .mul a b => a.eval x * b.eval x
  | .div a b => a.eval x / b.eval x
  | .pow a n => a.eval x ^ n
  | .log a => Real.log (a.eval x)

def Expr.Valid (X : Enclosure) : Expr → Prop
  | .variable => True
  | .rational _ => True
  | .add a b => a.Valid X ∧ b.Valid X
  | .neg a => a.Valid X
  | .mul a b => a.Valid X ∧ b.Valid X
  | .div a b => a.Valid X ∧ b.Valid X ∧ 0 < (b.box X).lower
  | .pow a _ => a.Valid X
  | .log a => a.Valid X ∧ 0 < (a.box X).lower

instance (X : Enclosure) (e : Expr) : Decidable (e.Valid X) := by
  induction e with
  | variable => exact isTrue trivial
  | rational q => exact isTrue trivial
  | add a b ha hb =>
    letI := ha
    letI := hb
    dsimp [Expr.Valid]
    infer_instance
  | neg a ha => exact ha
  | mul a b ha hb =>
    letI := ha
    letI := hb
    dsimp [Expr.Valid]
    infer_instance
  | div a b ha hb =>
    letI := ha
    letI := hb
    dsimp [Expr.Valid]
    infer_instance
  | pow a n ha => exact ha
  | log a ha =>
    letI := ha
    dsimp [Expr.Valid]
    infer_instance

theorem Expr.box_sound {X : Enclosure} {x : ℝ} (hx : X.Contains x)
    (e : Expr) (he : e.Valid X) : (e.box X).Contains (e.eval x) := by
  revert he
  induction e with
  | variable => intro _; exact hx
  | rational q => intro _; exact qpoint_contains q
  | add a b ha hb => intro he; exact Enclosure.add_contains (ha he.1) (hb he.2)
  | neg a ha => intro he; exact Enclosure.neg_contains (ha he)
  | mul a b ha hb => intro he; exact qmul_contains (ha he.1) (hb he.2)
  | div a b ha hb => intro he; exact qdiv_contains (ha he.1) (hb he.2.1) he.2.2
  | pow a n ha => intro he; exact qpow_contains (ha he) n
  | log a ha => intro he; exact qlog_contains (ha he.1) he.2

end ImbalancedChen.P5U7Q80Backend


