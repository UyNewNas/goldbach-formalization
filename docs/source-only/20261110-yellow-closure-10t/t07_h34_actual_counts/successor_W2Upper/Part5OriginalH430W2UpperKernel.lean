import ImbalancedChen.P2EnhancedSeedPairD6Primitive
import ImbalancedChen.P5OriginalActualTableFeedback
import ImbalancedChen.P5OriginalSignedMidpoint
import ImbalancedChen.P2DirectedLogRounding

/-! The logarithmic outer integrand of a single, genuinely clipped W2 vertical strip.
The three components below implement the value, first and second derivatives used in
the original pair_weight Jet2 expression. The log is taken before any nonnegative clamp. -/

namespace ImbalancedChen.Part5OriginalH430W2UpperKernel

open Set MeasureTheory
open scoped Interval
open Certificates Certificates.P2DirectedLogRounding

structure Line where
  c : ℚ
  m : ℚ
  deriving DecidableEq, Repr

def Line.atQ (a : Line) (u : ℚ) : ℚ := a.c + a.m*u
noncomputable def Line.atR (a : Line) (u : ℝ) : ℝ := a.c + a.m*u

structure Strip where
  l : ℚ
  r : ℚ
  low : Line
  high : Line
  deriving DecidableEq, Repr

noncomputable def Strip.density (s : Strip) (u : ℝ) : ℝ :=
  let v0 := s.low.atR u
  let v1 := s.high.atR u
  Real.log (v1*(1-u-v0)/(v0*(1-u-v1))) / (u*(1-u))

theorem original_inner_primitive (s : Strip) {u : ℝ} (hu : 0 < u)
    (h0 : 0 < s.low.atR u) (hlh : s.low.atR u ≤ s.high.atR u)
    (h1 : s.high.atR u < 1-u) :
    (∫ v in Ioo (s.low.atR u) (s.high.atR u), 1/(u*v*(1-u-v))) = s.density u := by
  rw [P2EnhancedSeedPairD6Primitive.pair_inner_log_integral hu h0 hlh h1]
  unfold Strip.density
  ring

/-- Real straight-line operations appearing in the archived pair kernel. -/
inductive Op where
  | const (q : ℚ)
  | input
  | plus (a b : Op)
  | negative (a : Op)
  | times (a b : Op)
  | inverse (a : Op)
  | logarithm (a : Op)
  deriving Repr

namespace Op
noncomputable def val : Op → ℝ → ℝ
  | .const q, _ => q
  | .input, u => u
  | .plus a b, u => val a u + val b u
  | .negative a, u => -val a u
  | .times a b, u => val a u * val b u
  | .inverse a, u => (val a u)⁻¹
  | .logarithm a, u => Real.log (val a u)

def quot (a b : Op) := times a (inverse b)
def minus (a b : Op) := plus a (negative b)
def sq (a : Op) := times a a
def cube (a : Op) := times (sq a) a

structure Jet where
  v : Op
  d : Op
  dd : Op

def jet : Op → Jet
  | .const c => ⟨.const c,.const 0,.const 0⟩
  | .input => ⟨.input,.const 1,.const 0⟩
  | .plus a b =>
    let A := jet a
    let B := jet b
    ⟨.plus A.v B.v,.plus A.d B.d,.plus A.dd B.dd⟩
  | .negative a =>
    let A := jet a
    ⟨.negative A.v,.negative A.d,.negative A.dd⟩
  | .times a b =>
    let A := jet a
    let B := jet b
    ⟨.times A.v B.v,.plus (.times A.d B.v) (.times A.v B.d),
      .plus (.plus (.times A.dd B.v) (.times (.times (.const 2) A.d) B.d)) (.times A.v B.dd)⟩
  | .inverse a =>
    let A := jet a
    ⟨.inverse A.v,quot (.negative A.d) (sq A.v),
      minus (quot (.times (.const 2) (sq A.d)) (cube A.v)) (quot A.dd (sq A.v))⟩
  | .logarithm a =>
    let A := jet a
    ⟨.logarithm A.v,quot A.d A.v,minus (quot A.dd A.v) (sq (quot A.d A.v))⟩

@[simp] theorem jet_value (e : Op) : e.jet.v = e := by
  induction e <;> simp_all [jet]

def Regular : Op → ℝ → Prop
  | .const _, _ | .input, _ => True
  | .plus a b, x | .times a b, x => Regular a x ∧ Regular b x
  | .negative a, x => Regular a x
  | .inverse a, x | .logarithm a, x => Regular a x ∧ 0 < a.val x

/-- The derivative fields are of the actual expression at its own point. -/
theorem actual_jet (e : Op) (x : ℝ) (hx : e.Regular x) :
    HasDerivAt e.val (e.jet.d.val x) x ∧
    HasDerivAt e.jet.d.val (e.jet.dd.val x) x ∧ ContinuousAt e.jet.dd.val x := by
  induction e with
  | const c =>
    simpa [jet,val] using
      And.intro (hasDerivAt_const x (c : ℝ))
        (And.intro (hasDerivAt_const x (0 : ℝ)) (continuousAt_const (c := (0 : ℝ))))
  | input =>
    simpa [jet,val] using
      And.intro (hasDerivAt_id x)
        (And.intro (hasDerivAt_const x (1 : ℝ)) (continuousAt_const (c := (0 : ℝ))))
  | plus a b ia ib =>
    obtain ⟨ha,ha',ha''⟩ := ia hx.1
    obtain ⟨hb,hb',hb''⟩ := ib hx.2
    simpa only [jet,jet_value,val] using And.intro (ha.add hb)
      (And.intro (ha'.add hb') (ha''.add hb''))
  | negative a ih =>
    obtain ⟨ha,ha',ha''⟩ := ih hx
    simpa only [jet,jet_value,val] using And.intro ha.neg (And.intro ha'.neg ha''.neg)
  | times a b ia ib =>
    obtain ⟨ha,ha',ha''⟩ := ia hx.1
    obtain ⟨hb,hb',hb''⟩ := ib hx.2
    simp only [jet,jet_value,val,Rat.cast_ofNat]
    refine ⟨ha.mul hb,?_,?_⟩
    · apply ((ha'.mul hb).add (ha.mul hb')).congr_deriv
      ring
    · exact (((ha''.mul hb.continuousAt).add
        ((continuousAt_const.mul ha'.continuousAt).mul hb'.continuousAt)).add
          (ha.continuousAt.mul hb''))
  | inverse a ih =>
    obtain ⟨ha,ha',ha''⟩ := ih hx.1
    have h := hx.2.ne'
    simp only [jet,jet_value,val,quot,sq,cube,minus,Rat.cast_ofNat]
    refine ⟨?_,?_,?_⟩
    · apply (ha.inv h).congr_deriv
      field_simp [h] <;> ring
    · apply (ha'.neg.mul ((ha.mul ha).inv (mul_ne_zero h h))).congr_deriv
      field_simp [h] <;> ring
    · exact ((continuousAt_const.mul (ha'.continuousAt.mul ha'.continuousAt)).mul
        (((ha.continuousAt.mul ha.continuousAt).mul ha.continuousAt).inv₀
          (mul_ne_zero (mul_ne_zero h h) h))).add
          ((ha''.mul ((ha.continuousAt.mul ha.continuousAt).inv₀ (mul_ne_zero h h))).neg)
  | logarithm a ih =>
    obtain ⟨ha,ha',ha''⟩ := ih hx.1
    have h := hx.2.ne'
    simp only [jet,jet_value,val,quot,sq,minus]
    refine ⟨?_,?_,?_⟩
    · apply (ha.log h).congr_deriv
      ring
    · apply (ha'.mul (ha.inv h)).congr_deriv
      field_simp [h] <;> ring
    · have hi := ha.continuousAt.inv₀ h
      exact (ha''.mul hi).add (((ha'.continuousAt.mul hi).mul (ha'.continuousAt.mul hi)).neg)

def affine (a : Line) := plus (.const a.c) (times (.const a.m) .input)

def kernel (s : Strip) : Op :=
  let u := input
  let a := affine s.low
  let b := affine s.high
  let z := minus (.const 1) u
  quot (logarithm (quot (times b (minus z a)) (times a (minus z b)))) (times u z)

theorem kernel_value (s : Strip) : (kernel s).val = s.density := by
  funext u
  simp only [kernel,affine,quot,minus,val,Strip.density,Line.atR,Rat.cast_one,
    div_eq_mul_inv,sub_eq_add_neg]

theorem kernel_regular (s : Strip) {u : ℝ} (hu : 0<u) (ha : 0<s.low.atR u)
    (hab : s.low.atR u ≤ s.high.atR u) (hb : s.high.atR u<1-u) :
    (kernel s).Regular u := by
  have hbp := ha.trans_le hab
  have hz : 0<1-u := hbp.trans hb
  have hs0 : 0 < 1-u-s.low.atR u := by linarith
  have hs1 : 0 < 1-u-s.high.atR u := by linarith
  have hden := mul_pos ha hs1
  have hrat := mul_pos (mul_pos hbp hs0) (inv_pos.mpr hden)
  have huz := mul_pos hu hz
  simpa [kernel,affine,quot,minus,Regular,val,Line.atR,sub_eq_add_neg] using
    (And.intro (And.intro hden hrat) huz)

end Op
end ImbalancedChen.Part5OriginalH430W2UpperKernel
