import ImbalancedChen.Part5OriginalH430W2UpperKernel

namespace ImbalancedChen.Part5OriginalH430W2UpperQuadrature

open Set MeasureTheory
open scoped Interval
open Certificates Certificates.P2DirectedLogRounding
open Part5OriginalH430W2UpperKernel

/-- Directed dyadic state for the odd power and the sum accumulated before it.
Only the proof refers to the exact power-series rationals. -/
private def oddState (t : ℚ) : ℕ → Enclosure × Enclosure
  | 0 => (Enclosure.point t,Enclosure.point 0)
  | n+1 =>
    let B := oddState t n
    let d : ℚ := ((2*n+1 : ℕ) : ℚ)
    (⟨roundDown 112 (B.1.lower*t^2),roundUp 112 (B.1.upper*t^2)⟩,
     ⟨roundDown 112 (B.2.lower+B.1.lower/d),roundUp 112 (B.2.upper+B.1.upper/d)⟩)

private def oddSum (t : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, t^(2*i+1)/((2*i+1 : ℕ) : ℚ)

private theorem oddState_sound (t : ℚ) (n : ℕ) :
    (oddState t n).1.lower ≤ t^(2*n+1) ∧ t^(2*n+1) ≤ (oddState t n).1.upper ∧
    (oddState t n).2.lower ≤ oddSum t n ∧ oddSum t n ≤ (oddState t n).2.upper := by
  induction n with
  | zero => simp [oddState,oddSum,Enclosure.point]
  | succ n ih =>
    obtain ⟨pl,pu,sl,su⟩ := ih
    have hp : t^(2*(n+1)+1) = t^(2*n+1)*t^2 := by
      rw [← pow_add]
      congr 1 <;> omega
    have hs : oddSum t (n+1) = oddSum t n + t^(2*n+1)/((2*n+1 : ℕ) : ℚ) := by
      unfold oddSum
      rw [Finset.sum_range_succ]
    have hd : (0 : ℚ) ≤ ((2*n+1 : ℕ) : ℚ) := by positivity
    dsimp only [oddState]
    rw [hp,hs]
    exact ⟨(roundDown_le _ _).trans (mul_le_mul_of_nonneg_right pl (sq_nonneg _)),
      (mul_le_mul_of_nonneg_right pu (sq_nonneg _)).trans (le_roundUp _ _),
      (roundDown_le _ _).trans (add_le_add sl (div_le_div_of_nonneg_right pl hd)),
      (add_le_add su (div_le_div_of_nonneg_right pu hd)).trans (le_roundUp _ _)⟩

/-- Rational enclosure with the original unsharpened analytic remainder. -/
def logAbove (q : ℚ) : Enclosure :=
  let t := logParameter q
  let B := oddState t 32
  ⟨2*B.2.lower,2*B.2.upper+2*B.1.upper/(1-t^2)⟩

private theorem logAbove_sound {q : ℚ} (hq : 1 ≤ q) :
    (logAbove q).Contains (Real.log (q : ℝ)) := by
  let t := logParameter q
  obtain ⟨_,pu,sl,su⟩ := oddState_sound t 32
  have pos : (0 : ℚ)<q+1 := by linarith
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hq) pos.le
  have ht' : t<1 := (div_lt_one pos).mpr (by linarith)
  have hd : 0 ≤ 1-t^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht'.le) (show 0≤1+t by linarith)]
  let c : RationalLogCertificate := ⟨q,32,(logAbove q).lower,(logAbove q).upper⟩
  have hv : c.Valid := by
    refine ⟨hq,?_,?_⟩
    · exact mul_le_mul_of_nonneg_left sl (by norm_num)
    · exact add_le_add (mul_le_mul_of_nonneg_left su (by norm_num))
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left pu (by norm_num)) hd)
  exact c.check_sound (decide_eq_true hv)

def logPoint (q : ℚ) : Enclosure :=
  (if 1 ≤ q then logAbove q else (logAbove q⁻¹).neg).round 112

theorem logPoint_sound {q : ℚ} (hq : 0 < q) : (logPoint q).Contains (Real.log (q : ℝ)) := by
  unfold logPoint
  apply Enclosure.round_contains
  by_cases h : 1 ≤ q
  · simpa only [if_pos h] using logAbove_sound h
  · have hi : 1 ≤ q⁻¹ := by
      rw [← one_div]
      exact (le_div_iff₀ hq).2 (by linarith)
    have H := Enclosure.neg_contains (logAbove_sound hi)
    simpa only [if_neg h,Rat.cast_inv,Real.log_inv,neg_neg] using H

namespace Box

def inverse (A : Enclosure) : Enclosure := ⟨A.upper⁻¹,A.lower⁻¹⟩

theorem inverse_sound {A : Enclosure} {x : ℝ} (hA : 0<A.lower) (hx : A.Contains x) :
    (inverse A).Contains x⁻¹ := by
  have hp : (0 : ℝ) < A.lower := by exact_mod_cast hA
  have hxp := hp.trans_le hx.1
  change ((A.upper⁻¹ : ℚ) : ℝ) ≤ _ ∧ _ ≤ ((A.lower⁻¹ : ℚ) : ℝ)
  push_cast
  have h1 := one_div_le_one_div_of_le hxp hx.2
  have h2 := one_div_le_one_div_of_le hp hx.1
  simpa only [one_div] using And.intro h1 h2

def logarithm (A : Enclosure) : Enclosure :=
  ⟨(logPoint A.lower).lower,(logPoint A.upper).upper⟩

theorem log_sound {A : Enclosure} {x : ℝ} (hA : 0<A.lower) (hx : A.Contains x) :
    (logarithm A).Contains (Real.log x) := by
  have hl : (0 : ℝ)<A.lower := by exact_mod_cast hA
  have hr : (0 : ℝ)<A.upper := (hl.trans_le hx.1).trans_le hx.2
  have hrq : 0<A.upper := by exact_mod_cast hr
  exact ⟨(logPoint_sound hA).1.trans (Real.log_le_log hl hx.1),
    (Real.log_le_log (hl.trans_le hx.1) hx.2).trans (logPoint_sound hrq).2⟩

/-- Directed interval evaluation of the author's actual expression. Arithmetic within
one panel is rational; high-precision dyadic rounding prevents denominator growth. -/
def eval (I : Enclosure) : Op → Enclosure
  | .const q => .point q
  | .input => I
  | .plus a b => (eval I a).add (eval I b)
  | .negative a => (eval I a).neg
  | .times a b => ((eval I a).mul (eval I b)).round 112
  | .inverse a => (inverse (eval I a)).round 112
  | .logarithm a => logarithm (eval I a)

def ok (I : Enclosure) : Op → Bool
  | .const _ | .input => true
  | .plus a b | .times a b => ok I a && ok I b
  | .negative a => ok I a
  | .inverse a | .logarithm a => ok I a && decide (0 < (eval I a).lower)

theorem sound (e : Op) (I : Enclosure) {x : ℝ} (hx : I.Contains x) (h : ok I e = true) :
    (eval I e).Contains (e.val x) := by
  induction e with
  | const q => exact Enclosure.point_contains q
  | input => exact hx
  | plus a b ha hb =>
    obtain ⟨h1,h2⟩ := Bool.and_eq_true.mp h
    exact Enclosure.add_contains (ha h1) (hb h2)
  | negative a ha => exact Enclosure.neg_contains (ha h)
  | times a b ha hb =>
    obtain ⟨h1,h2⟩ := Bool.and_eq_true.mp h
    exact Enclosure.round_contains (Enclosure.mul_contains (ha h1) (hb h2)) 112
  | inverse a ha =>
    obtain ⟨h1,h2⟩ := Bool.and_eq_true.mp h
    exact Enclosure.round_contains (inverse_sound (of_decide_eq_true h2) (ha h1)) 112
  | logarithm a ha =>
    obtain ⟨h1,h2⟩ := Bool.and_eq_true.mp h
    exact log_sound (of_decide_eq_true h2) (ha h1)

end Box

structure Safe (s : Strip) (x : ℝ) : Prop where
  u : 0<x
  low : 0<s.low.atR x
  order : s.low.atR x≤s.high.atR x
  upper : s.high.atR x<1-x

theorem Safe.regular {s : Strip} {x : ℝ} (h : Safe s x) : (Op.kernel s).Regular x :=
  Op.kernel_regular s h.u h.low h.order h.upper

theorem Safe.nonneg {s : Strip} {x : ℝ} (h : Safe s x) : 0≤s.density x := by
  rw [← original_inner_primitive s h.u h.low h.order h.upper]
  apply setIntegral_nonneg_of_ae_restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  exact (one_div_pos.mpr (mul_pos (mul_pos h.u (h.low.trans hv.1))
    (by linarith [h.upper,hv.2] : 0<1-x-v))).le

theorem density_cont {s : Strip} {l r : ℝ} (h : ∀ x∈Icc l r, Safe s x) :
    ContinuousOn s.density (Icc l r) := by
  rw [← Op.kernel_value s]
  exact fun x hx => ((Op.actual_jet _ x (h x hx).regular).1.continuousAt).continuousWithinAt

def panelLower (mid : Bool) (s : Strip) (l r : ℚ) : ℚ :=
  let e := Op.kernel s
  let I : Enclosure := ⟨l,r⟩
  let M := Enclosure.point ((l+r)/2)
  if mid then
    if Box.ok M e && Box.ok I e.jet.dd then
      roundDown 112 ((r-l)*((Box.eval M e).lower + (Box.eval I e.jet.dd).lower*(r-l)^2/24))
    else 0
  else if Box.ok I e then roundDown 112 ((r-l)*max 0 (Box.eval I e).lower) else 0

theorem panel_sound (mid : Bool) (s : Strip) {l r : ℚ} (hlr : l ≤ r)
    (h : ∀ x∈Icc (l : ℝ) (r : ℝ), Safe s x) :
    (panelLower mid s l r : ℝ) ≤ ∫ x in (l : ℝ)..(r : ℝ), s.density x := by
  let e := Op.kernel s
  let I : Enclosure := ⟨l,r⟩
  let m := (l+r)/2
  let M := Enclosure.point m
  have hr : (l : ℝ)≤r := by exact_mod_cast hlr
  have hz : (0 : ℝ)≤∫ x in (l : ℝ)..(r : ℝ),s.density x :=
    intervalIntegral.integral_nonneg hr (fun x hx => (h x (by exact hx)).nonneg)
  cases mid with
  | false =>
    by_cases hg : Box.ok I e = true
    · have hp (x : ℝ) (hx : x∈Icc (l : ℝ) (r : ℝ)) :
          max 0 ((Box.eval I e).lower : ℝ) ≤ s.density x := by
        apply max_le (h x hx).nonneg
        simpa only [e,Op.kernel_value] using (Box.sound e I hx hg).1
      have H := intervalIntegral.integral_mono_on (μ := volume) hr
        (f := fun _ : ℝ => max 0 ((Box.eval I e).lower : ℝ)) (g := s.density)
        (by exact continuous_const.intervalIntegrable _ _) ((density_cont h).intervalIntegrable_of_Icc hr) hp
      rw [intervalIntegral.integral_const] at H
      simp only [smul_eq_mul] at H
      have hd := roundDown_le 112 ((r-l)*max 0 (Box.eval I e).lower)
      have hcast : ((roundDown 112 ((r-l)*max 0 (Box.eval I e).lower) : ℚ) : ℝ)
          ≤ ((r : ℝ)-l)*max 0 ((Box.eval I e).lower : ℝ) := by exact_mod_cast hd
      change ((if Box.ok I e then roundDown 112 ((r-l)*max 0 (Box.eval I e).lower) else 0 : ℚ) : ℝ) ≤ _
      rw [if_pos hg]
      exact hcast.trans H
    · change ((if Box.ok I e then roundDown 112 ((r-l)*max 0 (Box.eval I e).lower) else 0 : ℚ) : ℝ) ≤ _
      simpa only [if_neg hg,Rat.cast_zero] using hz
  | true =>
    by_cases hg : (Box.ok M e && Box.ok I e.jet.dd) = true
    · obtain ⟨hv,hd⟩ := Bool.and_eq_true.mp hg
      have hder := fun x hx => Op.actual_jet e x (h x hx).regular
      have hB (x : ℝ) (hx : x∈Icc (l : ℝ) (r : ℝ)) := Box.sound e.jet.dd I hx hd
      have H := (P5OriginalSignedMidpoint.midpoint_bounds hr
        (fun x hx => (hder x hx).1) (fun x hx => (hder x hx).2.1)
        (fun x hx => (hder x hx).2.2.continuousWithinAt) hB).1
      have hmid : (M.Contains (((l : ℝ)+r)/2)) := by
        simpa only [M,m,Rat.cast_div,Rat.cast_add,Rat.cast_ofNat] using Enclosure.point_contains m
      have hp := (Box.sound e M hmid hv).1
      have hlow : ((r : ℝ)-l)*((Box.eval M e).lower + (Box.eval I e.jet.dd).lower*((r : ℝ)-l)^2/24)
          ≤ ∫ x in (l : ℝ)..(r : ℝ), s.density x := by
        rw [← Op.kernel_value s]
        exact (mul_le_mul_of_nonneg_left (add_le_add_right hp _) (sub_nonneg.mpr hr)).trans H
      have hrnd := roundDown_le 112 ((r-l)*((Box.eval M e).lower+(Box.eval I e.jet.dd).lower*(r-l)^2/24))
      have hc : ((roundDown 112 ((r-l)*((Box.eval M e).lower+(Box.eval I e.jet.dd).lower*(r-l)^2/24)) : ℚ) : ℝ) ≤
          ((r : ℝ)-l)*((Box.eval M e).lower+(Box.eval I e.jet.dd).lower*((r : ℝ)-l)^2/24) := by exact_mod_cast hrnd
      change ((if Box.ok M e && Box.ok I e.jet.dd then
        roundDown 112 ((r-l)*((Box.eval M e).lower+(Box.eval I e.jet.dd).lower*(r-l)^2/24)) else 0 : ℚ) : ℝ) ≤ _
      rw [if_pos hg]
      exact hc.trans hlow
    · change ((if Box.ok M e && Box.ok I e.jet.dd then
        roundDown 112 ((r-l)*((Box.eval M e).lower+(Box.eval I e.jet.dd).lower*(r-l)^2/24)) else 0 : ℚ) : ℝ) ≤ _
      simpa only [if_neg hg,Rat.cast_zero] using hz

def node (s : Strip) (n i : ℕ) : ℚ := s.l+(i : ℚ)*((s.r-s.l)/n)

def panels (mid : Bool) : ℕ := if mid then 64 else 1024

def stripLower (mid : Bool) (s : Strip) : ℚ :=
  max 0 (∑ i ∈ Finset.range (panels mid), panelLower mid s
    (node s (panels mid) i) (node s (panels mid) (i+1)))

theorem strip_sound (mid : Bool) (s : Strip) (hlr : s.l ≤ s.r)
    (hs : ∀ x∈Icc (s.l : ℝ) (s.r : ℝ), Safe s x) :
    (stripLower mid s : ℝ) ≤ ∫ x in (s.l : ℝ)..(s.r : ℝ), s.density x := by
  let n := panels mid
  have hn : 0<n := by
    change 0 < panels mid
    cases mid <;> decide
  have hnq : (0 : ℚ)<n := by exact_mod_cast hn
  have hstep : (0 : ℚ)≤(s.r-s.l)/n := div_nonneg (sub_nonneg.mpr hlr) hnq.le
  have hmono : Monotone (node s n) := by
    intro a b hab
    exact add_le_add_left (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hstep) s.l
  have hzero : node s n 0 = s.l := by simp [node]
  have hend : node s n n = s.r := by unfold node; field_simp [hnq.ne'] <;> ring
  have sub (i : ℕ) (hi : i≤n) :
      Icc (s.l : ℝ) (node s n i : ℝ) ⊆ Icc (s.l : ℝ) (s.r : ℝ) := by
    have H := hmono hi
    rw [hend] at H
    exact fun _ h => ⟨h.1,h.2.trans (by exact_mod_cast H)⟩
  have H (i : ℕ) (hi : i≤n) :
      (∑ t ∈ Finset.range i, (panelLower mid s (node s n t) (node s n (t+1)) : ℝ)) ≤
        ∫ x in (s.l : ℝ)..(node s n i : ℝ), s.density x := by
    induction i with
    | zero => simp [hzero]
    | succ i ih =>
      have hin : i≤n := by omega
      have hi0 := hmono (Nat.zero_le i)
      rw [hzero] at hi0
      have hi0r : (s.l : ℝ)≤node s n i := by exact_mod_cast hi0
      have h01 := hmono (Nat.le_succ i)
      have h01r : (node s n i : ℝ)≤node s n (i+1) := by exact_mod_cast h01
      have hc := density_cont hs
      have hs' : Icc (node s n i : ℝ) (node s n (i+1) : ℝ) ⊆ Icc (s.l : ℝ) (s.r : ℝ) :=
        fun x hx => sub _ hi ⟨hi0r.trans hx.1,hx.2⟩
      rw [Finset.sum_range_succ,← intervalIntegral.integral_add_adjacent_intervals
        ((hc.mono (sub _ hin)).intervalIntegrable_of_Icc hi0r)
        ((hc.mono hs').intervalIntegrable_of_Icc h01r)]
      exact add_le_add (ih hin) (panel_sound mid s h01 (fun x hx => hs x (hs' hx)))
  have hlim := H n le_rfl
  rw [hend] at hlim
  have hr : (s.l : ℝ)≤s.r := by exact_mod_cast hlr
  have hnon := intervalIntegral.integral_nonneg hr (fun x hx => (hs x hx).nonneg)
  simpa [stripLower,n] using max_le hnon hlim

end ImbalancedChen.Part5OriginalH430W2UpperQuadrature
