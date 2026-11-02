import ImbalancedChen.P5U7OriginalScalarCorrection

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The two actual scalar integrands and their literal `main_second(t,7)` and
`correction_second(u)` derivatives in certify_sharp_switch_midpoint.py.
The derivatives are proved on open neighborhoods of the CLOSED original
intervals, so none of the archived 1024 cell endpoints needs a seam exception.
No interval enclosure, derivative estimate, or saved endpoint is assumed.
-/

namespace ImbalancedChen.P5U7OriginalMidpoint

noncomputable section
open Set MeasureTheory
open P5U7OriginalScalarCorrection

def primeLog (t : ℝ) : ℝ := Real.log ((1 - 2 * t) / t)
def primeLogFirst (t : ℝ) : ℝ := -2 / (1 - 2 * t) - 1 / t
def primeLogSecond (t : ℝ) : ℝ := -4 / (1 - 2 * t) ^ 2 + 1 / t ^ 2
def reciprocal (t : ℝ) : ℝ := 1 / t + 1 / (1 - t)
def reciprocalFirst (t : ℝ) : ℝ := -1 / t ^ 2 + 1 / (1 - t) ^ 2
def reciprocalSecond (t : ℝ) : ℝ := 2 / t ^ 3 + 2 / (1 - t) ^ 3

def primeValue (t : ℝ) : ℝ := primeLog t * reciprocal t
def primeFirst (t : ℝ) : ℝ :=
  primeLogFirst t * reciprocal t + primeLog t * reciprocalFirst t
def primeSecond (t : ℝ) : ℝ :=
  primeLogSecond t * reciprocal t +
    2 * primeLogFirst t * reciprocalFirst t + primeLog t * reciprocalSecond t

theorem primeValue_eq {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    primeValue t = Real.log ((1 - 2 * t) / t) / (t * (1 - t)) := by
  unfold primeValue primeLog reciprocal
  field_simp [ht.ne', (sub_pos.mpr ht1).ne']
  <;> ring

theorem primeLog_hasDerivAt {t : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) :
    HasDerivAt primeLog (primeLogFirst t) t := by
  have hn : 0 < 1 - 2 * t := by linarith
  have hd := (((hasDerivAt_id t).const_mul 2).const_sub 1).div
    (hasDerivAt_id t) ht.ne'
  apply (hd.log (div_pos hn ht).ne').congr_deriv
  unfold primeLogFirst
  field_simp [ht.ne', hn.ne']
  <;> ring

theorem primeLogFirst_hasDerivAt {t : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) :
    HasDerivAt primeLogFirst (primeLogSecond t) t := by
  have hn : 1 - 2 * t ≠ 0 := ne_of_gt (by linarith)
  have hleft := (hasDerivAt_const t (-2 : ℝ)).div
    (((hasDerivAt_id t).const_mul 2).const_sub 1) hn
  have hright := (hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht.ne'
  apply (hleft.sub hright).congr_deriv
  unfold primeLogSecond
  field_simp [ht.ne', hn]
  <;> ring

theorem reciprocal_hasDerivAt {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt reciprocal (reciprocalFirst t) t := by
  have hm : 1 - t ≠ 0 := (sub_pos.mpr ht1).ne'
  have hleft := (hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht.ne'
  have hright := (hasDerivAt_const t (1 : ℝ)).div
    ((hasDerivAt_id t).const_sub 1) hm
  apply (hleft.add hright).congr_deriv
  unfold reciprocalFirst
  ring

theorem reciprocalFirst_hasDerivAt {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt reciprocalFirst (reciprocalSecond t) t := by
  have hm : 1 - t ≠ 0 := (sub_pos.mpr ht1).ne'
  have hleft := (hasDerivAt_const t (-1 : ℝ)).div
    ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht.ne')
  have hright := (hasDerivAt_const t (1 : ℝ)).div
    (((hasDerivAt_id t).const_sub 1).pow 2) (pow_ne_zero 2 hm)
  apply (hleft.add hright).congr_deriv
  unfold reciprocalSecond
  field_simp [ht.ne', hm]
  <;> ring

theorem primeValue_hasDerivAt {t : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) :
    HasDerivAt primeValue (primeFirst t) t := by
  exact (primeLog_hasDerivAt ht ht2).mul
    (reciprocal_hasDerivAt ht (by linarith))

theorem primeFirst_hasDerivAt {t : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) :
    HasDerivAt primeFirst (primeSecond t) t := by
  have hL := primeLog_hasDerivAt ht ht2
  have hL' := primeLogFirst_hasDerivAt ht ht2
  have hR := reciprocal_hasDerivAt ht (by linarith : t < 1)
  have hR' := reciprocalFirst_hasDerivAt ht (by linarith : t < 1)
  apply ((hL'.mul hR).add (hL.mul hR')).congr_deriv
  unfold primeSecond
  ring

def correctionA (u : ℝ) : ℝ := Real.log (u - 1) / u
def correctionAFirst (u : ℝ) : ℝ :=
  1 / (u * (u - 1)) - Real.log (u - 1) / u ^ 2
def correctionASecond (u : ℝ) : ℝ :=
  -(2 * u - 1) / (u ^ 2 * (u - 1) ^ 2) -
    1 / ((u - 1) * u ^ 2) + 2 * Real.log (u - 1) / u ^ 3
def correctionB (u : ℝ) : ℝ := Real.log ((191 / 59 : ℝ) / (u + 1))
def correctionBFirst (u : ℝ) : ℝ := -1 / (u + 1)
def correctionBSecond (u : ℝ) : ℝ := 1 / (u + 1) ^ 2

def correctionFirst (u : ℝ) : ℝ :=
  correctionAFirst u * correctionB u + correctionA u * correctionBFirst u
def correctionSecond (u : ℝ) : ℝ :=
  correctionASecond u * correctionB u +
    2 * correctionAFirst u * correctionBFirst u + correctionA u * correctionBSecond u

theorem correctionA_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt correctionA (correctionAFirst u) u := by
  have hu0 : u ≠ 0 := ne_of_gt (by linarith)
  have hm : u - 1 ≠ 0 := (sub_pos.mpr hu).ne'
  have hl := ((hasDerivAt_id u).sub_const 1).log hm
  apply (hl.div (hasDerivAt_id u) hu0).congr_deriv
  unfold correctionAFirst
  field_simp [hu0, hm]
  <;> ring

theorem correctionAFirst_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt correctionAFirst (correctionASecond u) u := by
  have hu0 : u ≠ 0 := ne_of_gt (by linarith)
  have hm : u - 1 ≠ 0 := (sub_pos.mpr hu).ne'
  have hl := ((hasDerivAt_id u).sub_const 1).log hm
  have hp := (hasDerivAt_id u).mul ((hasDerivAt_id u).sub_const 1)
  have hleft := (hasDerivAt_const u (1 : ℝ)).div hp (mul_ne_zero hu0 hm)
  have hright := hl.div ((hasDerivAt_id u).pow 2) (pow_ne_zero 2 hu0)
  apply (hleft.sub hright).congr_deriv
  unfold correctionASecond
  field_simp [hu0, hm]
  <;> ring

theorem correctionB_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt correctionB (correctionBFirst u) u := by
  have hp : 0 < u + 1 := by linarith
  have hd := (hasDerivAt_const u (191 / 59 : ℝ)).div
    ((hasDerivAt_id u).add_const 1) hp.ne'
  apply (hd.log (div_pos (by norm_num) hp).ne').congr_deriv
  unfold correctionBFirst
  field_simp [hp.ne']
  <;> ring

theorem correctionBFirst_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt correctionBFirst (correctionBSecond u) u := by
  have hp : u + 1 ≠ 0 := ne_of_gt (by linarith)
  apply ((hasDerivAt_const u (-1 : ℝ)).div
    ((hasDerivAt_id u).add_const 1) hp).congr_deriv
  unfold correctionBSecond
  ring

theorem correctionValue_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt scalarCorrectionKernel (correctionFirst u) u := by
  exact (correctionA_hasDerivAt hu).mul (correctionB_hasDerivAt hu)

theorem correctionFirst_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt correctionFirst (correctionSecond u) u := by
  have hA := correctionA_hasDerivAt hu
  have hA' := correctionAFirst_hasDerivAt hu
  have hB := correctionB_hasDerivAt hu
  have hB' := correctionBFirst_hasDerivAt hu
  apply ((hA'.mul hB).add (hA.mul hB')).congr_deriv
  unfold correctionSecond
  ring

theorem primeSecond_continuousAt {t : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) :
    ContinuousAt primeSecond t := by
  have h0 : t ≠ 0 := ht.ne'
  have h1 : 1 - t ≠ 0 := ne_of_gt (by linarith)
  have h2 : 1 - 2 * t ≠ 0 := ne_of_gt (by linarith)
  have hq : (1 - 2 * t) / t ≠ 0 := div_ne_zero h2 h0
  unfold primeSecond primeLogSecond primeLogFirst primeLog reciprocal
    reciprocalFirst reciprocalSecond
  fun_prop (disch := first | assumption | positivity)

theorem correctionSecond_continuousAt {u : ℝ} (hu : 1 < u) :
    ContinuousAt correctionSecond u := by
  have h0 : u ≠ 0 := ne_of_gt (by linarith)
  have hm : u - 1 ≠ 0 := (sub_pos.mpr hu).ne'
  have hp : u + 1 ≠ 0 := ne_of_gt (by linarith)
  have hq : (191 / 59 : ℝ) / (u + 1) ≠ 0 := div_ne_zero (by norm_num) hp
  unfold correctionSecond correctionASecond correctionAFirst correctionA
    correctionB correctionBFirst correctionBSecond
  fun_prop (disch := first | assumption | positivity)

theorem prime_regular :
    (∀ t ∈ Icc (59 / 250 : ℝ) (1 / 3), HasDerivAt primeValue (primeFirst t) t) ∧
    (∀ t ∈ Icc (59 / 250 : ℝ) (1 / 3), HasDerivAt primeFirst (primeSecond t) t) ∧
    ContinuousOn primeSecond (Icc (59 / 250 : ℝ) (1 / 3)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact primeValue_hasDerivAt (by linarith [ht.1]) (by linarith [ht.2])
  · intro t ht
    exact primeFirst_hasDerivAt (by linarith [ht.1]) (by linarith [ht.2])
  · intro t ht
    exact (primeSecond_continuousAt (by linarith [ht.1])
      (by linarith [ht.2])).continuousWithinAt

theorem correction_regular :
    (∀ u ∈ Icc (2 : ℝ) (132 / 59),
      HasDerivAt scalarCorrectionKernel (correctionFirst u) u) ∧
    (∀ u ∈ Icc (2 : ℝ) (132 / 59), HasDerivAt correctionFirst (correctionSecond u) u) ∧
    ContinuousOn correctionSecond (Icc (2 : ℝ) (132 / 59)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    exact correctionValue_hasDerivAt (by linarith [hu.1])
  · intro u hu
    exact correctionFirst_hasDerivAt (by linarith [hu.1])
  · intro u hu
    exact (correctionSecond_continuousAt (by linarith [hu.1])).continuousWithinAt

end
end ImbalancedChen.P5U7OriginalMidpoint
