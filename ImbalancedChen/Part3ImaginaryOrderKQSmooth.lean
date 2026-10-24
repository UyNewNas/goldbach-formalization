import ImbalancedChen.Part3ImaginaryOrderKQMoments
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED / 2026-10-24. No acceptance credit.
No compiler, checker, numerical replay or actual source edit is used.

The pinned ContDiff parameter is ℕ∞ω: ∞ means smooth, while ⊤=ω is the
analytic tier. Every C-infinity endpoint below therefore states ∞.

Actual M_n derivative recurrence supplies the smoothness proof, rather than
an assumed C-infinity family. Explicit finite factorial/binomial sums bound
every q derivative on every positive compact q interval, uniformly in t.
The actual complex quotient and actual max-extension are included. The
extension is smooth only strictly above its cutoff; no cutoff claim is made.
-/

namespace ImbalancedChen.Part3.ImaginaryOrderKQSmoothSourceOnly
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKQDerivativeSourceOnly
open ImaginaryOrderKQMomentsSourceOnly
open P3ActualLiteralPacketIntegralSourceOnly

def momentBound (n : ℕ) (a : ℝ) : ℝ := momentCoefficient n a*(4/a)

def inverseBound (n : ℕ) (a : ℝ) : ℝ := (n.factorial : ℝ)/a^(n+1)

/-- Fully explicit scalar bound, involving no K/moment/spectral value. -/
def quotientBound (n : ℕ) (a : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*momentBound i a*inverseBound (n-i) a

lemma momentBound_nonneg (n : ℕ) {a : ℝ} (ha : 0 < a) : 0 ≤ momentBound n a := by
  unfold momentBound momentCoefficient
  positivity

lemma inverseBound_nonneg (n : ℕ) {a : ℝ} (ha : 0 < a) : 0 ≤ inverseBound n a := by
  unfold inverseBound
  positivity

/-- Finite smoothness is proved simultaneously for every ACTUAL moment. -/
theorem qMoment_contDiffOn_nat (n m : ℕ) (t : ℝ) :
    ContDiffOn ℝ n (qMoment m t) (Ioi 0) := by
  induction n generalizing m with
  | zero =>
      apply contDiffOn_zero.mpr
      intro q hq
      exact (qMoment_continuousAt m t hq).continuousWithinAt
  | succ n ih =>
      have hd : DifferentiableOn ℝ (qMoment m t) (Ioi (0 : ℝ)) := by
        intro q hq
        exact (qMoment_hasDerivAt_succ m t hq).differentiableAt.differentiableWithinAt
      have hderiv : ContDiffOn ℝ n (deriv (qMoment m t)) (Ioi (0 : ℝ)) :=
        (ih (m+1)).congr (fun q hq => (qMoment_hasDerivAt_succ m t hq).deriv)
      have hchar : ContDiffOn ℝ ((n : ℕ∞ω)+1) (qMoment m t) (Ioi (0 : ℝ)) ↔
          DifferentiableOn ℝ (qMoment m t) (Ioi (0 : ℝ)) ∧
            ContDiffOn ℝ n (deriv (qMoment m t)) (Ioi (0 : ℝ)) := by
        rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
        simp
      simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
        hchar.mpr ⟨hd,hderiv⟩

theorem qMoment_contDiffOn_infty (m : ℕ) (t : ℝ) :
    ContDiffOn ℝ ∞ (qMoment m t) (Ioi 0) := by
  exact contDiffOn_infty.mpr (fun n => qMoment_contDiffOn_nat n m t)

theorem imaginaryOrderK_contDiffOn_infty (t : ℝ) :
    ContDiffOn ℝ ∞ (imaginaryOrderK t) (Ioi 0) := by
  exact (qMoment_contDiffOn_infty 0 t).congr
    (fun q _ => (qMoment_zero t q).symm)

theorem imaginaryOrderK_div_contDiffOn_infty (t : ℝ) :
    ContDiffOn ℝ ∞ (fun q : ℝ => imaginaryOrderK t q/q) (Ioi 0) := by
  exact (imaginaryOrderK_contDiffOn_infty t).div contDiffOn_id (fun q hq => hq.ne')

theorem imaginaryOrderK_contDiffOn_infty_Icc (t : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (imaginaryOrderK t) (Icc a b) := by
  exact (imaginaryOrderK_contDiffOn_infty t).mono (fun q hq => lt_of_lt_of_le ha hq.1)

theorem imaginaryOrderK_div_contDiffOn_infty_Icc (t : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (fun q : ℝ => imaginaryOrderK t q/q) (Icc a b) := by
  exact (imaginaryOrderK_div_contDiffOn_infty t).mono
    (fun q hq => lt_of_lt_of_le ha hq.1)

/-- Exact actual nth q derivative; the neighborhood is positive, so the
globally defined integral at q<=0 never enters an induction step. -/
theorem iteratedDeriv_imaginaryOrderK (n : ℕ) (t : ℝ) {q : ℝ} (hq : 0 < q) :
    iteratedDeriv n (imaginaryOrderK t) q = qMoment n t q := by
  induction n generalizing q with
  | zero => simpa only [iteratedDeriv_zero] using (qMoment_zero t q).symm
  | succ n ih =>
      have he : iteratedDeriv n (imaginaryOrderK t) =ᶠ[𝓝 q] qMoment n t := by
        filter_upwards [Ioi_mem_nhds hq] with r hr
        exact ih hr
      have hd := (qMoment_hasDerivAt_succ n t hq).congr_of_eventuallyEq he
      simpa only [iteratedDeriv_succ] using hd.deriv

theorem iteratedDeriv_imaginaryOrderK_abs_le (n : ℕ) (t : ℝ) {a q : ℝ}
    (ha : 0 < a) (hq : a ≤ q) :
    |iteratedDeriv n (imaginaryOrderK t) q| ≤ momentBound n a := by
  rw [iteratedDeriv_imaginaryOrderK n t (lt_of_lt_of_le ha hq)]
  exact qMoment_abs_le n t ha hq

lemma inverse_iteratedDerivWithin_abs (n : ℕ) {q : ℝ} (hq : 0 < q) :
    |iteratedDerivWithin n (fun r : ℝ => 1/r) (Ioi 0) q| =
      (n.factorial : ℝ)/q^(n+1) := by
  rw [iteratedDerivWithin_one_div n isOpen_Ioi q hq]
  have hz : (-1-(n : ℤ)) = -((n+1 : ℕ) : ℤ) := by omega
  rw [hz, zpow_neg, zpow_natCast]
  simp [abs_mul, abs_pow, abs_inv, abs_of_pos hq, div_eq_mul_inv]

lemma inverse_iteratedDerivWithin_abs_le (n : ℕ) {a q : ℝ}
    (ha : 0 < a) (hq : a ≤ q) :
    |iteratedDerivWithin n (fun r : ℝ => 1/r) (Ioi 0) q| ≤ inverseBound n a := by
  rw [inverse_iteratedDerivWithin_abs n (lt_of_lt_of_le ha hq)]
  unfold inverseBound
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos ha (n+1))
  gcongr <;> assumption

/-- Leibniz applied to the actual K and the actual reciprocal. The finite
binomial/factorial sum is explicit and uniform on every q>=a>0. -/
theorem iteratedDeriv_imaginaryOrderK_div_abs_le (n : ℕ) (t : ℝ) {a q : ℝ}
    (ha : 0 < a) (hq : a ≤ q) :
    |iteratedDeriv n (fun r : ℝ => imaginaryOrderK t r/r) q| ≤ quotientBound n a := by
  have hqp : 0 < q := lt_of_lt_of_le ha hq
  have hK : ContDiffOn ℝ n (imaginaryOrderK t) (Ioi (0 : ℝ)) :=
    (imaginaryOrderK_contDiffOn_infty t).of_le (by simp)
  have hInv : ContDiffOn ℝ n (fun r : ℝ => 1/r) (Ioi (0 : ℝ)) :=
    contDiffOn_const.div contDiffOn_id (fun r hr => hr.ne')
  have hmul := iteratedDerivWithin_mul hqp isOpen_Ioi.uniqueDiffOn
    (hK q hqp) (hInv q hqp)
  have he : (fun r : ℝ => imaginaryOrderK t r/r) =
      (fun r : ℝ => imaginaryOrderK t r*(1/r)) := by funext r; ring
  rw [he, ← iteratedDerivWithin_of_isOpen isOpen_Ioi q hqp]
  change |iteratedDerivWithin n ((imaginaryOrderK t)*(fun r : ℝ => 1/r)) (Ioi 0) q| ≤ _
  rw [hmul]
  calc
    |∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
        iteratedDerivWithin i (imaginaryOrderK t) (Ioi 0) q*
          iteratedDerivWithin (n-i) (fun r : ℝ => 1/r) (Ioi 0) q| ≤
        ∑ i ∈ Finset.range (n+1), |(n.choose i : ℝ)*
          iteratedDerivWithin i (imaginaryOrderK t) (Ioi 0) q*
            iteratedDerivWithin (n-i) (fun r : ℝ => 1/r) (Ioi 0) q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ quotientBound n a := by
      apply Finset.sum_le_sum
      intro i _hi
      have hA : |iteratedDerivWithin i (imaginaryOrderK t) (Ioi 0) q| ≤ momentBound i a := by
        rw [iteratedDerivWithin_of_isOpen isOpen_Ioi q hqp]
        exact iteratedDeriv_imaginaryOrderK_abs_le i t ha hq
      have hB := inverse_iteratedDerivWithin_abs_le (n-i) ha hq
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose i))]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _)) hB
        (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (momentBound_nonneg i ha))

theorem complexK_contDiffOn_infty (t : ℝ) :
    ContDiffOn ℝ ∞ (fun q : ℝ => (imaginaryOrderK t q : ℂ)) (Ioi 0) := by
  simpa only [Complex.ofRealCLM_apply] using
    Complex.ofRealCLM.contDiff.comp_contDiffOn (imaginaryOrderK_contDiffOn_infty t)

theorem complexK_div_contDiffOn_infty (t : ℝ) :
    ContDiffOn ℝ ∞ (fun q : ℝ => (imaginaryOrderK t q : ℂ)/(q : ℂ)) (Ioi 0) := by
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_div] using
    Complex.ofRealCLM.contDiff.comp_contDiffOn (imaginaryOrderK_div_contDiffOn_infty t)

/-- Ordinary real-to-complex calculus helper. Main endpoints instantiate it
only with the actual smooth functions already proved above. -/
lemma iteratedDeriv_ofReal_on_positive {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) (n : ℕ) {q : ℝ} (hq : 0 < q) :
    iteratedDeriv n (fun r : ℝ => (f r : ℂ)) q = (iteratedDeriv n f q : ℂ) := by
  have hsmooth (m : ℕ) : ContDiffOn ℝ ∞ (iteratedDeriv m f) (Ioi (0 : ℝ)) := by
    induction m with
    | zero => simpa only [iteratedDeriv_zero] using hf
    | succ m ih =>
        rw [iteratedDeriv_succ]
        exact ih.deriv_of_isOpen isOpen_Ioi (by simp)
  induction n generalizing q with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
      have hreal := ((hsmooth n).contDiffAt (Ioi_mem_nhds hq)).differentiableAt (by simp)
      have hd := hreal.hasDerivAt.ofReal_comp
      have he : iteratedDeriv n (fun r : ℝ => (f r : ℂ)) =ᶠ[𝓝 q]
          (fun r : ℝ => (iteratedDeriv n f r : ℂ)) := by
        filter_upwards [Ioi_mem_nhds hq] with r hr
        exact ih hr
      have hc := hd.congr_of_eventuallyEq he
      simpa only [iteratedDeriv_succ] using hc.deriv

theorem iteratedDeriv_complexK_norm_le (n : ℕ) (t : ℝ) {a q : ℝ}
    (ha : 0 < a) (hq : a ≤ q) :
    ‖iteratedDeriv n (fun r : ℝ => (imaginaryOrderK t r : ℂ)) q‖ ≤ momentBound n a := by
  rw [iteratedDeriv_ofReal_on_positive (imaginaryOrderK_contDiffOn_infty t) n
    (lt_of_lt_of_le ha hq)]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    iteratedDeriv_imaginaryOrderK_abs_le n t ha hq

theorem iteratedDeriv_complexK_div_norm_le (n : ℕ) (t : ℝ) {a q : ℝ}
    (ha : 0 < a) (hq : a ≤ q) :
    ‖iteratedDeriv n (fun r : ℝ => (imaginaryOrderK t r : ℂ)/(r : ℂ)) q‖ ≤
      quotientBound n a := by
  have h := iteratedDeriv_ofReal_on_positive (imaginaryOrderK_div_contDiffOn_infty t) n
    (lt_of_lt_of_le ha hq)
  simp only [Complex.ofReal_div] at h
  rw [h]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    iteratedDeriv_imaginaryOrderK_div_abs_le n t ha hq

theorem compact_q_all_order_bounds (n : ℕ) (t : ℝ) {a b q : ℝ}
    (ha : 0 < a) (hq : q ∈ Icc a b) :
    |iteratedDeriv n (imaginaryOrderK t) q| ≤ momentBound n a ∧
      |iteratedDeriv n (fun r : ℝ => imaginaryOrderK t r/r) q| ≤ quotientBound n a ∧
      ‖iteratedDeriv n (fun r : ℝ => (imaginaryOrderK t r : ℂ)) q‖ ≤ momentBound n a ∧
      ‖iteratedDeriv n (fun r : ℝ => (imaginaryOrderK t r : ℂ)/(r : ℂ)) q‖ ≤
        quotientBound n a := by
  exact ⟨iteratedDeriv_imaginaryOrderK_abs_le n t ha hq.1,
    iteratedDeriv_imaginaryOrderK_div_abs_le n t ha hq.1,
    iteratedDeriv_complexK_norm_le n t ha hq.1,
    iteratedDeriv_complexK_div_norm_le n t ha hq.1⟩

theorem extendedKKernel_contDiffOn_infty (a : ℝ) (ha : 0 < a) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun q : ℝ => extendedKKernel a ha t q) (Ioi a) := by
  intro q hq
  have hqp : 0 < q := lt_trans ha hq
  have hc := (complexK_div_contDiffOn_infty t).contDiffAt (Ioi_mem_nhds hqp)
  have he : (fun r : ℝ => extendedKKernel a ha t r) =ᶠ[𝓝 q]
      (fun r : ℝ => (imaginaryOrderK t r : ℂ)/(r : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hq] with r hr
    exact extendedKKernel_eq a ha t r hr.le
  exact (hc.congr_of_eventuallyEq he).contDiffWithinAt

theorem extendedKKernel_iteratedDeriv_norm_le (n : ℕ) (t c : ℝ) (hc : 0 < c)
    {a q : ℝ} (ha : 0 < a) (hqa : a ≤ q) (hcq : c < q) :
    ‖iteratedDeriv n (fun r : ℝ => extendedKKernel c hc t r) q‖ ≤ quotientBound n a := by
  have he : (fun r : ℝ => extendedKKernel c hc t r) =ᶠ[𝓝 q]
      (fun r : ℝ => (imaginaryOrderK t r : ℂ)/(r : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hcq] with r hr
    exact extendedKKernel_eq c hc t r hr.le
  rw [Filter.EventuallyEq.iteratedDeriv_eq n he]
  exact iteratedDeriv_complexK_div_norm_le n t ha hqa

theorem compact_extendedKKernel_all_order_bound (n : ℕ) (t c : ℝ) (hc : 0 < c)
    {a b q : ℝ} (hca : c < a) (hq : q ∈ Icc a b) :
    ‖iteratedDeriv n (fun r : ℝ => extendedKKernel c hc t r) q‖ ≤ quotientBound n a := by
  exact extendedKKernel_iteratedDeriv_norm_le n t c hc (lt_trans hc hca) hq.1
    (lt_of_lt_of_le hca hq.1)

/-- Smooth real q extension of the ACTUAL restricted kernel, on an open
neighborhood of the full physical region. Subtypes are not treated as a
normed vector space; q derivatives are those of this actual real extension. -/
theorem physical_extendedKKernel_contDiffOn_infty {ι : Type*} (P : PacketData ι) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun q : ℝ => extendedKKernel (P.Y0/32)
      (by have h := P.Y0_pos; positivity) t q) (Ioi (P.Y0/32)) := by
  exact extendedKKernel_contDiffOn_infty (P.Y0/32)
    (by have h := P.Y0_pos; positivity) t

theorem physical_extendedKKernel_iteratedDeriv_norm_le {ι : Type*} (P : PacketData ι)
    (n : ℕ) (t q : ℝ) (hq : q ∈ P.region) :
    ‖iteratedDeriv n (fun r : ℝ => extendedKKernel (P.Y0/32)
      (by have h := P.Y0_pos; positivity) t r) q‖ ≤ quotientBound n (P.Y0/16) := by
  have ha : 0 < P.Y0/16 := by have h := P.Y0_pos; positivity
  have hcq : P.Y0/32 < q := by linarith [P.Y0_pos, hq.1]
  exact extendedKKernel_iteratedDeriv_norm_le n t (P.Y0/32)
    (by have h := P.Y0_pos; positivity) ha hq.1 hcq

/-- The specific restricted continuous kernel is the restriction of the
proved smooth real-q extension. No differentiable vector-space structure
is falsely assigned to the closed-interval subtype P.region. -/
theorem restrictedKKernel_smooth_extension {ι : Type*} (P : PacketData ι) (t : ℝ) :
    (∀ q : P.region,
      ImaginaryOrderKExplicitMajorantSourceOnly.restrictedKKernel P t q =
        extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) t (q : ℝ)) ∧
      ContDiffOn ℝ ∞ (fun q : ℝ => extendedKKernel (P.Y0/32)
        (by have h := P.Y0_pos; positivity) t q) (Ioi (P.Y0/32)) := by
  refine ⟨?_, physical_extendedKKernel_contDiffOn_infty P t⟩
  intro q
  rfl

end
end ImbalancedChen.Part3.ImaginaryOrderKQSmoothSourceOnly
