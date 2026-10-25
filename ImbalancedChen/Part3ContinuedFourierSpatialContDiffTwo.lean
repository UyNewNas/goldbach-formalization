import ImbalancedChen.Part3ContinuedFourierNonconstantMaass
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

Genuine two-variable C2 of the actual continued nonconstant completed
Fourier kernel. Every spatial moment term is first proved Frechet
differentiable directly by composition and multiplication of its qMoment
and phase factors. Its derivative is identified as a continuous linear map
from the already proved coordinate restrictions. An actual summable uniform
operator-norm bound then differentiates the infinite sum by Mathlib's
Frechet series theorem.

The derivative of a moment sum is a fixed bounded linear combination of
two shifted moment sums. Continuity gives C1; applying C1 to the shifts
gives C2 through the genuine Frechet derivative criterion. This is not an
inference of C2 from coordinatewise derivative existence alone.
-/

namespace ImbalancedChen.Part3.ContinuedFourierSpatialContDiffTwo

noncomputable section

open Set Filter Topology
open ImbalancedChen.Part3.ComplexOrderKQCalculus
open ImbalancedChen.Part3.ContinuedFourierSpatialMoments
open ImbalancedChen.Part3.ContinuedFourierMomentSeriesCalculus

def upperChart : Set (ℝ × ℝ) := {p | 0 < p.2}

theorem upperChart_isOpen : IsOpen upperChart := isOpen_lt continuous_const continuous_snd

def firstLift : ℂ →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ (ContinuousLinearMap.fst ℝ ℝ ℝ)

def secondLift : ℂ →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ (ContinuousLinearMap.snd ℝ ℝ ℝ)

def coordinateLinear (a b : ℂ) : (ℝ × ℝ) →L[ℝ] ℂ := firstLift a + secondLift b

@[simp] theorem coordinateLinear_apply (a b : ℂ) (h : ℝ × ℝ) :
    coordinateLinear a b h = h.1 • a + h.2 • b := by
  simp [coordinateLinear, firstLift, secondLift]

theorem coordinateLinear_norm_le (a b : ℂ) : ‖coordinateLinear a b‖ ≤ ‖a‖ + ‖b‖ := by
  simpa [coordinateLinear, firstLift, secondLift] using norm_add_le (firstLift a) (secondLift b)

private theorem hasFDerivAt_coordinateLinear {f : ℝ × ℝ → ℂ} {x y : ℝ} {a b : ℂ}
    (hf : DifferentiableAt ℝ f (x, y))
    (hx : HasDerivAt (fun t : ℝ => f (t, y)) a x)
    (hy : HasDerivAt (fun t : ℝ => f (x, t)) b y) :
    HasFDerivAt f (coordinateLinear a b) (x, y) := by
  have hpathx : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have hpathy : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have h1 : fderiv ℝ f (x, y) (1, 0) = a :=
    (hf.hasFDerivAt.comp_hasDerivAt x hpathx).unique hx
  have h2 : fderiv ℝ f (x, y) (0, 1) = b :=
    (hf.hasFDerivAt.comp_hasDerivAt y hpathy).unique hy
  have heq : fderiv ℝ f (x, y) = coordinateLinear a b := by
    ext h
    have hsplit : h = h.1 • (1, 0) + h.2 • (0, 1) := by ext <;> simp
    calc
      fderiv ℝ f (x, y) h =
          fderiv ℝ f (x, y) (h.1 • (1, 0) + h.2 • (0, 1)) := congrArg _ hsplit
      _ = h.1 • a + h.2 • b := by simp [h1, h2]
      _ = coordinateLinear a b h := by simp
  exact hf.hasFDerivAt.congr_fderiv heq

def termGradient (j k n : ℕ) (s : ℂ) (x y : ℝ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  coordinateLinear (spatialMomentTerm (j + 1) k n s y x)
    (spatialMomentTerm j (k + 1) n s y x)

/-- Direct two-variable differentiability precedes derivative identification. -/
theorem spatialMomentTerm_hasFDerivAt (j k n : ℕ) (s : ℂ)
    (x y : ℝ) (hy : 0 < y) :
    HasFDerivAt (fun p : ℝ × ℝ => spatialMomentTerm j k n s p.2 p.1)
      (termGradient j k n s x y) (x, y) := by
  have hw : 0 < frequency (n + 1) := by unfold frequency; positivity
  have hq : DifferentiableAt ℝ (fun p : ℝ × ℝ => frequency (n + 1) * p.2) (x, y) := by
    fun_prop
  have hK := (qMoment_hasDerivAt k (s - 1 / 2) (mul_pos hw hy)).differentiableAt.comp (x, y) hq
  have hphase := (phase_hasDerivAt (n + 1) x).differentiableAt.comp (x, y) differentiableAt_fst
  have hd : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => spatialMomentTerm j k n s p.2 p.1) (x, y) := by
    exact (hK.const_mul
      (spectralCoefficient n s * (Complex.I * (frequency (n + 1) : ℂ)) ^ j *
        (frequency (n + 1) : ℂ) ^ k)).mul hphase
  exact hasFDerivAt_coordinateLinear hd
    (spatialMomentTerm_hasDerivAt_x j k n s y x)
    (spatialMomentTerm_hasDerivAt_y j k n s y x hy)

theorem termGradient_norm_bound (j k M : ℕ) {a : ℝ} (ha : 0 < a)
    (n : ℕ) {s : ℂ} (hs : |s.re| ≤ (M : ℝ)) {x y : ℝ} (hy : a ≤ y) :
    ‖termGradient j k n s x y‖ ≤
      spatialMajorant (j + 1) k M a n + spatialMajorant j (k + 1) M a n := by
  exact (coordinateLinear_norm_le _ _).trans
    (add_le_add (spatialMomentTerm_norm_bound (j + 1) k M ha n hs hy x)
      (spatialMomentTerm_norm_bound j (k + 1) M ha n hs hy x))

def sumGradient (j k : ℕ) (s : ℂ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  coordinateLinear (momentSum (j + 1) k s p.2 p.1) (momentSum j (k + 1) s p.2 p.1)

theorem termGradient_tsum (j k : ℕ) (s : ℂ) (x y : ℝ) (hy : 0 < y) :
    (∑' n : ℕ, termGradient j k n s x y) = sumGradient j k s (x, y) := by
  have hx := (spatialMoment_norm_summable (j + 1) k s hy x).of_norm
  have hv := (spatialMoment_norm_summable j (k + 1) s hy x).of_norm
  unfold termGradient sumGradient coordinateLinear momentSum
  rw [(firstLift.summable hx).tsum_add (secondLift.summable hv),
    ← firstLift.map_tsum hx, ← secondLift.map_tsum hv]

/-- Genuine Frechet differentiation under the continued two-variable sum. -/
theorem momentSum_hasFDerivAt (j k : ℕ) (s : ℂ) (x y : ℝ) (hy : 0 < y) :
    HasFDerivAt (fun p : ℝ × ℝ => momentSum j k s p.2 p.1)
      (sumGradient j k s (x, y)) (x, y) := by
  let M : ℕ := Nat.ceil |s.re|
  have ha : 0 < y / 2 := by linarith
  let u : ℕ → ℝ := fun n => spatialMajorant (j + 1) k M (y / 2) n +
    spatialMajorant j (k + 1) M (y / 2) n
  have hu : Summable u := (spatialMajorant_summable (j + 1) k M ha).add
    (spatialMajorant_summable j (k + 1) M ha)
  have hp : (x, y) ∈ Ioo (x - 1) (x + 1) ×ˢ Ioo (y / 2) (3 * y / 2) := by
    constructor <;> constructor <;> linarith
  have h := hasFDerivAt_tsum_of_isPreconnected
    (f := fun (n : ℕ) (p : ℝ × ℝ) => spatialMomentTerm j k n s p.2 p.1)
    (f' := fun (n : ℕ) (p : ℝ × ℝ) => termGradient j k n s p.1 p.2)
    (u := u) (s := Ioo (x - 1) (x + 1) ×ˢ Ioo (y / 2) (3 * y / 2))
    hu (isOpen_Ioo.prod isOpen_Ioo) (isPreconnected_Ioo.prod isPreconnected_Ioo)
    (fun n p ht => spatialMomentTerm_hasFDerivAt j k n s p.1 p.2 (ha.trans ht.2.1))
    (fun n p ht => termGradient_norm_bound j k M ha n (Nat.le_ceil _) ht.2.1.le)
    hp (spatialMoment_norm_summable j k s hy x).of_norm hp
  exact h.congr_fderiv (termGradient_tsum j k s x y hy)

theorem momentSum_continuousOn (j k : ℕ) (s : ℂ) :
    ContinuousOn (fun p : ℝ × ℝ => momentSum j k s p.2 p.1) upperChart := by
  intro p hp
  exact (momentSum_hasFDerivAt j k s p.1 p.2 hp).continuousAt.continuousWithinAt

theorem sumGradient_continuousOn (j k : ℕ) (s : ℂ) :
    ContinuousOn (sumGradient j k s) upperChart := by
  exact (firstLift.continuous.comp_continuousOn (momentSum_continuousOn (j + 1) k s)).add
    (secondLift.continuous.comp_continuousOn (momentSum_continuousOn j (k + 1) s))

theorem momentSum_contDiffOn_one (j k : ℕ) (s : ℂ) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => momentSum j k s p.2 p.1) upperChart := by
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (n := 0) upperChart_isOpen.uniqueDiffOn).2
  refine ⟨?_, sumGradient j k s, contDiffOn_zero.mpr (sumGradient_continuousOn j k s), ?_⟩
  · intro h
    norm_num at h
  · intro p hp
    exact (momentSum_hasFDerivAt j k s p.1 p.2 hp).hasFDerivWithinAt

theorem sumGradient_contDiffOn_one (j k : ℕ) (s : ℂ) :
    ContDiffOn ℝ 1 (sumGradient j k s) upperChart := by
  exact (firstLift.contDiff.comp_contDiffOn (momentSum_contDiffOn_one (j + 1) k s)).add
    (secondLift.contDiff.comp_contDiffOn (momentSum_contDiffOn_one j (k + 1) s))

/-- C2 of every actual moment sum in both real spatial variables. -/
theorem momentSum_contDiffOn_two (j k : ℕ) (s : ℂ) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => momentSum j k s p.2 p.1) upperChart := by
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (n := 1) upperChart_isOpen.uniqueDiffOn).2
  refine ⟨?_, sumGradient j k s, sumGradient_contDiffOn_one j k s, ?_⟩
  · intro h
    norm_num at h
  · intro p hp
    exact (momentSum_hasFDerivAt j k s p.1 p.2 hp).hasFDerivWithinAt

/-- The literal completed nonconstant kernel is genuinely C2 on the full
positive-height real chart at every complex spectral parameter. -/
theorem weightedKernel_contDiffOn_two (s : ℂ) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => weightedKernel s p.2 p.1) upperChart := by
  have hp := momentSum_contDiffOn_two 0 0 s
  have hmap : ContDiff ℝ 2 (fun p : ℝ × ℝ => (-p.1, p.2)) := by fun_prop
  have hn : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => momentSum 0 0 s p.2 (-p.1)) upperChart :=
    hp.comp hmap.contDiffOn (fun p hp => hp)
  have hsqrt : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sqrt p.2) upperChart :=
    contDiffOn_snd.sqrt (fun p hp => ne_of_gt hp)
  have hroot : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (Real.sqrt p.2 : ℂ)) upperChart :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hsqrt
  apply ((hroot.const_mul (2 : ℂ)).mul (hp.add hn)).congr
  intro p hp
  rw [weightedKernel, ← signedMomentSum_zero_zero_eq_actual s p.2 p.1 hp]
  simp only [signedMomentSum, pow_zero, one_mul]

end

end ImbalancedChen.Part3.ContinuedFourierSpatialContDiffTwo
