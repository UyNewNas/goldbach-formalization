/-
SOURCE ONLY -- 2026-10-23. NO compilation/Lean/lake/typechecker/CI.
Author: /root/p3_common_interval_phase_separation_sol_max_oct22.

Complete uncompiled `by` bodies for three actual analytic steps:
 (A) one REAL compact-support coordinate, normalized period P=64:
     endpoint vanishing, L successive actual IBPs, and coefficient bounds;
 (B) another slice remains continuous after this actual coefficient integral;
 (C) a stronger existing MULTIDIMENSIONAL Fourier derivative bound is
     specialized to compact C^r functions with derivative order EXACTLY r.

No hb, four-dimensional Fourier separation, or desired weighted-l1/HasSum
conclusion is assumed. The explicit inputs of(A) are finite C^L regularity,
geometric support inside(-32,32), and a bound on the actual L-th derivative.
The input of(B) is a jointly continuous real-coordinate/compact-parameter
kernel. The input of(C) is actual compact support and finite C^r regularity.
The final comment lists the remaining actualNormalizedF dependencies.

Fixed mathlib: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
Read pinned primary sources (all displayed declarations have by proofs):
 Analysis/Fourier/AddCircle.lean, blob3f5c6ed72797f568db7740186fc4ee2f0cdf0fed:
  fourierCoeffOn_eq_integral357--366; IBP586--603.
 Analysis/Calculus/IteratedDeriv/Defs.lean,
  blob301c2076a2ee07b61d38cacb1d0995e327a36500:
  continuous/differentiable iterated derivatives285--302; successor306--308.
 Analysis/Calculus/Deriv/Support.lean,
  blob2e0f13e2809671ab3f7a797c8e33d1da18e45f2b:
  tsupport_deriv_subset, with no differentiability premise.
 Analysis/Calculus/ContDiff/FTaylorSeries.lean,
  blob084664a10b855ddacd40c45817aae5c2dd2f73da:
  HasCompactSupport.iteratedFDeriv871--873.
 Topology/Algebra/Support.lean, blob6724d9a28680cfee734a0e2be71203cd5ca0d9ee:
  generated image_eq_zero_of_notMem_tsupport112--113.
 MeasureTheory/Integral/IntervalIntegral/Basic.lean,
  blob89cf34cb5387b20f311300f6e708aa752ebf3a23:
  norm integral bound769--771; CLM/integral commutation870--872.
 Topology/CompactOpen.lean, blob72358cfcca49fb9e41916f095309bc5f605d24ba:
  ContinuousMap.curry430--435.
 Analysis/Fourier/FourierTransformDeriv.lean,
  blob01d43a1b8b62e8070087c93a29ff4fba3c52173b:
  Real.pow_mul_norm_iteratedFDeriv_fourier_le730--736.

Stronger native Fourier primitives FOUND and inspected:
  AddCircleMulti.lean, blob08ab569e1977c455fdde0a67df2131ea1fc864c5,
  UnitAddTorus.mFourierCoeff_eq_integral251--255 and
  hasSum_mFourier_series_apply_of_summable329--332, actual multidim inversion.
  SchwartzSpace/Fourier.lean, blob29b759c53de55f6eee6359d7603e7a12c94d70e1,
  actual multidim Schwartz fourierTransformCLM51--84. At output derivative
  order0 and polynomial weight r, its displayed proof uses input derivative
  orders at most r. Its finite moment orders cause no x^eta loss on the
  fixed compact support. Thus a Schwartz route can ALSO retain r=4L.
  The deprecated FourierSchwartz.lean is merely a shim; it is NOT a decay API.

This file prefers the quantitative theorem underlying that Schwartz proof
in(C), avoiding an implicit-continuity argument with unknown seminorm orders.
It does not falsely claim that matching the original coefficient to the
multidimensional Fourier integral has already been formalized.
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.CompactOpen
import Mathlib.Tactic

noncomputable section

open Set MeasureTheory
open scoped Interval BigOperators FourierTransform

namespace P3CompactCoordinateSourceOnly

private theorem h64 : (-32 : ℝ) < 32 := by norm_num

def coeff64 (f : ℝ → ℂ) (n : ℤ) : ℂ := fourierCoeffOn h64 f n

def ibpScale64 (n : ℤ) : ℂ := 64 / (2 * (Real.pi : ℂ) * Complex.I * n)

lemma jet_tsupport_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using (Subset.rfl : tsupport f ⊆ tsupport f)
  | succ j ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih

lemma compact_of_inside64 (f : ℝ → ℂ)
    (hs : tsupport f ⊆ Ioo (-32 : ℝ) 32) : HasCompactSupport f := by
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport f)
    (hs.trans Ioo_subset_Icc_self)

lemma jet_zero_outside64 (f : ℝ → ℂ)
    (hs : tsupport f ⊆ Ioo (-32 : ℝ) 32)
    (j : ℕ) (x : ℝ) (hx : x ∉ Ioo (-32 : ℝ) 32) : iteratedDeriv j f x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact hx (hs (jet_tsupport_subset f j hmem))

lemma jet_zero_left64 (f : ℝ → ℂ)
    (hs : tsupport f ⊆ Ioo (-32 : ℝ) 32) (j : ℕ) :
    iteratedDeriv j f (-32) = 0 := by
  exact jet_zero_outside64 f hs j (-32) (by simp)

lemma jet_zero_right64 (f : ℝ → ℂ)
    (hs : tsupport f ⊆ Ioo (-32 : ℝ) 32) (j : ℕ) :
    iteratedDeriv j f 32 = 0 := by
  exact jet_zero_outside64 f hs j 32 (by simp)

/- An actual IBP of an actual derivative of the given compact slice.
   There is no separately assumed jet identity or endpoint cancellation. -/
lemma coeff64_jet_ibp (f : ℝ → ℂ) (L : ℕ) (hf : ContDiff ℝ L f)
    (hs : tsupport f ⊆ Ioo (-32 : ℝ) 32)
    (j : ℕ) (hj : j < L) (n : ℤ) (hn : n ≠ 0) :
    coeff64 (iteratedDeriv j f) n =
      ibpScale64 n * coeff64 (iteratedDeriv (j+1) f) n := by
  have hcj : Continuous (iteratedDeriv j f) :=
    ContDiff.continuous_iteratedDeriv j hf (by exact_mod_cast Nat.le_of_lt hj)
  have hcj1 : Continuous (iteratedDeriv (j+1) f) :=
    ContDiff.continuous_iteratedDeriv (j+1) hf (by exact_mod_cast (show j+1 ≤ L by omega))
  have hdj : Differentiable ℝ (iteratedDeriv j f) :=
    ContDiff.differentiable_iteratedDeriv j hf (by exact_mod_cast hj)
  have hd (x : ℝ) :
      HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j+1) f x) x := by
    simpa only [iteratedDeriv_succ] using (hdj x).hasDerivAt
  have hi := fourierCoeffOn_of_hasDerivAt_Ioo h64 hn hcj.continuousOn
    (fun x _hx => hd x) (hcj1.intervalIntegrable (-32) 32)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  change fourierCoeffOn h64 (iteratedDeriv j f) n =
    ibpScale64 n * fourierCoeffOn h64 (iteratedDeriv (j+1) f) n
  rw [hi, jet_zero_right64 f hs j, jet_zero_left64 f hs j]
  simp only [sub_self, mul_zero, zero_sub]
  unfold ibpScale64
  field_simp [hnC, hpiC, Complex.I_ne_zero]; norm_num; ring

lemma coeff64_iterated_ibp (f : ℝ → ℂ) (L : ℕ) (hf : ContDiff ℝ L f)
    (hs : tsupport f ⊆ Ioo (-32 : ℝ) 32) (n : ℤ) (hn : n ≠ 0) :
    coeff64 f n = (ibpScale64 n)^L * coeff64 (iteratedDeriv L f) n := by
  have hrec : ∀ j : ℕ, j ≤ L →
      coeff64 f n = (ibpScale64 n)^j * coeff64 (iteratedDeriv j f) n := by
    intro j
    induction j with
    | zero => intro _hj; simp only [pow_zero, one_mul, iteratedDeriv_zero]
    | succ j ih =>
        intro hj
        rw [ih (by omega), coeff64_jet_ibp f L hf hs j (by omega) n hn, pow_succ]
        ring
  exact hrec L le_rfl

/- Normalized period64 Fourier coefficient has operator bound1 against
   the sup on [-32,32]. Normalization and the length64 cancel exactly. -/
lemma norm_coeff64_le (f : ℝ → ℂ) (n : ℤ) (M : ℝ)
    (hM : ∀ x ∈ Icc (-32 : ℝ) 32, ‖f x‖ ≤ M) : ‖coeff64 f n‖ ≤ M := by
  have hphase (x : ℝ) : ‖fourier (-n) (x : AddCircle (64 : ℝ))‖ = 1 := by
    exact Circle.norm_coe _
  have hI :
      ‖∫ x in (-32 : ℝ)..32, fourier (-n) (x : AddCircle (64 : ℝ)) • f x‖
        ≤ M * 64 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-32 : ℝ)) (b := 32)
      (f := fun x => fourier (-n) (x : AddCircle (64 : ℝ)) • f x)
      (C := M) (fun x hx => by
        have hx' : x ∈ Ioc (-32 : ℝ) 32 := by
          simpa only [uIoc_of_le (show (-32 : ℝ) ≤ 32 by norm_num)] using hx
        simpa only [norm_smul, hphase, one_mul] using hM x (Ioc_subset_Icc_self hx'))
    norm_num at hh ⊢
    exact hh
  calc
    ‖coeff64 f n‖ = (1/64 : ℝ) *
        ‖∫ x in (-32 : ℝ)..32, fourier (-n) (x : AddCircle (64 : ℝ)) • f x‖ := by
      rw [coeff64, fourierCoeffOn_eq_integral, norm_smul]
      norm_num
    _ ≤ (1/64 : ℝ) * (M*64) := mul_le_mul_of_nonneg_left hI (by norm_num)
    _ = M := by ring

lemma norm_ibpScale64 (n : ℤ) :
    ‖ibpScale64 n‖ = 64 / (2 * Real.pi * |(n : ℝ)|) := by
  norm_num [ibpScale64, norm_div, norm_mul, Complex.norm_real,
    Complex.norm_intCast, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/- The requested nonzero-frequency L-times IBP bound. The only regularity
   order used is L; there is no use of the later Poisson tail order J. -/
theorem norm_coeff64_iterated_le
    (f : ℝ → ℂ) (L : ℕ) (hf : ContDiff ℝ L f)
    (hs : tsupport f ⊆ Ioo (-32 : ℝ) 32) (n : ℤ) (hn : n ≠ 0)
    (ML : ℝ) (hML : ∀ x ∈ Icc (-32 : ℝ) 32, ‖iteratedDeriv L f x‖ ≤ ML) :
    ‖coeff64 f n‖ ≤ (64 / (2*Real.pi*|(n : ℝ)|))^L * ML := by
  rw [coeff64_iterated_ibp f L hf hs n hn, norm_mul, norm_pow, norm_ibpScale64]
  exact mul_le_mul_of_nonneg_left
    (norm_coeff64_le (iteratedDeriv L f) n ML hML) (by positivity)

/- Integrating in one real coordinate preserves continuity of another
   compact parameter, with the EXACT coeff64 integral, not an abstract
   unknown coefficient function. No domination hypothesis is inserted:
   continuity on the compact integration interval supplies integrability. -/
section Parameter

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]

def coeff64Other (G : C(ℝ × Y, ℂ)) (n : ℤ) : C(Y, ℂ) :=
  (1/64 : ℝ) • ∫ t in (-32 : ℝ)..32,
    fourier (-n) (t : AddCircle (64 : ℝ)) • G.curry t

lemma coeff64Other_apply (G : C(ℝ × Y, ℂ)) (n : ℤ) (y : Y) :
    coeff64Other G n y = coeff64 (fun t => G (t,y)) n := by
  let H : ℝ → C(Y, ℂ) := fun t =>
    fourier (-n) (t : AddCircle (64 : ℝ)) • G.curry t
  have hH : Continuous H :=
    (((fourier (-n)).continuous.comp (AddCircle.continuous_mk' (64 : ℝ))).smul
      G.curry.continuous)
  have hHI : IntervalIntegrable H volume (-32) 32 := hH.intervalIntegrable _ _
  have hev : (∫ t in (-32 : ℝ)..32, H t) y =
      ∫ t in (-32 : ℝ)..32, H t y := by
    exact ((ContinuousMap.evalCLM ℝ y).intervalIntegral_comp_comm hHI).symm
  unfold coeff64Other
  rw [ContinuousMap.smul_apply]
  rw [coeff64, fourierCoeffOn_eq_integral]
  norm_num only [sub_neg_eq_add, show (32 : ℝ) + 32 = 64 by norm_num]
  simpa only [H, ContinuousMap.smul_apply, ContinuousMap.curry_apply,
    fourier_coe_apply, show (32 : ℝ) - -32 = 64 by norm_num] using
    congrArg (fun q : ℂ => (1/64 : ℝ) • q) hev

theorem continuous_coeff64_other_slice (G : C(ℝ × Y, ℂ)) (n : ℤ) :
    Continuous (fun y : Y => coeff64 (fun t => G (t,y)) n) := by
  have hc := (coeff64Other G n).continuous
  change Continuous (fun y : Y => coeff64Other G n y) at hc
  simpa only [coeff64Other_apply] using hc

end Parameter

/- Stronger existing multidimensional quantitative input, specialized
   without losing control over the finite derivative order. It is the
   theorem used in the actual Schwartz Fourier transform continuity proof.
   In dimension4 choose r=4L, giving EXACTLY the wanted 4L derivative cost.
   This route avoids differentiating nested coefficient integrals. -/
section Multidimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem compact_fourier_weight_bound (f : V → ℂ) (r : ℕ)
    (hf : ContDiff ℝ r f) (hs : HasCompactSupport f) (w : V) :
    ‖w‖^r * ‖𝓕 f w‖ ≤ 2^r *
      ∑ j ∈ Finset.range (r+1), ∫ v : V, ‖iteratedFDeriv ℝ j f v‖ := by
  have hi (j : ℕ) (hj : j ≤ r) :
      Integrable (fun v : V => ‖iteratedFDeriv ℝ j f v‖) := by
    have hfj : ContDiff ℝ j f := hf.of_le (by exact_mod_cast hj)
    exact hfj.continuous_iteratedFDeriv'.norm.integrable_of_hasCompactSupport
      (hs.iteratedFDeriv j).norm
  have hp : ∀ (k j : ℕ), k ≤ (0 : ℕ∞) → j ≤ (r : ℕ∞) →
      Integrable (fun v : V => ‖v‖^k * ‖iteratedFDeriv ℝ j f v‖) := by
    intro k j hk hj
    have hk0 : k = 0 := by
      have hk' : k ≤ 0 := by exact_mod_cast hk
      omega
    subst k
    simpa only [pow_zero, one_mul] using hi j (by exact_mod_cast hj)
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (K := (0 : ℕ∞)) (N := (r : ℕ∞)) hf hp
    (k := 0) (n := r) (by simp) (by simp) w
  simpa [Finset.sum_product, norm_iteratedFDeriv_zero] using h

end Multidimensional

end P3CompactCoordinateSourceOnly

/-
ACTUAL NORMALIZED AMPLITUDE -- EXACT CONSUMPTION AND REMAINING BOUNDARY

The actual original amplitude, already derived without a, is
 F(t,v,w,zeta)=alpha(v)alpha(w)alpha(zeta)*sqrt(zeta)
  *psi(sqrt(v*w/zeta)/t)
  *phiHat(sigma*rho*t*sqrt(v*zeta/w)), rho=VB/C<=x^eta,
zero-extended outside the positive orthant. Its support is in the fixed
box [1/16,16]x[1/2,5/2]^3, strictly inside the period64 cube. Here the
alpha support may be chosen compactly inside(1/2,5/2).

For any coordinate, freeze the other three and take that actual slice f.
To consume norm_coeff64_iterated_le one must supply precisely:
  ContDiff Real L f;
  tsupport f subset Ioo(-32,32);
  the actual L-th coordinate derivative bound ML.
The source-only mathematical calculation gives ML<=C_L*x^(L eta).
The theorem above proves the vanishing of EVERY intermediate endpoint
and L actual IBPs from those inputs, rather than postulating them.
The n=0 mode is handled by norm_coeff64_le with its zero-order bound.
Combining |n|>=1 for nonzero integer n with (1+|n|)<=2|n| gives the usual
constant*(1+|n|)^(-L) bound. That last elementary comparison is not needed
by, and has not been hidden inside, the actual IBP proof.

To consume continuous_coeff64_other_slice, bundle the jointly continuous
actual zero extension (or any mixed derivative) as G:C(Real x Y,Complex),
where Y is the remaining compact chart. The output is precisely continuity
of the actual interval Fourier coefficient in that other variable. It is
not a continuity hypothesis on an already unknown c1/c2/c3 coefficient.

Prefer the native multidimensional alternative when continuing: encode F
on EuclideanSpace Real(Fin4), use compact_fourier_weight_bound at r=4L,
and bound every displayed derivative integral on the FIXED support by its
fixed volume times the actual 4L-derivative sup. This preserves x^(4L eta)
without a separate derivative-under-nested-integral argument. The native
AddCircleMulti coefficient integral and inverse are already proved at the
fixed pin; rescale the period64 cube to the unit torus and match its
coefficient to 64^(-4)*(Fourier F)(k/64). This matching and the lattice
weighted-summability specialization remain to be written in Lean.

The ACTUAL zero-extension smoothness and finite derivative seminorm bound
are still source-only mathematics; neither has been supplied as checked
Lean here. Thus actualNormalizedF -> the final mixed-decay hb is still
OPEN formally. The new code genuinely discharges the one-coordinate IBP
and other-slice continuity parts, and exposes an existing stronger native
multidimensional route with the exact derivative-order budget.

With L chosen after J0, eta chosen after L, and only then the Poisson tail
order J, no circular derivative loss occurs. Common I_V and e((km/64)p/V)
are untouched by these lemmas; beta remains a function of(y,z) only.
The original x^(5kappa+o(1)) is not recharged. No compilation or actual
.lean/cache/Git/Sites mutation occurred. Uncompiled bodies require later
typechecking only when the user reauthorizes it. STOP.
-/

end
