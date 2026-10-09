/-
SPDX-License-Identifier: Apache-2.0

HELD SOURCE CANDIDATE. No Lean/Lake execution or kernel verification has
been performed. The only foreign arithmetic supplier is the approved
66-module Mertens closure consumed by ChenPrimeHarmonicAdapter.

Continuous tests of the sum of two logarithmic coordinates are approximated
on one fixed compact interval by polynomials. Each polynomial is expanded
by the finite binomial theorem into separated tests of the two actual
masked prime measures. Thus no pair-limit premise occurs in the final
arithmetic theorems. The fifth selector retains its factor one half and
its artificial (p-1)^2 diagonal; no phi(p^2) identity is used.
-/
import ImbalancedChen.ChenPrimeHarmonicAdapter
import ImbalancedChen.ChenPairHarmonicFinite
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Data.Nat.Choose.Sum

namespace ImbalancedChen.ChenPairHarmonicLimit

noncomputable section
open Filter Topology
open scoped BigOperators
open Classical
open ChenPrimeHarmonicAdapter

/-- The tensor of the two literal half-open, centre-masked prime bands. -/
def primeTensor (K : ℝ → ℝ → ℝ) (a b c d : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
    ∑ q ∈ chenSinglePrimeSelector N ((N : ℝ) ^ c) ((N : ℝ) ^ d),
      K (Real.log (p : ℝ) / Real.log (N : ℝ))
        (Real.log (q : ℝ) / Real.log (N : ℝ)) /
          (((p : ℝ) - 1) * ((q : ℝ) - 1))

/-- Fixed-rectangle limiting measure, with its two positive densities. -/
def rectangleIntegral (K : ℝ → ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  ∫ u in a..b, ∫ v in c..d, K u v / (u * v)

private def clip (a b x : ℝ) : ℝ := max a (min b x)

private theorem continuous_clip (a b : ℝ) : Continuous (clip a b) :=
  continuous_const.max (continuous_const.min continuous_id)

private theorem clip_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    clip a b x ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

private theorem clip_eq {a b x : ℝ} (hx : x ∈ Set.Icc a b) : clip a b x = x := by
  simp only [clip, min_eq_right hx.2, max_eq_right hx.1]

private theorem rectangle_slice_continuous {a b c d : ℝ} {K : ℝ → ℝ → ℝ}
    (hc : 0 < c)
    (hK : ContinuousOn (Function.uncurry K) (Set.Icc a b ×ˢ Set.Icc c d))
    {u : ℝ} (hu : u ∈ Set.Icc a b) :
    ContinuousOn (fun v => K u v / (u * v)) (Set.Icc c d) := by
  have hk : ContinuousOn (fun v => K u v) (Set.Icc c d) :=
    hK.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨hu, hv⟩)
  -- The constant u may be zero; division by that constant is continuous.
  have hv : ContinuousOn (fun v : ℝ => K u v / v) (Set.Icc c d) :=
    hk.div continuousOn_id (fun v hv => ne_of_gt (hc.trans_le hv.1))
  simpa only [div_div, mul_comm] using hv.div_const u

/-- Parameter continuity is established from compact rectangle continuity,
using a continuous clipped extension. No global continuity of K is assumed. -/
private theorem rectangle_inner_continuous {a b c d : ℝ} {K : ℝ → ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (hK : ContinuousOn (Function.uncurry K) (Set.Icc a b ×ˢ Set.Icc c d)) :
    ContinuousOn (fun u => ∫ v in c..d, K u v / (u * v)) (Set.Icc a b) := by
  let E : ℝ → ℝ → ℝ := fun u v =>
    K (clip a b u) (clip c d v) / (clip a b u * clip c d v)
  have hnum : Continuous (fun z : ℝ × ℝ => K (clip a b z.1) (clip c d z.2)) := by
    apply continuousOn_univ.mp
    exact hK.comp
      (((continuous_clip a b).comp continuous_fst).prodMk
        ((continuous_clip c d).comp continuous_snd)).continuousOn
      (fun z _ => ⟨clip_mem hab z.1, clip_mem hcd z.2⟩)
  have hE : Continuous (Function.uncurry E) := by
    apply hnum.div
      (((continuous_clip a b).comp continuous_fst).mul
        ((continuous_clip c d).comp continuous_snd))
    intro z
    exact mul_ne_zero (ne_of_gt (ha.trans_le (clip_mem hab z.1).1))
      (ne_of_gt (hc.trans_le (clip_mem hcd z.2).1))
  have hcont : Continuous (fun u => ∫ v in c..d, E u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hE c d
  apply hcont.continuousOn.congr
  intro u hu
  apply intervalIntegral.integral_congr
  intro v hv
  rw [Set.uIcc_of_le hcd] at hv
  simp only [E, clip_eq hu, clip_eq hv]

private theorem rectangleIntegral_add {a b c d : ℝ} {K L : ℝ → ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (hK : ContinuousOn (Function.uncurry K) (Set.Icc a b ×ˢ Set.Icc c d))
    (hL : ContinuousOn (Function.uncurry L) (Set.Icc a b ×ˢ Set.Icc c d)) :
    rectangleIntegral (fun u v => K u v + L u v) a b c d =
      rectangleIntegral K a b c d + rectangleIntegral L a b c d := by
  unfold rectangleIntegral
  rw [← intervalIntegral.integral_add
    ((rectangle_inner_continuous ha hab hc hcd hK).intervalIntegrable_of_Icc hab)
    ((rectangle_inner_continuous ha hab hc hcd hL).intervalIntegrable_of_Icc hab)]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hab] at hu
  simp only [add_div]
  exact intervalIntegral.integral_add
    ((rectangle_slice_continuous hc hK hu).intervalIntegrable_of_Icc hcd)
    ((rectangle_slice_continuous hc hL hu).intervalIntegrable_of_Icc hcd)

private theorem rectangleIntegral_sub {a b c d : ℝ} {K L : ℝ → ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (hK : ContinuousOn (Function.uncurry K) (Set.Icc a b ×ˢ Set.Icc c d))
    (hL : ContinuousOn (Function.uncurry L) (Set.Icc a b ×ˢ Set.Icc c d)) :
    rectangleIntegral (fun u v => K u v - L u v) a b c d =
      rectangleIntegral K a b c d - rectangleIntegral L a b c d := by
  unfold rectangleIntegral
  rw [← intervalIntegral.integral_sub
    ((rectangle_inner_continuous ha hab hc hcd hK).intervalIntegrable_of_Icc hab)
    ((rectangle_inner_continuous ha hab hc hcd hL).intervalIntegrable_of_Icc hab)]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hab] at hu
  simp only [sub_div]
  exact intervalIntegral.integral_sub
    ((rectangle_slice_continuous hc hK hu).intervalIntegrable_of_Icc hcd)
    ((rectangle_slice_continuous hc hL hu).intervalIntegrable_of_Icc hcd)

/-- Uniform approximation in the numerator controls the entire iterated
integral. Positivity of u*v is explicit; F itself may have either sign. -/
private theorem rectangleIntegral_sub_le {a b c d δ : ℝ} {K L : ℝ → ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) (hδ : 0 ≤ δ)
    (hK : ContinuousOn (Function.uncurry K) (Set.Icc a b ×ˢ Set.Icc c d))
    (hL : ContinuousOn (Function.uncurry L) (Set.Icc a b ×ˢ Set.Icc c d))
    (hclose : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc c d, |K u v - L u v| ≤ δ) :
    |rectangleIntegral K a b c d - rectangleIntegral L a b c d| ≤
      δ * ((b - a) * (d - c) / (a * c)) := by
  rw [← rectangleIntegral_sub ha hab hc hcd hK hL]
  have hpoint (u : ℝ) (hu : u ∈ Set.Icc a b) (v : ℝ) (hv : v ∈ Set.Icc c d) :
      ‖(K u v - L u v) / (u * v)‖ ≤ δ / (a * c) := by
    have hu0 : 0 < u := ha.trans_le hu.1
    have hv0 : 0 < v := hc.trans_le hv.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hu0 hv0)]
    exact (div_le_div_of_nonneg_right (hclose u hu v hv) (mul_pos hu0 hv0).le).trans
      (div_le_div_of_nonneg_left hδ (mul_pos ha hc)
        (mul_le_mul hu.1 hv.1 hc.le hu0.le))
  have hinner (u : ℝ) (hu : u ∈ Set.Icc a b) :
      ‖∫ v in c..d, (K u v - L u v) / (u * v)‖ ≤ δ / (a * c) * (d - c) := by
    simpa only [abs_of_nonneg (sub_nonneg.mpr hcd)] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := c) (b := d) (C := δ / (a * c))
        (f := fun v => (K u v - L u v) / (u * v))
        (fun v hv => hpoint u hu v (by
          rw [Set.uIoc_of_le hcd] at hv
          exact ⟨hv.1.le, hv.2⟩)))
  have hout := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b)
    (fun u hu => hinner u (by
      rw [Set.uIoc_of_le hab] at hu
      exact ⟨hu.1.le, hu.2⟩))
  rw [abs_of_nonneg (sub_nonneg.mpr hab), Real.norm_eq_abs] at hout
  exact hout.trans_eq (by ring)

private theorem rectangleIntegral_separated (a b c d : ℝ) (f g : ℝ → ℝ) :
    rectangleIntegral (fun u v => f u * g v) a b c d =
      (∫ u in a..b, f u / u) * (∫ v in c..d, g v / v) := by
  unfold rectangleIntegral
  have hpoint (u v : ℝ) : (f u * g v) / (u * v) = (f u / u) * (g v / v) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [hpoint, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_mul_const]

private theorem primeTensor_add (K L : ℝ → ℝ → ℝ) (a b c d : ℝ) (N : ℕ) :
    primeTensor (fun u v => K u v + L u v) a b c d N =
      primeTensor K a b c d N + primeTensor L a b c d N := by
  simp only [primeTensor, add_div, Finset.sum_add_distrib]

private theorem primeTensor_separated (a b c d : ℝ) (N : ℕ) (f g : ℝ → ℝ) :
    primeTensor (fun u v => f u * g v) a b c d N =
      chenSinglePrimeHarmonicSum f a b N * chenSinglePrimeHarmonicSum g c d N := by
  exact chen_prime_tensor_separated N ((N : ℝ) ^ a) ((N : ℝ) ^ b)
    ((N : ℝ) ^ c) ((N : ℝ) ^ d)
    (fun p => f (Real.log (p : ℝ) / Real.log (N : ℝ)))
    (fun q => g (Real.log (q : ℝ) / Real.log (N : ℝ)))

private theorem tendsto_primeTensor_separated {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hc : 0 < c) (hcd : c < d) (hd : d ≤ 1)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Tendsto (primeTensor (fun u v => f u * g v) a b c d) atTop
      (𝓝 (rectangleIntegral (fun u v => f u * g v) a b c d)) := by
  rw [rectangleIntegral_separated]
  apply ((tendsto_chenSinglePrimeHarmonicSum ha hab hb hf.continuousOn).mul
    (tendsto_chenSinglePrimeHarmonicSum hc hcd hd hg.continuousOn)).congr'
  exact Filter.Eventually.of_forall (fun N => (primeTensor_separated a b c d N f g).symm)

private theorem tendsto_primeTensor_add {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d)
    {K L : ℝ → ℝ → ℝ}
    (hK : Continuous (Function.uncurry K)) (hL : Continuous (Function.uncurry L))
    (hKL : Tendsto (primeTensor K a b c d) atTop (𝓝 (rectangleIntegral K a b c d)))
    (hLL : Tendsto (primeTensor L a b c d) atTop (𝓝 (rectangleIntegral L a b c d))) :
    Tendsto (primeTensor (fun u v => K u v + L u v) a b c d) atTop
      (𝓝 (rectangleIntegral (fun u v => K u v + L u v) a b c d)) := by
  rw [rectangleIntegral_add ha hab.le hc hcd.le hK.continuousOn hL.continuousOn]
  apply (hKL.add hLL).congr'
  exact Filter.Eventually.of_forall (fun N => (primeTensor_add K L a b c d N).symm)

private theorem tendsto_primeTensor_finsetSum {ι : Type*} (s : Finset ι)
    {a b c d : ℝ} (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d)
    (K : ι → ℝ → ℝ → ℝ)
    (hK : ∀ i ∈ s, Continuous (Function.uncurry (K i)))
    (hlim : ∀ i ∈ s,
      Tendsto (primeTensor (K i) a b c d) atTop (𝓝 (rectangleIntegral (K i) a b c d))) :
    Tendsto (primeTensor (fun u v => ∑ i ∈ s, K i u v) a b c d) atTop
      (𝓝 (rectangleIntegral (fun u v => ∑ i ∈ s, K i u v) a b c d)) := by
  revert hK hlim
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      have hzero : primeTensor (fun _ _ => 0) a b c d = (fun _ : ℕ => 0) := by
        funext N
        simp [primeTensor]
      simp only [Finset.sum_empty, hzero]
      simpa [rectangleIntegral] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | @insert i s hi ih =>
      intro hK hlim
      simp only [Finset.sum_insert hi]
      apply tendsto_primeTensor_add ha hab hc hcd (hK i (by simp))
      · exact continuous_finsetSum s (fun j hj => hK j (by simp [hj]))
      · exact hlim i (by simp)
      · exact ih (fun j hj => hK j (by simp [hj])) (fun j hj => hlim j (by simp [hj]))

/-- The polynomial case is proved by a finite binomial expansion. Every
term is a product of two actual one-prime continuous-test limits. -/
private theorem tendsto_primeTensor_polynomial {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hc : 0 < c) (hcd : c < d) (hd : d ≤ 1) (P : Polynomial ℝ) :
    Tendsto (primeTensor (fun u v => P.eval (u + v)) a b c d) atTop
      (𝓝 (rectangleIntegral (fun u v => P.eval (u + v)) a b c d)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [Polynomial.eval_add]
      exact tendsto_primeTensor_add ha hab hc hcd
        (P.continuous.comp (continuous_fst.add continuous_snd))
        (Q.continuous.comp (continuous_fst.add continuous_snd)) hP hQ
  | monomial k r =>
      simp only [Polynomial.eval_monomial]
      have hbin : (fun u v : ℝ => r * (u + v) ^ k) =
          (fun u v => ∑ i ∈ Finset.range (k + 1),
            (r * (k.choose i : ℝ) * u ^ i) * v ^ (k - i)) := by
        funext u v
        rw [add_pow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hbin]
      apply tendsto_primeTensor_finsetSum _ ha hab hc hcd
      · intro i _
        fun_prop
      · intro i _
        exact tendsto_primeTensor_separated ha hab hb hc hcd hd
          (by fun_prop) (by fun_prop)

private theorem selected_log_coordinate {N p : ℕ} {a b : ℝ}
    (hN : 2 ≤ N)
    (hp : p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ b)) :
    Real.log (p : ℝ) / Real.log (N : ℝ) ∈ Set.Icc a b := by
  obtain ⟨_, hpa, hpb⟩ := Finset.mem_filter.mp hp
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one hN1
  have hp0 : (0 : ℝ) < p := (Real.rpow_pos_of_pos hNpos a).trans_le hpa
  have hlo := Real.log_le_log (Real.rpow_pos_of_pos hNpos a) hpa
  have hhi := Real.log_le_log hp0 hpb.le
  rw [Real.log_rpow hNpos a] at hlo
  rw [Real.log_rpow hNpos b] at hhi
  exact ⟨(le_div_iff₀ (Real.log_pos hN1)).mpr hlo,
    (div_le_iff₀ (Real.log_pos hN1)).mpr hhi⟩

private theorem selected_denominator_pos {N p : ℕ} {A B : ℝ}
    (hp : p ∈ chenSinglePrimeSelector N A B) : 0 < (p : ℝ) - 1 := by
  have hpprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
  linarith

private theorem primeTensor_one_nonneg (a b c d : ℝ) (N : ℕ) :
    0 ≤ primeTensor (fun _ _ => 1) a b c d N := by
  unfold primeTensor
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro q hq
  exact div_nonneg zero_le_one
    (mul_nonneg (selected_denominator_pos hp).le (selected_denominator_pos hq).le)

/-- The finite approximation error is δ times the product mass of the
actual positive one-prime measures. Both moving-centre masks remain. -/
private theorem primeTensor_sub_le {a b c d δ : ℝ} {K L : ℝ → ℝ → ℝ}
    {N : ℕ} (hN : 2 ≤ N) (_hδ : 0 ≤ δ)
    (hclose : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc c d, |K u v - L u v| ≤ δ) :
    |primeTensor K a b c d N - primeTensor L a b c d N| ≤
      δ * primeTensor (fun _ _ => 1) a b c d N := by
  unfold primeTensor
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← sub_div]
  calc
    _ ≤ ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
        |∑ q ∈ chenSinglePrimeSelector N ((N : ℝ) ^ c) ((N : ℝ) ^ d),
          (K (Real.log (p : ℝ) / Real.log (N : ℝ))
                (Real.log (q : ℝ) / Real.log (N : ℝ)) -
            L (Real.log (p : ℝ) / Real.log (N : ℝ))
                (Real.log (q : ℝ) / Real.log (N : ℝ))) /
              (((p : ℝ) - 1) * ((q : ℝ) - 1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
        ∑ q ∈ chenSinglePrimeSelector N ((N : ℝ) ^ c) ((N : ℝ) ^ d),
          δ / (((p : ℝ) - 1) * ((q : ℝ) - 1)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_div, abs_of_pos
        (mul_pos (selected_denominator_pos hp) (selected_denominator_pos hq))]
      exact div_le_div_of_nonneg_right
        (hclose _ (selected_log_coordinate hN hp) _ (selected_log_coordinate hN hq))
        (mul_pos (selected_denominator_pos hp) (selected_denominator_pos hq)).le
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring

/-- Genuine continuous-test rectangle limit for the two actual prime
measures. The only analytic hypothesis is continuity of the fixed F on
the compact sum interval. The arithmetic one-prime theorem is invoked
inside the polynomial proof, not passed in as an unproved pair premise. -/
theorem tendsto_chenPrimeTensor_sumTest {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hc : 0 < c) (hcd : c < d) (hd : d ≤ 1)
    {F : ℝ → ℝ} (hF : ContinuousOn F (Set.Icc (a + c) (b + d))) :
    Tendsto (primeTensor (fun u v => F (u + v)) a b c d) atTop
      (𝓝 (∫ u in a..b, ∫ v in c..d, F (u + v) / (u * v))) := by
  have hFK : ContinuousOn (fun z : ℝ × ℝ => F (z.1 + z.2))
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    hF.comp (continuous_fst.add continuous_snd).continuousOn
      (fun z hz => ⟨add_le_add hz.1.1 hz.2.1, add_le_add hz.1.2 hz.2.2⟩)
  have hmass : Tendsto (primeTensor (fun _ _ => 1) a b c d) atTop
      (𝓝 (rectangleIntegral (fun _ _ => 1) a b c d)) := by
    simpa only [one_mul] using
      (tendsto_primeTensor_separated ha hab hb hc hcd hd
        (f := fun _ => 1) (g := fun _ => 1) continuous_const continuous_const)
  let M : ℝ := |rectangleIntegral (fun _ _ => 1) a b c d| + 1
  let J : ℝ := (b - a) * (d - c) / (a * c)
  let R : ℝ := max M J
  have hM : 0 < M := by dsimp [M]; positivity
  have hR : 0 < R := hM.trans_le (le_max_left _ _)
  have hmassBound : ∀ᶠ N : ℕ in atTop, primeTensor (fun _ _ => 1) a b c d N < M := by
    filter_upwards [Metric.tendsto_nhds.mp hmass 1 zero_lt_one] with N hN
    rw [Real.dist_eq, abs_lt] at hN
    dsimp [M]
    linarith [le_abs_self (rectangleIntegral (fun _ _ => 1) a b c d)]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / (3 * R)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδR : δ * R = ε / 3 := by
    dsimp [δ]
    rw [← div_div, div_mul_cancel₀ _ hR.ne']
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn
    (a + c) (b + d) F hF δ hδ
  have hclose : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc c d,
      |F (u + v) - P.eval (u + v)| ≤ δ := by
    intro u hu v hv
    rw [abs_sub_comm]
    exact (hP _ ⟨add_le_add hu.1 hv.1, add_le_add hu.2 hv.2⟩).le
  have hPK : Continuous (fun z : ℝ × ℝ => P.eval (z.1 + z.2)) :=
    P.continuous.comp (continuous_fst.add continuous_snd)
  have hint : |rectangleIntegral (fun u v => F (u + v)) a b c d -
      rectangleIntegral (fun u v => P.eval (u + v)) a b c d| ≤ ε / 3 := by
    calc
      _ ≤ δ * J := rectangleIntegral_sub_le
        (K := fun u v => F (u + v)) (L := fun u v => P.eval (u + v))
        ha hab.le hc hcd.le hδ.le
        hFK hPK.continuousOn hclose
      _ ≤ δ * R := mul_le_mul_of_nonneg_left (le_max_right _ _) hδ.le
      _ = ε / 3 := hδR
  filter_upwards [hmassBound, eventually_ge_atTop (2 : ℕ),
    Metric.tendsto_nhds.mp (tendsto_primeTensor_polynomial ha hab hb hc hcd hd P)
      (ε / 3) (by positivity)] with N hmassN hN hpoly
  rw [Real.dist_eq] at hpoly ⊢
  have hsum : |primeTensor (fun u v => F (u + v)) a b c d N -
      primeTensor (fun u v => P.eval (u + v)) a b c d N| < ε / 3 := by
    calc
      _ ≤ δ * primeTensor (fun _ _ => 1) a b c d N :=
        primeTensor_sub_le hN hδ.le hclose
      _ < δ * M := mul_lt_mul_of_pos_left hmassN hδ
      _ ≤ δ * R := mul_le_mul_of_nonneg_left (le_max_left _ _) hδ.le
      _ = ε / 3 := hδR
  have htri1 := abs_sub_le
    (primeTensor (fun u v => F (u + v)) a b c d N)
    (primeTensor (fun u v => P.eval (u + v)) a b c d N)
    (rectangleIntegral (fun u v => F (u + v)) a b c d)
  have htri2 := abs_sub_le
    (primeTensor (fun u v => P.eval (u + v)) a b c d N)
    (rectangleIntegral (fun u v => P.eval (u + v)) a b c d)
    (rectangleIntegral (fun u v => F (u + v)) a b c d)
  rw [abs_sub_comm (rectangleIntegral (fun u v => P.eval (u + v)) a b c d)] at htri2
  change |primeTensor (fun u v => F (u + v)) a b c d N -
    rectangleIntegral (fun u v => F (u + v)) a b c d| < ε
  linarith

/-- The artificial diagonal introduced by tensoring one masked prime band
vanishes. Its denominator is (p-1)^2, never phi(p^2). -/
theorem tendsto_chenPrimeTensor_diagonal {a b : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF : ContinuousOn F (Set.Icc (2 * a) (2 * b))) :
    Tendsto (fun N : ℕ =>
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
        F (2 * (Real.log (p : ℝ) / Real.log (N : ℝ))) / ((p : ℝ) - 1) ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound : ∀ x ∈ Set.Icc (2 * a) (2 * b), |F x| ≤ M := by
    intro x hx
    have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  have hdecay : Tendsto (fun N : ℕ => 8 * M / (N : ℝ) ^ a) atTop (𝓝 0) := by
    simpa only [pow_zero, mul_zero, mul_one_div] using
      (tendsto_nat_log_pow_div_rpow 0 ha).const_mul (8 * M)
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hdecay.eventually (gt_mem_nhds hε),
    hpower.eventually (eventually_ge_atTop (2 : ℝ)), eventually_ge_atTop (2 : ℕ)]
    with N he hA hN
  rw [Real.dist_eq, sub_zero]
  apply lt_of_le_of_lt _ he
  apply chen_pair_diagonal_tail_bound N
    (chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ b))
    (fun p => F (2 * (Real.log (p : ℝ) / Real.log (N : ℝ)))) hA hM
  · intro p hp
    obtain ⟨hpN, hpA, _⟩ := Finset.mem_filter.mp hp
    exact ⟨hpA, (mem_chenAdditivePrimeCarrier.mp hpN).1.le⟩
  · intro p hp
    have hx := selected_log_coordinate hN hp
    apply hbound
    constructor <;> linarith [hx.1, hx.2]

/-- The actual sixth main sum has the full rectangle integral. The two
half-open bands force p<q, so the true off-diagonal phi(pq) is exact. -/
theorem tendsto_chenY6_log_totient_sum {a h d : ℝ}
    (ha : 0 < a) (hah : a < h) (hhd : h < d) (hd : d ≤ 1)
    {F : ℝ → ℝ} (hF : ContinuousOn F (Set.Icc (a + h) (h + d))) :
    Tendsto (fun N : ℕ =>
      ∑ t ∈ chenY6PrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ h) ((N : ℝ) ^ d),
        F (Real.log ((t.1 * t.2 : ℕ) : ℝ) / Real.log (N : ℝ)) /
          (Nat.totient (t.1 * t.2) : ℝ)) atTop
      (𝓝 (∫ u in a..h, ∫ v in h..d, F (u + v) / (u * v))) := by
  apply (tendsto_chenPrimeTensor_sumTest ha hah (hhd.le.trans hd)
    (ha.trans hah) hhd hd hF).congr'
  exact Filter.Eventually.of_forall (fun N =>
    (chenY6_log_totient_sum_eq_tensor N ((N : ℝ) ^ a) ((N : ℝ) ^ h)
      ((N : ℝ) ^ d) F).symm)

/-- The actual fifth main sum is one half of the square integral. The
strict-order symmetry and the vanishing diagonal are both discharged. -/
theorem tendsto_chenY5_log_totient_sum {a h : ℝ}
    (ha : 0 < a) (hah : a < h) (hh : h ≤ 1)
    {F : ℝ → ℝ} (hF : ContinuousOn F (Set.Icc (2 * a) (2 * h))) :
    Tendsto (fun N : ℕ =>
      ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ h),
        F (Real.log ((t.1 * t.2 : ℕ) : ℝ) / Real.log (N : ℝ)) /
          (Nat.totient (t.1 * t.2) : ℝ)) atTop
      (𝓝 ((1 / 2 : ℝ) * (∫ u in a..h, ∫ v in a..h, F (u + v) / (u * v)))) := by
  have hF' : ContinuousOn F (Set.Icc (a + a) (h + h)) := by
    simpa only [two_mul] using hF
  have hlim := ((tendsto_chenPrimeTensor_sumTest ha hah hh ha hah hh hF').sub
    (tendsto_chenPrimeTensor_diagonal ha hF)).const_mul (1 / 2 : ℝ)
  simp only [sub_zero] at hlim
  apply hlim.congr'
  exact Filter.Eventually.of_forall (fun N =>
    (chenY5_log_totient_sum_eq_half_square_sub_diagonal N ((N : ℝ) ^ a)
      ((N : ℝ) ^ h) F).symm)

/-- Upsilon 6's manuscript exponents, with no analytic premise besides
continuity of the fixed coefficient on its actual compact sum interval. -/
theorem tendsto_chenY6_manuscript_log_totient_sum {F : ℝ → ℝ}
    (hF : ContinuousOn F
      (Set.Icc ((100 / 1149 : ℝ) + 50 / 309) ((50 / 309 : ℝ) + 183 / 766))) :
    Tendsto (fun N : ℕ =>
      ∑ t ∈ chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ (50 / 309 : ℝ)) ((N : ℝ) ^ (183 / 766 : ℝ)),
        F (Real.log ((t.1 * t.2 : ℕ) : ℝ) / Real.log (N : ℝ)) /
          (Nat.totient (t.1 * t.2) : ℝ)) atTop
      (𝓝 (∫ u in (100 / 1149 : ℝ)..(50 / 309 : ℝ),
        ∫ v in (50 / 309 : ℝ)..(183 / 766 : ℝ), F (u + v) / (u * v))) :=
  tendsto_chenY6_log_totient_sum (by norm_num) (by norm_num) (by norm_num) (by norm_num) hF

/-- Upsilon 5's manuscript exponents. The factor one half is retained in
the exact half-square representation of the symmetric triangular limit. -/
theorem tendsto_chenY5_manuscript_log_totient_sum {F : ℝ → ℝ}
    (hF : ContinuousOn F (Set.Icc (2 * (100 / 1149 : ℝ)) (2 * (50 / 309 : ℝ)))) :
    Tendsto (fun N : ℕ =>
      ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ (50 / 309 : ℝ)),
        F (Real.log ((t.1 * t.2 : ℕ) : ℝ) / Real.log (N : ℝ)) /
          (Nat.totient (t.1 * t.2) : ℝ)) atTop
      (𝓝 ((1 / 2 : ℝ) * (∫ u in (100 / 1149 : ℝ)..(50 / 309 : ℝ),
        ∫ v in (100 / 1149 : ℝ)..(50 / 309 : ℝ), F (u + v) / (u * v)))) :=
  tendsto_chenY5_log_totient_sum (by norm_num) (by norm_num) (by norm_num) hF

end
end ImbalancedChen.ChenPairHarmonicLimit
