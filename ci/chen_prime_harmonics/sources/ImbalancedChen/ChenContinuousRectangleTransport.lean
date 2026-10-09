/-
SPDX-License-Identifier: Apache-2.0

HELD SOURCE CANDIDATE: static review only; no Lean/Lake execution or kernel
verification was available in the preparation environment.

Continuous two-coordinate kernels on the actual compact rectangle are
approximated by finite separated continuous tests. Banach-valued Bernstein
approximation supplies the analytic density step, while the existing genuine
one-prime Mertens adapter supplies every arithmetic limit. No pair-limit,
uniform mass, distribution, or sieve-lower-bound premise is introduced.

The prime selectors, centre masks, inclusive lower/strict upper endpoints,
off-diagonal totient products and artificial square diagonal are literal.
This new module leaves the separately running pair-limit candidate untouched.
-/
import ImbalancedChen.ChenPairHarmonicLimit
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.LocallyConvex

namespace ImbalancedChen.ChenContinuousRectangleTransport

noncomputable section
open Filter Topology
open scoped BigOperators unitInterval
open Classical
open ChenPrimeHarmonicAdapter ChenPairHarmonicLimit

/- These minimal helpers reproduce private arguments from the held pair-limit
module, rather than referring to generated private declaration names. -/

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
      simp [rectangleIntegral]
  | @insert i s hi ih =>
      intro hK hlim
      simp only [Finset.sum_insert hi]
      apply tendsto_primeTensor_add ha hab hc hcd (hK i (by simp))
      · exact continuous_finsetSum s (fun j hj => hK j (by simp [hj]))
      · exact hlim i (by simp)
      · exact ih (fun j hj => hK j (by simp [hj])) (fun j hj => hlim j (by simp [hj]))

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

/-- Uniform finite-separated approximation on a compact rectangle. Only
rectangle continuity is needed: clipping supplies globally continuous
factors without making any assumption about K outside the rectangle.
The approximation index is fixed before the arithmetic limit is taken. -/
theorem exists_separated_near_continuousOn {a b c d : ℝ} {K : ℝ → ℝ → ℝ}
    (hab : a < b) (hcd : c ≤ d)
    (hK : ContinuousOn (Function.uncurry K) (Set.Icc a b ×ˢ Set.Icc c d))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, ∃ f g : Fin (n + 1) → ℝ → ℝ,
      (∀ i, Continuous (f i)) ∧ (∀ i, Continuous (g i)) ∧
      ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc c d,
        |K u v - ∑ i, f i u * g i v| < δ := by
  let e := iccHomeoI a b hab
  let A : C(ℝ, Set.Icc a b) :=
    ⟨fun u => ⟨clip a b u, clip_mem hab.le u⟩,
      (continuous_clip a b).subtype_mk _⟩
  let B : C(ℝ, Set.Icc c d) :=
    ⟨fun v => ⟨clip c d v, clip_mem hcd v⟩,
      (continuous_clip c d).subtype_mk _⟩
  let H : C(I × Set.Icc c d, ℝ) :=
    ⟨fun z => K (e.symm z.1 : ℝ) (z.2 : ℝ),
      hK.comp_continuous
        ((continuous_subtype_val.comp (e.symm.continuous.comp continuous_fst)).prodMk
          (continuous_subtype_val.comp continuous_snd))
        (fun z => ⟨(e.symm z.1).property, z.2.property⟩)⟩
  let G : C(I, C(Set.Icc c d, ℝ)) := H.curry
  obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.mp
    (bernsteinApproximation_uniform G) δ hδ).exists
  have hnorm : ‖bernsteinApproximation n G - G‖ < δ := by
    simpa only [dist_eq_norm] using hn
  let f : Fin (n + 1) → ℝ → ℝ := fun i u => bernstein n i (e (A u))
  let g : Fin (n + 1) → ℝ → ℝ := fun i v => G (bernstein.z i) (B v)
  refine ⟨n, f, g, ?_, ?_, ?_⟩
  · intro i
    exact (bernstein n i).continuous.comp (e.continuous.comp A.continuous)
  · intro i
    exact (G (bernstein.z i)).continuous.comp B.continuous
  · intro u hu v hv
    have hG : G (e (A u)) (B v) = K u v := by
      change K (e.symm (e (A u)) : ℝ) (B v : ℝ) = K u v
      rw [e.symm_apply_apply]
      change K (clip a b u) (clip c d v) = K u v
      rw [clip_eq hu, clip_eq hv]
    have hp : ‖((bernsteinApproximation n G - G) (e (A u))) (B v)‖ < δ :=
      (ContinuousMap.norm_coe_le_norm
        ((bernsteinApproximation n G - G) (e (A u))) (B v)).trans_lt
        ((ContinuousMap.norm_coe_le_norm
          (bernsteinApproximation n G - G) (e (A u))).trans_lt hnorm)
    change ‖(bernsteinApproximation n G (e (A u))) (B v) -
      G (e (A u)) (B v)‖ < δ at hp
    rw [bernsteinApproximation.apply] at hp
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul, hG, Real.norm_eq_abs] at hp
    rw [abs_sub_comm] at hp
    exact hp

/-- Genuine two-coordinate continuous-test convergence for the two actual
prime bands. The arithmetic input is discharged by the one-prime supplier
inside the finite-separated proof. There is no target-limit hypothesis. -/
theorem tendsto_chenPrimeTensor_continuous {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hc : 0 < c) (hcd : c < d) (hd : d ≤ 1)
    {K : ℝ → ℝ → ℝ}
    (hK : ContinuousOn (Function.uncurry K) (Set.Icc a b ×ˢ Set.Icc c d)) :
    Tendsto (primeTensor K a b c d) atTop
      (𝓝 (rectangleIntegral K a b c d)) := by
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
  obtain ⟨n, f, g, hf, hg, happrox⟩ :=
    exists_separated_near_continuousOn hab hcd.le hK δ hδ
  let L : ℝ → ℝ → ℝ := fun u v => ∑ i : Fin (n + 1), f i u * g i v
  have hLK : Continuous (Function.uncurry L) :=
    continuous_finsetSum Finset.univ (fun i _ =>
      ((hf i).comp continuous_fst).mul ((hg i).comp continuous_snd))
  have hclose : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc c d, |K u v - L u v| ≤ δ :=
    fun u hu v hv => (happrox u hu v hv).le
  have hLlim : Tendsto (primeTensor L a b c d) atTop
      (𝓝 (rectangleIntegral L a b c d)) := by
    apply tendsto_primeTensor_finsetSum (Finset.univ : Finset (Fin (n + 1)))
      ha hab hc hcd (fun i u v => f i u * g i v)
    · intro i _
      exact ((hf i).comp continuous_fst).mul ((hg i).comp continuous_snd)
    · intro i _
      exact tendsto_primeTensor_separated ha hab hb hc hcd hd (hf i) (hg i)
  have hint : |rectangleIntegral K a b c d - rectangleIntegral L a b c d| ≤ ε / 3 := by
    calc
      _ ≤ δ * J := rectangleIntegral_sub_le (K := K) (L := L)
        ha hab.le hc hcd.le hδ.le hK hLK.continuousOn hclose
      _ ≤ δ * R := mul_le_mul_of_nonneg_left (le_max_right _ _) hδ.le
      _ = ε / 3 := hδR
  filter_upwards [hmassBound, eventually_ge_atTop (2 : ℕ),
    Metric.tendsto_nhds.mp hLlim (ε / 3) (by positivity)] with N hmassN hN hsep
  rw [Real.dist_eq] at hsep ⊢
  have hsum : |primeTensor K a b c d N - primeTensor L a b c d N| < ε / 3 := by
    calc
      _ ≤ δ * primeTensor (fun _ _ => 1) a b c d N :=
        primeTensor_sub_le hN hδ.le hclose
      _ < δ * M := mul_lt_mul_of_pos_left hmassN hδ
      _ ≤ δ * R := mul_le_mul_of_nonneg_left (le_max_left _ _) hδ.le
      _ = ε / 3 := hδR
  have htri1 := abs_sub_le
    (primeTensor K a b c d N) (primeTensor L a b c d N) (rectangleIntegral K a b c d)
  have htri2 := abs_sub_le
    (primeTensor L a b c d N) (rectangleIntegral L a b c d) (rectangleIntegral K a b c d)
  rw [abs_sub_comm (rectangleIntegral L a b c d)] at htri2
  linarith

/-- Finite sixth-selector identity for an arbitrary two-prime numerator.
The disjoint half-open bands force distinct labels before using totients. -/
theorem chenY6_kernel_totient_sum_eq_tensor (N : ℕ) (A H D : ℝ) (W : ℕ → ℕ → ℝ) :
    (∑ t ∈ chenY6PrimeSelector N A H D,
      W t.1 t.2 / (Nat.totient (t.1 * t.2) : ℝ)) =
      ∑ p ∈ chenSinglePrimeSelector N A H, ∑ q ∈ chenSinglePrimeSelector N H D,
        W p q / (((p : ℝ) - 1) * ((q : ℝ) - 1)) := by
  rw [chenY6PrimeSelector_eq_single_product, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  have hpprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1
  have hqprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hq).1).2.1
  rw [chen_prime_pair_totient_cast hpprime hqprime (chenY6_single_product_lt hp hq).ne]

/-- Finite fifth-selector identity for any symmetric numerator on its
actual masked prime band. The diagonal denominator is exactly (p-1)^2. -/
theorem chenY5_kernel_totient_sum_eq_half_square_sub_diagonal
    (N : ℕ) (A H : ℝ) (W : ℕ → ℕ → ℝ)
    (hW : ∀ p ∈ chenSinglePrimeSelector N A H,
      ∀ q ∈ chenSinglePrimeSelector N A H, W p q = W q p) :
    (∑ t ∈ chenY5PrimeSelector N A H,
      W t.1 t.2 / (Nat.totient (t.1 * t.2) : ℝ)) =
      (1 / 2 : ℝ) *
        ((∑ p ∈ chenSinglePrimeSelector N A H, ∑ q ∈ chenSinglePrimeSelector N A H,
          W p q / (((p : ℝ) - 1) * ((q : ℝ) - 1))) -
          ∑ p ∈ chenSinglePrimeSelector N A H, W p p / ((p : ℝ) - 1) ^ 2) := by
  rw [chenY5PrimeSelector_eq_single_square_filter]
  have hterms :
      (∑ t ∈ (chenSinglePrimeSelector N A H ×ˢ
          chenSinglePrimeSelector N A H).filter (fun t => t.1 < t.2),
        W t.1 t.2 / (Nat.totient (t.1 * t.2) : ℝ)) =
      ∑ t ∈ (chenSinglePrimeSelector N A H ×ˢ
          chenSinglePrimeSelector N A H).filter (fun t => t.1 < t.2),
        W t.1 t.2 / (((t.1 : ℝ) - 1) * ((t.2 : ℝ) - 1)) := by
    apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨htS, hlt⟩ := Finset.mem_filter.mp ht
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp htS
    have hpprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1
    have hqprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hq).1).2.1
    rw [chen_prime_pair_totient_cast hpprime hqprime hlt.ne]
  rw [hterms]
  simpa only [pow_two] using
    chen_ordered_half_square (chenSinglePrimeSelector N A H)
      (fun p q => W p q / (((p : ℝ) - 1) * ((q : ℝ) - 1)))
      (fun p hp q hq => by rw [hW p hp q hq, mul_comm ((p : ℝ) - 1)])

/-- A general compact-continuous diagonal is an instance of the existing
public sum-test diagonal theorem. No fresh tail/distribution hypothesis. -/
theorem tendsto_chenPrimeTensor_continuous_diagonal {a b : ℝ} (ha : 0 < a)
    {K : ℝ → ℝ → ℝ}
    (hK : ContinuousOn (Function.uncurry K) (Set.Icc a b ×ˢ Set.Icc a b)) :
    Tendsto (fun N : ℕ =>
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
        K (Real.log (p : ℝ) / Real.log (N : ℝ))
          (Real.log (p : ℝ) / Real.log (N : ℝ)) / ((p : ℝ) - 1) ^ 2)
      atTop (𝓝 0) := by
  have hF : ContinuousOn (fun s : ℝ => K (s / 2) (s / 2))
      (Set.Icc (2 * a) (2 * b)) := by
    apply hK.comp ((continuous_id.div_const 2).prodMk
      (continuous_id.div_const 2)).continuousOn
    intro s hs
    have hx : s / 2 ∈ Set.Icc a b := by
      constructor <;> linarith [hs.1, hs.2]
    exact ⟨hx, hx⟩
  have htwo (x : ℝ) : 2 * x / 2 = x := by ring
  simpa only [htwo] using (tendsto_chenPrimeTensor_diagonal ha hF)

/-- The sixth harmonic main sum for an arbitrary continuous rectangle
kernel. No symmetry and no global continuity of K are required. -/
theorem tendsto_chenY6_kernel_totient_sum {a h d : ℝ}
    (ha : 0 < a) (hah : a < h) (hhd : h < d) (hd : d ≤ 1)
    {K : ℝ → ℝ → ℝ}
    (hK : ContinuousOn (Function.uncurry K) (Set.Icc a h ×ˢ Set.Icc h d)) :
    Tendsto (fun N : ℕ =>
      ∑ t ∈ chenY6PrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ h) ((N : ℝ) ^ d),
        K (Real.log (t.1 : ℝ) / Real.log (N : ℝ))
          (Real.log (t.2 : ℝ) / Real.log (N : ℝ)) /
            (Nat.totient (t.1 * t.2) : ℝ)) atTop
      (𝓝 (∫ u in a..h, ∫ v in h..d, K u v / (u * v))) := by
  apply (tendsto_chenPrimeTensor_continuous ha hah (hhd.le.trans hd)
    (ha.trans hah) hhd hd hK).congr'
  exact Filter.Eventually.of_forall (fun N =>
    (chenY6_kernel_totient_sum_eq_tensor N ((N : ℝ) ^ a) ((N : ℝ) ^ h)
      ((N : ℝ) ^ d) (fun p q => K (Real.log (p : ℝ) / Real.log (N : ℝ))
        (Real.log (q : ℝ) / Real.log (N : ℝ)))).symm)

/-- The fifth harmonic main sum is exactly one half of the full square
integral. Symmetry is required only on that square; the actual prime
diagonal is proved to vanish rather than dropped from the finite sum. -/
theorem tendsto_chenY5_kernel_totient_sum {a h : ℝ}
    (ha : 0 < a) (hah : a < h) (hh : h ≤ 1)
    {K : ℝ → ℝ → ℝ}
    (hK : ContinuousOn (Function.uncurry K) (Set.Icc a h ×ˢ Set.Icc a h))
    (hSymm : ∀ u ∈ Set.Icc a h, ∀ v ∈ Set.Icc a h, K u v = K v u) :
    Tendsto (fun N : ℕ =>
      ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ h),
        K (Real.log (t.1 : ℝ) / Real.log (N : ℝ))
          (Real.log (t.2 : ℝ) / Real.log (N : ℝ)) /
            (Nat.totient (t.1 * t.2) : ℝ)) atTop
      (𝓝 ((1 / 2 : ℝ) * (∫ u in a..h, ∫ v in a..h, K u v / (u * v)))) := by
  have hlim := ((tendsto_chenPrimeTensor_continuous ha hah hh ha hah hh hK).sub
    (tendsto_chenPrimeTensor_continuous_diagonal ha hK)).const_mul (1 / 2 : ℝ)
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (chenY5_kernel_totient_sum_eq_half_square_sub_diagonal N
    ((N : ℝ) ^ a) ((N : ℝ) ^ h)
    (fun p q => K (Real.log (p : ℝ) / Real.log (N : ℝ))
      (Real.log (q : ℝ) / Real.log (N : ℝ)))
    (fun p hp q hq => hSymm _ (selected_log_coordinate hN hp)
      _ (selected_log_coordinate hN hq))).symm

/-- Sixth-term manuscript endpoints, preserving the actual disjoint bands. -/
theorem tendsto_chenY6_manuscript_kernel_totient_sum {K : ℝ → ℝ → ℝ}
    (hK : ContinuousOn (Function.uncurry K)
      (Set.Icc (100 / 1149 : ℝ) (50 / 309 : ℝ) ×ˢ
        Set.Icc (50 / 309 : ℝ) (183 / 766 : ℝ))) :
    Tendsto (fun N : ℕ =>
      ∑ t ∈ chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ (50 / 309 : ℝ)) ((N : ℝ) ^ (183 / 766 : ℝ)),
        K (Real.log (t.1 : ℝ) / Real.log (N : ℝ))
          (Real.log (t.2 : ℝ) / Real.log (N : ℝ)) /
            (Nat.totient (t.1 * t.2) : ℝ)) atTop
      (𝓝 (∫ u in (100 / 1149 : ℝ)..(50 / 309 : ℝ),
        ∫ v in (50 / 309 : ℝ)..(183 / 766 : ℝ), K u v / (u * v))) :=
  tendsto_chenY6_kernel_totient_sum (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hK

/-- Fifth-term manuscript endpoints with only compact-square symmetry. -/
theorem tendsto_chenY5_manuscript_kernel_totient_sum {K : ℝ → ℝ → ℝ}
    (hK : ContinuousOn (Function.uncurry K)
      (Set.Icc (100 / 1149 : ℝ) (50 / 309 : ℝ) ×ˢ
        Set.Icc (100 / 1149 : ℝ) (50 / 309 : ℝ)))
    (hSymm : ∀ u ∈ Set.Icc (100 / 1149 : ℝ) (50 / 309 : ℝ),
      ∀ v ∈ Set.Icc (100 / 1149 : ℝ) (50 / 309 : ℝ), K u v = K v u) :
    Tendsto (fun N : ℕ =>
      ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ (50 / 309 : ℝ)),
        K (Real.log (t.1 : ℝ) / Real.log (N : ℝ))
          (Real.log (t.2 : ℝ) / Real.log (N : ℝ)) /
            (Nat.totient (t.1 * t.2) : ℝ)) atTop
      (𝓝 ((1 / 2 : ℝ) * (∫ u in (100 / 1149 : ℝ)..(50 / 309 : ℝ),
        ∫ v in (100 / 1149 : ℝ)..(50 / 309 : ℝ), K u v / (u * v)))) :=
  tendsto_chenY5_kernel_totient_sum (by norm_num) (by norm_num) (by norm_num) hK hSymm

end
end ImbalancedChen.ChenContinuousRectangleTransport
