import ImbalancedChen.P2HistoricalFibreBinding
import ImbalancedChen.P2PairedFibreBuchstabVariableLower
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# P2: affine reduction of the literal inner Buchstab fibre

SOURCE ONLY; uncompiled.  The first two imports refer to the sibling
drafts under their proposed installation paths.  No compiler, producer,
runtime, replay, audit, or numerical evaluation is part of this delivery.

This is the adjacent four-to-three iterated-integral dictionary.  For
`S = 1-t-u-z`, the substitution is `w = S-z*s`; its reversed endpoints
are `(S-z)/z` and `(S-a)/z`.  The reciprocal `1/w` and the positive
absolute Jacobian `z` give exactly `z/(S-z*s)`.  The function integrated
here is the actual pinned Buchstab function minus its original half
baseline.  The coefficient is precisely `(K/4)/(t*u*z^2)`.

Continuity and interval integrability are proved, including every closed
endpoint and the zero-width fibre `a=z`.  Continuous clamped extensions
pay the successive outer integrability obligations.  The main equality
has no gain, integrability, or integral-identity hypothesis.  Nothing in
this file identifies the historical five-coordinate sieve-profile
integral with this paired four-coordinate integral.
-/

namespace ImbalancedChen.Certificates.P2BuchstabFibreAffineReduction

noncomputable section

open MeasureTheory Set
open scoped Interval BigOperators
open P2HistoricalFibreBinding

def residual (t u z : ℝ) : ℝ := 1 - t - u - z

def lower (t u z : ℝ) : ℝ := (residual t u z - z) / z

def upper (a t u z : ℝ) : ℝ := (residual t u z - a) / z

def coefficient (K t u z : ℝ) : ℝ := (K / 4) / (t * u * z ^ 2)

/-- The Jacobian is positive on the entire transformed closed interval. -/
def jacobian (t u z s : ℝ) : ℝ := z / (residual t u z - z * s)

/-- The actual pinned semantic gain, now at the independent variable `s`. -/
def gain (s : ℝ) : ℝ := LiLiuPrereqBuchstab.buchstab s - (1 : ℝ) / 2

def semanticKernel (K t u z w : ℝ) : ℝ :=
  pairedChenQuarterWeight K t u z w * pairedSemanticBuchstabGain t u z w

def semanticInner (a K t u z : ℝ) : ℝ :=
  ∫ w in a..z, semanticKernel K t u z w

def transformedFibre (a t u z : ℝ) : ℝ :=
  ∫ s in lower t u z..upper a t u z, jacobian t u z s * gain s

def reducedInner (a K t u z : ℝ) : ℝ :=
  coefficient K t u z * transformedFibre a t u z

theorem endpoints_order {a t u z : ℝ} (hz : 0 < z) (haz : a ≤ z) :
    lower t u z ≤ upper a t u z := by
  have hdiff : upper a t u z - lower t u z = (z - a) / z := by
    unfold upper lower
    ring
  have hnonneg : 0 ≤ (z - a) / z := div_nonneg (sub_nonneg.mpr haz) hz.le
  linarith

theorem recover_endpoints {a t u z : ℝ} (hz : z ≠ 0) :
    residual t u z - z * upper a t u z = a ∧
    residual t u z - z * lower t u z = z := by
  constructor <;> simp only [upper, lower] <;> field_simp [hz] <;> ring

theorem endpoint_width (a t u z : ℝ) :
    upper a t u z - lower t u z = (z - a) / z := by
  unfold upper lower
  ring

theorem inverse_forward {t u z w : ℝ} (hz : z ≠ 0) :
    residual t u z - z * ((residual t u z - w) / z) = w := by
  field_simp [hz]
  ring

theorem forward_inverse {t u z s : ℝ} (hz : z ≠ 0) :
    (residual t u z - (residual t u z - z * s)) / z = s := by
  field_simp [hz]
  ring

/-- The inverse affine map sends the whole closed transformed interval
to the whole original closed fibre. -/
theorem recover_mem {a t u z s : ℝ} (hz : 0 < z)
    (hs : s ∈ Icc (lower t u z) (upper a t u z)) :
    residual t u z - z * s ∈ Icc a z := by
  have hlo : residual t u z - z ≤ s * z :=
    (div_le_iff₀ hz).mp hs.1
  have hhi : s * z ≤ residual t u z - a :=
    (le_div_iff₀ hz).mp hs.2
  constructor <;> nlinarith

theorem forward_mem {a t u z w : ℝ} (hz : 0 < z)
    (hw : w ∈ Icc a z) :
    (residual t u z - w) / z ∈ Icc (lower t u z) (upper a t u z) := by
  have hl : lower t u z ≤ (residual t u z - w) / z := by
    unfold lower
    apply (div_le_div_iff₀ hz hz).mpr
    nlinarith [hw.2]
  have hu : (residual t u z - w) / z ≤ upper a t u z := by
    unfold upper
    apply (div_le_div_iff₀ hz hz).mpr
    nlinarith [hw.1]
  exact ⟨hl, hu⟩

theorem denominator_pos {a t u z s : ℝ} (ha : 0 < a) (haz : a ≤ z)
    (hs : s ∈ Icc (lower t u z) (upper a t u z)) :
    0 < residual t u z - z * s :=
  ha.trans_le (recover_mem (ha.trans_le haz) hs).1

theorem jacobian_pos {a t u z s : ℝ} (ha : 0 < a) (haz : a ≤ z)
    (hs : s ∈ Icc (lower t u z) (upper a t u z)) :
    0 < jacobian t u z s :=
  div_pos (ha.trans_le haz) (denominator_pos ha haz hs)

theorem argument_recovered (t u z s : ℝ) (hz : z ≠ 0) :
    (1 - t - u - z - (residual t u z - z * s)) / z = s := by
  unfold residual
  field_simp [hz]
  ring

/-- Actual Buchstab continuity, with the denominator proved nonzero at
every transformed endpoint as well as in the interior. -/
theorem continuousOn_transformed {a t u z : ℝ} (ha : 0 < a) (haz : a ≤ z) :
    ContinuousOn (fun s => jacobian t u z s * gain s)
      (uIcc (lower t u z) (upper a t u z)) := by
  have hc : ContinuousOn (fun s => jacobian t u z s)
      (uIcc (lower t u z) (upper a t u z)) := by
    unfold jacobian
    apply continuousOn_const.div (continuousOn_const.sub
      (continuousOn_const.mul continuousOn_id))
    intro s hs
    rw [uIcc_of_le (endpoints_order (ha.trans_le haz) haz)] at hs
    exact (denominator_pos ha haz hs).ne'
  have hg : Continuous gain := LiLiuPrereqBuchstab.continuous_buchstab.sub continuous_const
  exact hc.mul hg.continuousOn

theorem intervalIntegrable_transformed {a t u z : ℝ} (ha : 0 < a) (haz : a ≤ z) :
    IntervalIntegrable (fun s => jacobian t u z s * gain s) volume
      (lower t u z) (upper a t u z) :=
  (continuousOn_transformed ha haz).intervalIntegrable

theorem continuousOn_semanticKernel {a K t u z : ℝ}
    (ha : 0 < a) (haz : a ≤ z) (ht : 0 < t) (hu : 0 < u) :
    ContinuousOn (semanticKernel K t u z) (uIcc a z) := by
  have hz : 0 < z := ha.trans_le haz
  have hw : ContinuousOn (fun w => pairedChenQuarterWeight K t u z w) (uIcc a z) := by
    unfold pairedChenQuarterWeight
    apply continuousOn_const.div (continuousOn_const.mul continuousOn_id)
    intro w hw
    rw [uIcc_of_le haz] at hw
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero ht.ne' hu.ne')
      (pow_ne_zero 2 hz.ne')) (ha.trans_le hw.1).ne'
  have harg : Continuous (fun w : ℝ => (1 - t - u - z - w) / z) := by fun_prop
  have hg : Continuous (pairedSemanticBuchstabGain t u z) :=
    (LiLiuPrereqBuchstab.continuous_buchstab.comp harg).sub continuous_const
  exact hw.mul hg.continuousOn

theorem intervalIntegrable_semanticKernel {a K t u z : ℝ}
    (ha : 0 < a) (haz : a ≤ z) (ht : 0 < t) (hu : 0 < u) :
    IntervalIntegrable (semanticKernel K t u z) volume a z :=
  (continuousOn_semanticKernel ha haz ht hu).intervalIntegrable

/-- Exact inverse affine substitution for the literal weighted semantic
gain.  The theorem itself also works for vanishing `K`, `t`, or `u`;
separate theorems above establish genuine integrability on positive fibres. -/
theorem semanticInner_eq_reducedInner {a K t u z : ℝ} (hz : z ≠ 0) :
    semanticInner a K t u z = reducedInner a K t u z := by
  have he := recover_endpoints (a := a) (t := t) (u := u) hz
  have hc := intervalIntegral.smul_integral_comp_sub_mul
    (f := semanticKernel K t u z)
    (a := lower t u z) (b := upper a t u z) z (residual t u z)
  rw [he.1, he.2] at hc
  change z * (∫ s in lower t u z..upper a t u z,
    semanticKernel K t u z (residual t u z - z * s)) = semanticInner a K t u z at hc
  calc
    semanticInner a K t u z =
        z * (∫ s in lower t u z..upper a t u z,
          semanticKernel K t u z (residual t u z - z * s)) := hc.symm
    _ = ∫ s in lower t u z..upper a t u z,
          z * semanticKernel K t u z (residual t u z - z * s) :=
      (intervalIntegral.integral_const_mul z _).symm
    _ = ∫ s in lower t u z..upper a t u z,
          coefficient K t u z * (jacobian t u z s * gain s) := by
      apply intervalIntegral.integral_congr
      intro s _hs
      unfold semanticKernel pairedSemanticBuchstabGain
      rw [argument_recovered t u z s hz]
      simp only [pairedChenQuarterWeight, coefficient, jacobian, gain,
        div_eq_mul_inv, mul_inv_rev]
      ring
    _ = reducedInner a K t u z := by
      rw [intervalIntegral.integral_const_mul]
      rfl

theorem zero_width (a K t u : ℝ) :
    semanticInner a K t u a = 0 ∧ reducedInner a K t u a = 0 ∧
      transformedFibre a t u a = 0 := by
  simp [semanticInner, reducedInner, transformedFibre, lower, upper]

/-- The literal fourfold semantic gain in the original paired variables. -/
def fourfoldSemantic (K a tl tr ul ur Z : ℝ) : ℝ :=
  ∫ t in tl..tr, ∫ u in ul..ur, ∫ z in a..Z, ∫ w in a..z,
    pairedChenQuarterWeight K t u z w * pairedSemanticBuchstabGain t u z w

/-- A triple integral whose inner value is a genuine real Buchstab
integral, carrying the exact positive affine Jacobian. -/
def tripleReduced (K a tl tr ul ur Z : ℝ) : ℝ :=
  ∫ t in tl..tr, ∫ u in ul..ur, ∫ z in a..Z,
    coefficient K t u z *
      (∫ s in (1 - t - u - z - z) / z..(1 - t - u - z - a) / z,
        (z / (1 - t - u - z - z * s)) *
          (LiLiuPrereqBuchstab.buchstab s - (1 : ℝ) / 2))

def semanticZ (a K t u Z : ℝ) : ℝ := ∫ z in a..Z, semanticInner a K t u z

def reducedZ (a K t u Z : ℝ) : ℝ := ∫ z in a..Z, reducedInner a K t u z

def semanticUZ (a K t ul ur Z : ℝ) : ℝ := ∫ u in ul..ur, semanticZ a K t u Z

def reducedUZ (a K t ul ur Z : ℝ) : ℝ := ∫ u in ul..ur, reducedZ a K t u Z

theorem semanticZ_eq_reducedZ {a K t u Z : ℝ} (ha : 0 < a) (hAZ : a ≤ Z) :
    semanticZ a K t u Z = reducedZ a K t u Z := by
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hAZ] at hz
  exact semanticInner_eq_reducedInner (ha.trans_le hz.1).ne'

theorem semanticUZ_eq_reducedUZ {a K t ul ur Z : ℝ}
    (ha : 0 < a) (hAZ : a ≤ Z) :
    semanticUZ a K t ul ur Z = reducedUZ a K t ul ur Z := by
  apply intervalIntegral.integral_congr
  intro u _hu
  exact semanticZ_eq_reducedZ ha hAZ

/-- This exact identity does not assume the identity as a premise and
does not replace the actual Buchstab gain by a constant lower barrier. -/
theorem fourfoldSemantic_eq_tripleReduced {K a tl tr ul ur Z : ℝ}
    (ha : 0 < a) (hAZ : a ≤ Z) :
    fourfoldSemantic K a tl tr ul ur Z = tripleReduced K a tl tr ul ur Z := by
  change (∫ t in tl..tr, semanticUZ a K t ul ur Z) =
    ∫ t in tl..tr, reducedUZ a K t ul ur Z
  apply intervalIntegral.integral_congr
  intro t _ht
  exact semanticUZ_eq_reducedUZ ha hAZ

/-! The remaining section pays the successive integrability obligations.
The clamp is used only outside the actual support. -/

private abbrev Quad := ((ℝ × ℝ) × ℝ) × ℝ

private def clip (a x : ℝ) : ℝ := max a x

private def safeKernel (a K : ℝ) (p : Quad) : ℝ :=
  semanticKernel K (clip a p.1.1.1) (clip a p.1.1.2) (clip a p.1.2) (clip a p.2)

private theorem continuous_safeKernel {a : ℝ} (ha : 0 < a) (K : ℝ) :
    Continuous (safeKernel a K) := by
  have hclip : Continuous (clip a) := continuous_const.max continuous_id
  have hn (x : ℝ) : clip a x ≠ 0 := (ha.trans_le (le_max_left a x)).ne'
  have ht : Continuous (fun p : Quad => clip a p.1.1.1) := hclip.comp (by fun_prop)
  have hu : Continuous (fun p : Quad => clip a p.1.1.2) := hclip.comp (by fun_prop)
  have hz : Continuous (fun p : Quad => clip a p.1.2) := hclip.comp (by fun_prop)
  have hw : Continuous (fun p : Quad => clip a p.2) := hclip.comp (by fun_prop)
  have hweight : Continuous (fun p : Quad => pairedChenQuarterWeight K
      (clip a p.1.1.1) (clip a p.1.1.2) (clip a p.1.2) (clip a p.2)) :=
    continuous_const.div (((ht.mul hu).mul (hz.pow 2)).mul hw)
      (fun p => mul_ne_zero (mul_ne_zero (mul_ne_zero (hn _) (hn _))
        (pow_ne_zero 2 (hn _))) (hn _))
  have hgain : Continuous (fun p : Quad => pairedSemanticBuchstabGain
      (clip a p.1.1.1) (clip a p.1.1.2) (clip a p.1.2) (clip a p.2)) :=
    (LiLiuPrereqBuchstab.continuous_buchstab.comp
      (((((continuous_const.sub ht).sub hu).sub hz).sub hw).div hz
        (fun p => hn p.1.2))).sub continuous_const
  exact hweight.mul hgain

private def safeInner (a K : ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  ∫ w in a..p.2, safeKernel a K (p, w)

private def safeZ (a K Z : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ z in a..Z, safeInner a K (p, z)

private def safeUZ (a K ul ur Z t : ℝ) : ℝ :=
  ∫ u in ul..ur, safeZ a K Z (t, u)

private theorem continuous_safeInner {a : ℝ} (ha : 0 < a) (K : ℝ) :
    Continuous (safeInner a K) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun p w => safeKernel a K (p, w)) (continuous_safeKernel ha K) continuous_snd

private theorem continuous_safeZ {a : ℝ} (ha : 0 < a) (K Z : ℝ) :
    Continuous (safeZ a K Z) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun p z => safeInner a K (p, z)) (continuous_safeInner ha K) a Z

private theorem continuous_safeUZ {a : ℝ} (ha : 0 < a) (K ul ur Z : ℝ) :
    Continuous (safeUZ a K ul ur Z) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t u => safeZ a K Z (t, u)) (continuous_safeZ ha K Z) ul ur

private theorem safeInner_eq {a K t u z : ℝ}
    (ht : a ≤ t) (hu : a ≤ u) (hz : a ≤ z) :
    safeInner a K ((t, u), z) = semanticInner a K t u z := by
  apply intervalIntegral.integral_congr
  intro w hw
  rw [uIcc_of_le hz] at hw
  simp only [safeKernel, clip, max_eq_right ht, max_eq_right hu,
    max_eq_right hz, max_eq_right hw.1]

private theorem safeZ_eq {a K t u Z : ℝ}
    (ht : a ≤ t) (hu : a ≤ u) (hAZ : a ≤ Z) :
    safeZ a K Z (t, u) = semanticZ a K t u Z := by
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hAZ] at hz
  exact safeInner_eq ht hu hz.1

private theorem safeUZ_eq {a K t ul ur Z : ℝ}
    (ht : a ≤ t) (hul : a ≤ ul) (hu : ul ≤ ur) (hAZ : a ≤ Z) :
    safeUZ a K ul ur Z t = semanticUZ a K t ul ur Z := by
  apply intervalIntegral.integral_congr
  intro u hu'
  rw [uIcc_of_le hu] at hu'
  exact safeZ_eq ht (hul.trans hu'.1) hAZ

/-- Genuine integrability of both outer `z` integrands. -/
theorem intervalIntegrable_z {a K t u Z : ℝ} (ha : 0 < a)
    (ht : a ≤ t) (hu : a ≤ u) (hAZ : a ≤ Z) :
    IntervalIntegrable (semanticInner a K t u) volume a Z ∧
    IntervalIntegrable (reducedInner a K t u) volume a Z := by
  have hs : IntervalIntegrable (fun z => safeInner a K ((t, u), z)) volume a Z :=
    ((continuous_safeInner ha K).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable a Z
  have ho : IntervalIntegrable (semanticInner a K t u) volume a Z := by
    apply hs.congr
    intro z hz
    rw [uIoc_of_le hAZ] at hz
    exact safeInner_eq ht hu hz.1.le
  refine ⟨ho, ho.congr ?_⟩
  intro z hz
  rw [uIoc_of_le hAZ] at hz
  exact semanticInner_eq_reducedInner (ha.trans hz.1).ne'

/-- Genuine integrability of both outer `u` integrands. -/
theorem intervalIntegrable_u {a K t ul ur Z : ℝ} (ha : 0 < a)
    (ht : a ≤ t) (hul : a ≤ ul) (hu : ul ≤ ur) (hAZ : a ≤ Z) :
    IntervalIntegrable (fun u => semanticZ a K t u Z) volume ul ur ∧
    IntervalIntegrable (fun u => reducedZ a K t u Z) volume ul ur := by
  have hs : IntervalIntegrable (fun u => safeZ a K Z (t, u)) volume ul ur :=
    ((continuous_safeZ ha K Z).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable ul ur
  have ho : IntervalIntegrable (fun u => semanticZ a K t u Z) volume ul ur := by
    apply hs.congr
    intro u hu'
    rw [uIoc_of_le hu] at hu'
    exact safeZ_eq ht (hul.trans hu'.1.le) hAZ
  exact ⟨ho, ho.congr (fun _u _hu => semanticZ_eq_reducedZ ha hAZ)⟩

/-- Genuine integrability of both final outer `t` integrands. -/
theorem intervalIntegrable_t {a K tl tr ul ur Z : ℝ} (ha : 0 < a)
    (htl : a ≤ tl) (ht : tl ≤ tr) (hul : a ≤ ul) (hu : ul ≤ ur) (hAZ : a ≤ Z) :
    IntervalIntegrable (fun t => semanticUZ a K t ul ur Z) volume tl tr ∧
    IntervalIntegrable (fun t => reducedUZ a K t ul ur Z) volume tl tr := by
  have hs := (continuous_safeUZ ha K ul ur Z).intervalIntegrable tl tr
  have ho : IntervalIntegrable (fun t => semanticUZ a K t ul ur Z) volume tl tr := by
    apply hs.congr
    intro t ht'
    rw [uIoc_of_le ht] at ht'
    exact safeUZ_eq (htl.trans ht'.1.le) hul hu hAZ
  exact ⟨ho, ho.congr (fun _t _ht => semanticUZ_eq_reducedUZ ha hAZ)⟩

namespace FullMask

open PairedV2 PairedV2.FullMask

/-- The transformed coordinate remains in the actual analytic regime of
the adopted row.  This is the same residual cutoff, transported through
the proved inverse map, rather than a new pointwise hypothesis. -/
theorem transformed_argument_ge (r : Row) {t u z s : ℝ}
    (ht : t ∈ Icc (tLower (indices r).1 : ℝ) (tUpper (indices r).1 : ℝ))
    (hu : u ∈ Icc (uLower (indices r).2 : ℝ) (uUpper (indices r).2 : ℝ))
    (hz : z ∈ Icc (a : ℝ) (cutoff r : ℝ))
    (hs : s ∈ Icc (lower t u z) (upper (a : ℝ) t u z)) :
    (7 / 3 : ℝ) ≤ s := by
  have ha : (0 : ℝ) < (a : ℝ) := by norm_num [a]
  have hzpos : 0 < z := ha.trans_le hz.1
  have hw := recover_mem hzpos hs
  have harg := P2PairedFibreBuchstabVariableLower.FullMask.closedSupport_argument
    r (t := t) (u := u) (z := z) (w := residual t u z - z * s) ⟨ht, hu, hz, hw⟩
  rw [argument_recovered t u z s hzpos.ne'] at harg
  exact harg

/-- Both actual inner integrals are genuinely integrable on every closed
adopted fibre, including its degenerate lower slice. -/
theorem row_inner_integrability (r : Row) {t u z : ℝ}
    (ht : t ∈ Icc (tLower (indices r).1 : ℝ) (tUpper (indices r).1 : ℝ))
    (hu : u ∈ Icc (uLower (indices r).2 : ℝ) (uUpper (indices r).2 : ℝ))
    (hz : z ∈ Icc (a : ℝ) (cutoff r : ℝ)) :
    IntervalIntegrable (semanticKernel (K : ℝ) t u z) volume (a : ℝ) z ∧
    IntervalIntegrable (fun s => jacobian t u z s * gain s) volume
      (lower t u z) (upper (a : ℝ) t u z) := by
  have ha : (0 : ℝ) < (a : ℝ) := by norm_num [a]
  have hs : P2PairedFibreBuchstabVariableLower.FullMask.closedSupport r t u z (a : ℝ) :=
    ⟨ht, hu, hz, le_rfl, hz.1⟩
  obtain ⟨ht', hu', _hz', _hw'⟩ :=
    P2PairedFibreBuchstabVariableLower.FullMask.closedSupport_lower_bounds r hs
  exact ⟨intervalIntegrable_semanticKernel ha hz.1 (ha.trans_le ht') (ha.trans_le hu'),
    intervalIntegrable_transformed ha hz.1⟩

/-- The final outer integrands on every adopted row are genuinely
integrable in both representations.  The intermediate `z` and `u`
obligations are the unconditional lemmas above. -/
theorem row_outer_integrability (r : Row) :
    IntervalIntegrable
      (fun t => semanticUZ (a : ℝ) (K : ℝ) t
        (uLower (indices r).2 : ℝ) (uUpper (indices r).2 : ℝ) (cutoff r : ℝ))
      volume (tLower (indices r).1 : ℝ) (tUpper (indices r).1 : ℝ) ∧
    IntervalIntegrable
      (fun t => reducedUZ (a : ℝ) (K : ℝ) t
        (uLower (indices r).2 : ℝ) (uUpper (indices r).2 : ℝ) (cutoff r : ℝ))
      volume (tLower (indices r).1 : ℝ) (tUpper (indices r).1 : ℝ) := by
  obtain ⟨haZ, hzul, huu, _hurh, hhtl, htt, _htrd, _hcut⟩ := row_endpoint_bounds r
  have ha : (0 : ℝ) < (a : ℝ) := by norm_num [a]
  have hAZ : (a : ℝ) ≤ (cutoff r : ℝ) := by exact_mod_cast haZ.le
  have hZU : (cutoff r : ℝ) ≤ (uLower (indices r).2 : ℝ) := by exact_mod_cast hzul
  have hTU : (tLower (indices r).1 : ℝ) ≤ (tUpper (indices r).1 : ℝ) := by
    exact_mod_cast htt.le
  have hUU : (uLower (indices r).2 : ℝ) ≤ (uUpper (indices r).2 : ℝ) := by
    exact_mod_cast huu.le
  have hHT : (h : ℝ) < (tLower (indices r).1 : ℝ) := by exact_mod_cast hhtl
  have hAH : (a : ℝ) < (h : ℝ) := by norm_num [a, h]
  exact intervalIntegrable_t ha (hAH.trans hHT).le hTU (hAZ.trans hZU) hUU hAZ

/-- Each adopted row is identified with the precise transformed triple
integral, including the row's original coefficient and endpoint data. -/
theorem rowGainIntegral_eq_tripleReduced (r : Row) :
    P2PairedFibreBuchstabVariableLower.FullMask.rowGainIntegral r =
      tripleReduced (K : ℝ) (a : ℝ)
        (tLower (indices r).1 : ℝ) (tUpper (indices r).1 : ℝ)
        (uLower (indices r).2 : ℝ) (uUpper (indices r).2 : ℝ) (cutoff r : ℝ) := by
  have ha : (0 : ℝ) < (a : ℝ) := by norm_num [a]
  have hAZ : (a : ℝ) ≤ (cutoff r : ℝ) := by
    exact_mod_cast (row_endpoint_bounds r).1.le
  exact fourfoldSemantic_eq_tripleReduced ha hAZ

/-- Summation changes only the representation of each literal row. -/
theorem sum_rowGainIntegral_eq_sum_tripleReduced :
    (∑ r : Row, P2PairedFibreBuchstabVariableLower.FullMask.rowGainIntegral r) =
      ∑ r : Row, tripleReduced (K : ℝ) (a : ℝ)
        (tLower (indices r).1 : ℝ) (tUpper (indices r).1 : ℝ)
        (uLower (indices r).2 : ℝ) (uUpper (indices r).2 : ℝ) (cutoff r : ℝ) := by
  exact Finset.sum_congr rfl (fun r _hr => rowGainIntegral_eq_tripleReduced r)

end FullMask

end

end ImbalancedChen.Certificates.P2BuchstabFibreAffineReduction
