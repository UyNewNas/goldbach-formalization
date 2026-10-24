import ImbalancedChen.CurrentChenP5CausalRhoQuotientBridge
import ImbalancedChen.CurrentChenUpsilon6LogDomain
import ImbalancedChen.VariableEnvelope
import Mathlib.Tactic.FieldSimp

/-!
# Actual original U6 causal level and its quotient attachment geometry

Source checked: global-chen-lower-completion-20261010.txt, section 4.
For U6 the level is the enhanced max only when the larger prime exponent
t is below mu. At and above mu it is v(t), hence 57/64-3t/2. Extending
the U5 max formula to that whole U6 rectangle would change this source.

The corrected Runbo product domain supplies the physical cutoff square.
The actual source exponent, inherited child alpha, concrete small-weight
attachment parameters and original same-mask quotient minorant are proved.
The full signed rho support above sqrt(N) still needs its P3 licensing;
the physical cap in these identities is not replaced by a support cover.

SOURCE ONLY: uncompiled; prior draft modules are frozen.
-/

namespace ImbalancedChen.P5U6CausalLevelGeometry

open scoped BigOperators
open Classical
open P5SelectedMaskTransport

noncomputable section

abbrev Point := Fin 2 → ℝ
def a : ℝ := 417 / 5000
def h : ℝ := 19 / 125
def d : ℝ := 59 / 250

/-- Literal original root occurrence: t is the larger prime coordinate. -/
def physicalLevel (u t : ℝ) : ℝ :=
  if t < VariableEnvelope.mu then
    max (VariableEnvelope.v t)
      (max (VariableEnvelope.v (t + u)) (VariableEnvelope.B a))
  else VariableEnvelope.v t

def residual (x : Point) : ℝ := physicalLevel (x 0) (x 1) - x 0 - x 1
def sourceExponent (x : Point) : ℝ := 1 - x 0 - x 1
def argument (x : Point) : ℝ := residual x / a
def alpha (x : Point) : ℝ := sourceExponent x / residual x
def relativeCutoff (x : Point) : ℝ := a / residual x

theorem physicalLevel_nonEnhanced {u t : ℝ} (ht : VariableEnvelope.mu ≤ t) :
    physicalLevel u t = 57 / 64 - 3 / 2 * t := by
  rw [physicalLevel, if_neg (not_lt_of_ge ht), VariableEnvelope.v_eq_C ht]
  rfl

theorem residual_nonEnhanced {x : Point} (ht : VariableEnvelope.mu ≤ x 1) :
    residual x = 57 / 64 - 5 / 2 * x 1 - x 0 := by
  unfold residual
  rw [physicalLevel_nonEnhanced ht]
  ring

theorem physicalLevel_bounds {u t : ℝ}
    (hu : a ≤ u) (huh : u ≤ h) (hht : h ≤ t) (htd : t ≤ d) :
    (1 / 2 : ℝ) < physicalLevel u t ∧
      physicalLevel u t ≤ (1 + t + u) / 2 := by
  by_cases htm : t < VariableEnvelope.mu
  · have hv : VariableEnvelope.v t = (1 + t) / 2 := by
      simpa only [VariableEnvelope.A] using VariableEnvelope.v_eq_A htm.le
    rw [physicalLevel, if_pos htm]
    constructor
    · apply lt_of_lt_of_le ?_ (le_max_left _ _)
      rw [hv]
      norm_num [h] at hht
      linarith
    · apply max_le
      · rw [hv]
        norm_num [a] at hu
        linarith
      · apply max_le
        · rw [VariableEnvelope.v_eq_min]
          exact (min_le_left _ _).trans (by dsimp [VariableEnvelope.A]; linarith)
        · dsimp [VariableEnvelope.B, VariableEnvelope.cap, a, h] at *
          linarith
  · have hmu : VariableEnvelope.mu ≤ t := le_of_not_gt htm
    rw [physicalLevel_nonEnhanced hmu]
    constructor
    · dsimp [d] at htd
      linarith
    · dsimp [VariableEnvelope.mu] at hmu
      dsimp [a] at hu
      linarith

theorem domain_bounds {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) :
    2 * a + eta < residual x ∧ residual x ≤ sourceExponent x / 2 ∧
      sourceExponent x ≤ 1 ∧ 0 < sourceExponent x := by
  obtain ⟨hu, huh, hht, htd⟩ := mem_currentChenUpsilon6LogRectangle.mp hx.1
  have hlevel := physicalLevel_bounds hu huh.le hht htd.le
  have hproduct := hx.2
  change x 0 + x 1 ≤ (833 / 2500 : ℝ) - eta at hproduct
  dsimp [residual, sourceExponent, a] at *
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem residual_pos {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) : 0 < residual x := by
  have hr := (domain_bounds heta hx).1
  norm_num [a] at hr
  linarith

/-- Original cutoff and both selected-prefix squares are genuinely legal
at this piecewise U6 physical level. -/
theorem root_squares {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) :
    2 * x 1 < physicalLevel (x 0) (x 1) ∧
      x 1 + 2 * x 0 < physicalLevel (x 0) (x 1) ∧
      x 0 + x 1 + 2 * a < physicalLevel (x 0) (x 1) := by
  obtain ⟨hu, huh, hht, htd⟩ := mem_currentChenUpsilon6LogRectangle.mp hx.1
  have hl := (physicalLevel_bounds hu huh.le hht htd.le).1
  have hp := hx.2
  have hr := (domain_bounds heta hx).1
  change x 0 + x 1 ≤ (833 / 2500 : ℝ) - eta at hp
  dsimp [residual, a] at hr ⊢
  constructor
  · norm_num [d] at htd
    linarith
  constructor
  · norm_num [h] at huh
    linarith
  · linarith

theorem cutoff_le_residual_half {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) : a ≤ residual x / 2 := by
  have h := (domain_bounds heta hx).1
  linarith

/-- The actual causal attachment may take nu=R and r=a/R. This identifies
the original cutoff exactly, without identifying an h248 correction. -/
theorem residual_mul_relativeCutoff {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) : residual x * relativeCutoff x = a := by
  unfold relativeCutoff
  field_simp [(residual_pos heta hx).ne'] <;> ring

theorem relativeCutoff_mem {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) :
    0 < relativeCutoff x ∧ relativeCutoff x ≤ 1 / 2 := by
  have hR := residual_pos heta hx
  constructor
  · exact div_pos (by norm_num [a]) hR
  · apply (div_le_iff₀ hR).mpr
    have h := cutoff_le_residual_half heta hx
    linarith

theorem argument_ge_two {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) : 2 ≤ argument x := by
  apply (le_div_iff₀ (by norm_num [a] : 0 < a)).mpr
  have h := (domain_bounds heta hx).1
  linarith

theorem alpha_ge_two {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) : 2 ≤ alpha x := by
  apply (le_div_iff₀ (residual_pos heta hx)).mpr
  have h := (domain_bounds heta hx).2.1
  linarith

theorem residual_div_argument {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) : residual x / argument x = a := by
  unfold argument
  field_simp [(residual_pos heta hx).ne', show a ≠ 0 by norm_num [a]] <;> ring

theorem sourcePower_eq_residualPower_alpha {N : ℕ} (hN : (1 : ℝ) < N)
    {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) :
    (N : ℝ) ^ sourceExponent x = ((N : ℝ) ^ residual x) ^ alpha x := by
  rw [← Real.rpow_mul (zero_lt_one.trans hN).le]
  congr 1
  unfold alpha
  field_simp [(residual_pos heta hx).ne'] <;> ring

/-- A child keeps the same total physical cap. Its extra absolute prefix
exponent is xi, so neither the source exponent nor alpha is reset. -/
def childResidual (x : Point) (xi : ℝ) : ℝ := residual x - xi
def childSourceExponent (x : Point) (xi : ℝ) : ℝ := sourceExponent x - xi
def childAlpha (x : Point) (xi : ℝ) : ℝ := childSourceExponent x xi / childResidual x xi

theorem child_keeps_total_cap (x : Point) (xi : ℝ) :
    x 0 + x 1 + xi + childResidual x xi = physicalLevel (x 0) (x 1) := by
  unfold childResidual residual
  ring

theorem child_alpha_recurrence {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) {xi : ℝ} (hxi : xi < residual x) :
    childAlpha x xi = 1 + (alpha x - 1) / (1 - xi / residual x) := by
  have hR := residual_pos heta hx
  have hchild : residual x - xi ≠ 0 := (sub_pos.mpr hxi).ne'
  have hden : 1 - xi / residual x ≠ 0 :=
    (sub_pos.mpr ((div_lt_one hR).mpr hxi)).ne'
  unfold childAlpha childSourceExponent childResidual alpha
  field_simp [hR.ne', hchild, hden]
  <;> ring

theorem child_alpha_ge_parent {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) {xi : ℝ}
    (hxi0 : 0 ≤ xi) (hxi : xi < residual x) : alpha x ≤ childAlpha x xi := by
  have hR := residual_pos heta hx
  have hchild : 0 < residual x - xi := sub_pos.mpr hxi
  have ha := alpha_ge_two heta hx
  have hsource := (domain_bounds heta hx).2.1
  unfold alpha childAlpha childSourceExponent childResidual
  apply (div_le_div_iff₀ hR hchild).mpr
  have hmul := mul_nonneg hxi0 (by linarith [hR] : 0 ≤ sourceExponent x - residual x)
  nlinarith only [hmul]

theorem child_alpha_ge_two {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) {xi : ℝ}
    (hxi0 : 0 ≤ xi) (hxi : xi < residual x) : 2 ≤ childAlpha x xi :=
  (alpha_ge_two heta hx).trans (child_alpha_ge_parent heta hx hxi0 hxi)

/-- A child that passes its actual cutoff square inherits the same ceiling a. -/
theorem child_cutoff_square {x : Point} {xi : ℝ}
    (hsquare : xi + 2 * a ≤ residual x) : a ≤ childResidual x xi / 2 := by
  unfold childResidual
  linarith

private theorem power_log_coordinate {N p : ℕ} (hN : (1 : ℝ) < N) (hp : 0 < p) :
    (N : ℝ) ^ (Real.log (p : ℝ) / Real.log (N : ℝ)) = p := by
  apply (Real.mul_log_eq_log_iff (zero_lt_one.trans hN)
    (by exact_mod_cast hp)).mp
  exact div_mul_cancel₀ _ (Real.log_pos hN).ne'

theorem pair_product_power {N : ℕ} (hN : (1 : ℝ) < N) {t : ℕ × ℕ}
    (ht : t ∈ sixthSupport N) :
    (N : ℝ) ^ (currentChenUpsilon6LogCoordinates N t 0 +
      currentChenUpsilon6LogCoordinates N t 1) = ((t.1 * t.2 : ℕ) : ℝ) := by
  obtain ⟨hc, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hc
  have hp0 := (mem_chenAdditivePrimeCarrier.mp hp).2.1.pos
  have hq0 := (mem_chenAdditivePrimeCarrier.mp hq).2.1.pos
  change (N : ℝ) ^ (Real.log (t.1 : ℝ) / Real.log (N : ℝ) +
    Real.log (t.2 : ℝ) / Real.log (N : ℝ)) = _
  rw [Real.rpow_add (zero_lt_one.trans hN), power_log_coordinate hN hp0,
    power_log_coordinate hN hq0, Nat.cast_mul]

/-- Literal source upper exponent N/(p1*p2), with natural quotient
rounding retained. This is independent of a distribution support cover. -/
theorem receiver_quotient_le_source_power {N : ℕ} (hN : (1 : ℝ) < N)
    {t : ℕ × ℕ} (ht : t ∈ sixthSupport N) (P : ℕ) :
    (((N - P) / (t.1 * t.2) : ℕ) : ℝ) ≤
      (N : ℝ) ^ sourceExponent (currentChenUpsilon6LogCoordinates N t) := by
  have hbpower := pair_product_power hN ht
  have hNp := zero_lt_one.trans hN
  calc
    _ ≤ ((N - P : ℕ) : ℝ) / ((t.1 * t.2 : ℕ) : ℝ) := Nat.cast_div_le
    _ ≤ (N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le N P) (Nat.cast_nonneg _)
    _ = _ := by
      rw [← hbpower]
      unfold sourceExponent
      rw [show 1 - currentChenUpsilon6LogCoordinates N t 0 -
          currentChenUpsilon6LogCoordinates N t 1 =
          1 - (currentChenUpsilon6LogCoordinates N t 0 +
            currentChenUpsilon6LogCoordinates N t 1) by ring,
        Real.rpow_sub hNp, Real.rpow_one]

def attachedSmallCutoff (N : ℕ) (epsilon : ℝ) (t : ℕ × ℕ) : ℝ :=
  (N : ℝ) ^ (residual (currentChenUpsilon6LogCoordinates N t) * epsilon ^ 2)

def attachedSmallLevel (N : ℕ) (epsilon : ℝ) (t : ℕ × ℕ) : ℝ :=
  (N : ℝ) ^ (residual (currentChenUpsilon6LogCoordinates N t) * epsilon)

/-- Concrete actual attachment parameters at the original per-pair
physical residual. A fixed epsilon<1/8 works on every corrected pair. -/
theorem attachment_gates {N : ℕ} (hN : (1 : ℝ) < N)
    {eta epsilon : ℝ} (heta : 0 ≤ eta) (heps : 0 < epsilon) (heps8 : epsilon < 1 / 8)
    (E : ℕ × ℕ → Prop) {t : ℕ × ℕ}
    (ht : t ∈ currentChenUpsilon6RetainedSelector N E eta) :
    1 < attachedSmallLevel N epsilon t ∧
      attachedSmallCutoff N epsilon t ≤ attachedSmallLevel N epsilon t ∧
      attachedSmallCutoff N epsilon t ≤ P5CausalRhoQuotientBridge.cutoff N := by
  have hx := (mem_currentChenUpsilon6RetainedSelector_log_iff hN E eta t).mp ht
  have hR := residual_pos heta hx.2.2.2
  have hb := domain_bounds heta hx.2.2.2
  have hRhalf : residual (currentChenUpsilon6LogCoordinates N t) ≤ 1 / 2 := by
    linarith only [hb.2.1, hb.2.2.1]
  have heps1 : epsilon ≤ 1 := by linarith
  have hepssq : epsilon ^ 2 ≤ epsilon := by nlinarith
  have hepssq64 : epsilon ^ 2 ≤ 1 / 64 := by nlinarith
  have hexp : residual (currentChenUpsilon6LogCoordinates N t) * epsilon ^ 2 ≤ a := by
    have hmul := mul_le_mul hRhalf hepssq64 (sq_nonneg epsilon)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    norm_num [a] at *
    linarith only [hmul]
  refine ⟨Real.one_lt_rpow hN (mul_pos hR heps), ?_, ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_le hN.le
      (mul_le_mul_of_nonneg_left hepssq hR.le)
  · exact Real.rpow_le_rpow_of_exponent_le hN.le hexp

/-- Every active full physical modulus is positive and centre-coprime.
This proves residue primitiveness, but deliberately proves no total
enhanced support envelope that could license a distribution theorem. -/
theorem concrete_active_modulus_primitive {N : ℕ}
    (hN : (1 : ℝ) < N) {eta epsilon : ℝ} (E : ℕ × ℕ → Prop)
    (policy : (ℕ × ℕ) → List ℕ → Bool) {t : ℕ × ℕ}
    (ht : t ∈ currentChenUpsilon6RetainedSelector N E eta) {k : ℕ}
    (hk : k ∈ P5CausalRhoQuotientBridge.active (policy t) N
      (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
      (attachedSmallCutoff N epsilon t) (P5CausalRhoQuotientBridge.cutoff N)
      (attachedSmallLevel N epsilon t)) :
    0 < (t.1 * t.2) * k ∧ Nat.Coprime ((t.1 * t.2) * k) N := by
  have hselector := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  have hb := chenY6PrimeSelector_sieve_data hselector
  have hkbase := (Finset.mem_filter.mp hk).1
  have hksf := actualLowerSmallRoughModuli_squarefree (policy t) N
    (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
    (attachedSmallCutoff N epsilon t) (P5CausalRhoQuotientBridge.cutoff N) hkbase
  have hkN := actualLowerSmallRoughModuli_coprime_target (policy t) N
    (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
    (attachedSmallCutoff N epsilon t) (P5CausalRhoQuotientBridge.cutoff N) hkbase
  exact ⟨mul_pos (Nat.zero_lt_one.trans hb.1) (Nat.pos_of_ne_zero hksf.ne_zero),
    Nat.coprime_mul_iff_left.mpr ⟨hb.2.1, hkN⟩⟩

/-- The genuine causal-rho quotient bridge now receives fully proved
original U6 level parameters; no arbitrary enhanced-policy license is
assumed to discharge its pointwise minorant gates. -/
theorem concrete_causal_retained_minorant {N : ℕ} (hN : (1 : ℝ) < N)
    {eta epsilon : ℝ} (heta : 0 ≤ eta) (heps : 0 < epsilon) (heps8 : epsilon < 1 / 8)
    (policy : (ℕ × ℕ) → List ℕ → Bool) (E : ℕ × ℕ → Prop) :
    P5CausalRhoQuotientBridge.estimatorSum N policy
        (attachedSmallCutoff N epsilon) (attachedSmallLevel N epsilon) (retainedSupport N eta) -
      P5CausalRhoQuotientBridge.estimatorSum N policy
        (attachedSmallCutoff N epsilon) (attachedSmallLevel N epsilon)
        ((retainedSupport N eta).filter E) ≤ currentChenUpsilon6Retained N E eta := by
  apply P5CausalRhoQuotientBridge.estimator_retained_le_actual
  intro t ht
  exact attachment_gates hN heta heps heps8 E ht

end

end ImbalancedChen.P5U6CausalLevelGeometry
