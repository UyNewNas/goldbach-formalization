import ImbalancedChen.OriginalPairedN48SmallLogSoundness
import ImbalancedChen.P2HistoricSieveTrapezoidError
import Mathlib.Analysis.Convex.Deriv

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual Buchstab curvature control without assuming a second derivative at
the integer knots.  The slope is globally 2-Lipschitz on [2,infinity).
Consequently ±omega+x² are convex on every tail cell.  The same quadratic
chord bound gives BOTH the original h³/6 trapezoid error and h²/4 bulge.
-/

namespace ImbalancedChen.OriginalPairedN48BuchstabQuadraticError

noncomputable section
open Set MeasureTheory Filter
open scoped Interval Topology
open LiLiuPrereqBuchstab
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalPairedN48OmegaProducerAdapter
open OriginalPairedN48OmegaTrapezoidStep

private theorem initial_lipschitz {s t : ℝ}
    (hs : 1 ≤ s) (hst : s ≤ t) (ht : t ≤ 2) :
    |buchstab s - buchstab t| ≤ t - s := by
  have hs0 : 0 < s := by linarith only [hs]
  have ht0 : 0 < t := hs0.trans_le hst
  rw [buchstab_eq_one_div hs (hst.trans ht),
    buchstab_eq_one_div (hs.trans hst) ht]
  have hnonneg : 0 ≤ 1 / s - 1 / t :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hs0 hst)
  have he : 1 / s - 1 / t = (t - s) / (s * t) := by
    field_simp [hs0.ne', ht0.ne']
    <;> ring
  rw [abs_of_nonneg hnonneg, he]
  have hden : 1 ≤ s * t := by
    have hp := mul_nonneg (sub_nonneg.mpr hs)
      (sub_nonneg.mpr (hs.trans hst))
    nlinarith only [hp, hs, hst]
  apply (div_le_iff₀ (mul_pos hs0 ht0)).2
  have h := mul_le_mul_of_nonneg_left hden (sub_nonneg.mpr hst)
  simpa only [mul_one] using h

/-- This includes the entire initial reciprocal interval and the join at2.
No derivative assertion is made at the derivative jump itself. -/
theorem buchstab_lipschitz_one {s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    |buchstab s - buchstab t| ≤ |s - t| := by
  have hord : ∀ s t : ℝ, 1 ≤ s → s ≤ t →
      |buchstab s - buchstab t| ≤ t - s := by
    intro s t hs hst
    by_cases hs2 : 2 ≤ s
    · have h := P5Z.U1011BuchstabTailLipschitz.abs_sub_le_half hs2 (hs2.trans hst)
      rw [abs_of_nonpos (sub_nonpos.mpr hst)] at h
      linarith only [h, hst]
    · by_cases ht2 : t ≤ 2
      · exact initial_lipschitz hs hst ht2
      · have hleft := initial_lipschitz (s := s) (t := 2) hs
          (le_of_lt (lt_of_not_ge hs2)) (by norm_num)
        have hright := P5Z.U1011BuchstabTailLipschitz.abs_sub_le_half
          (s := 2) (t := t) (by norm_num) (le_of_lt (lt_of_not_ge ht2))
        rw [abs_of_nonpos (by linarith only [ht2] : 2 - t ≤ 0)] at hright
        have htriangle := abs_sub_le (buchstab s) (buchstab 2) (buchstab t)
        linarith only [hleft, hright, htriangle, le_of_not_ge ht2]
  rcases le_total s t with hst | hts
  · have h := hord s t hs hst
    simpa only [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using h
  · have h := hord t s ht hts
    simpa only [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hts)] using h

def numerator (s : ℝ) : ℝ := buchstab (s - 1) - buchstab s
def slope (s : ℝ) : ℝ := numerator s / s

/-- The true unweighted derivative follows from the pinned weighted DDE. -/
theorem hasDerivAt_buchstab {s : ℝ} (hs : 2 < s) :
    HasDerivAt buchstab (slope s) s := by
  have hs0 : 0 < s := by linarith only [hs]
  have hd := (hasDerivAt_mul_buchstab hs).fun_div (hasDerivAt_id s) hs0.ne'
  have hd' : HasDerivAt (fun t : ℝ => (t * buchstab t) / t) (slope s) s := by
    apply hd.congr_deriv
    dsimp [slope, numerator]
    field_simp [hs0.ne']
    <;> ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs0] with t ht
  field_simp [ht.ne']

private theorem numerator_abs_le_one {s : ℝ} (hs : 2 ≤ s) :
    |numerator s| ≤ 1 := by
  have ha0 := buchstab_nonneg (show 1 ≤ s - 1 by linarith only [hs])
  have ha1 := buchstab_le_one (show 1 ≤ s - 1 by linarith only [hs])
  have hb0 := buchstab_nonneg (show 1 ≤ s by linarith only [hs])
  have hb1 := buchstab_le_one (show 1 ≤ s by linarith only [hs])
  apply abs_le.mpr
  dsimp [numerator]
  constructor <;> linarith only [ha0, ha1, hb0, hb1]

/-- A deliberately uniform constant2 also crosses all later integer knots.
It is exactly sufficient for the original trapezoid and cell-bulge tokens. -/
theorem slope_lipschitz_two {s t : ℝ} (hs : 2 ≤ s) (ht : 2 ≤ t) :
    |slope s - slope t| ≤ 2 * |s - t| := by
  have hord : ∀ s t : ℝ, 2 ≤ s → s ≤ t →
      |slope s - slope t| ≤ 2 * (t - s) := by
    intro s t hs hst
    have hs0 : 0 < s := by linarith only [hs]
    have ht0 : 0 < t := hs0.trans_le hst
    have hd : 0 ≤ t - s := sub_nonneg.mpr hst
    have hA := buchstab_lipschitz_one
      (show 1 ≤ s - 1 by linarith only [hs])
      (show 1 ≤ t - 1 by linarith only [hs, hst])
    have hB := buchstab_lipschitz_one
      (show 1 ≤ s by linarith only [hs])
      (show 1 ≤ t by linarith only [hs, hst])
    have hid : (s - 1) - (t - 1) = s - t := by ring
    rw [hid, abs_of_nonpos (sub_nonpos.mpr hst)] at hA
    rw [abs_of_nonpos (sub_nonpos.mpr hst)] at hB
    have hnum : |numerator s - numerator t| ≤ 2 * (t - s) := by
      have he : numerator s - numerator t =
          (buchstab (s - 1) - buchstab (t - 1)) +
            -(buchstab s - buchstab t) := by dsimp [numerator]; ring
      rw [he]
      have htri := abs_add (buchstab (s - 1) - buchstab (t - 1))
        (-(buchstab s - buchstab t))
      rw [abs_neg] at htri
      linarith only [hA, hB, htri]
    have hNt := numerator_abs_le_one (hs.trans hst)
    have he : s * t * (slope s - slope t) =
        t * (numerator s - numerator t) + (t - s) * numerator t := by
      dsimp [slope]
      field_simp [hs0.ne', ht0.ne']
      <;> ring
    have hprod : |s * t * (slope s - slope t)| ≤ 2 * t * (t - s) + (t - s) := by
      rw [he]
      calc
        |t * (numerator s - numerator t) + (t - s) * numerator t| ≤
            |t * (numerator s - numerator t)| + |(t - s) * numerator t| := abs_add _ _
        _ = t * |numerator s - numerator t| + (t - s) * |numerator t| := by
          rw [abs_mul, abs_mul, abs_of_pos ht0, abs_of_nonneg hd]
        _ ≤ t * (2 * (t - s)) + (t - s) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hnum ht0.le)
            (mul_le_mul_of_nonneg_left hNt hd)
        _ = 2 * t * (t - s) + (t - s) := by ring
    have hpay : 2 * t * (t - s) + (t - s) ≤ (s * t) * (2 * (t - s)) := by
      have h1 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hs ht0.le) (show 0 ≤ 2 * (t - s) by positivity)
      have h2 := mul_le_mul_of_nonneg_right
        (show 1 ≤ 2 * t by linarith only [hs, hst]) hd
      nlinarith only [h1, h2]
    rw [abs_mul, abs_of_pos (mul_pos hs0 ht0)] at hprod
    exact (mul_le_mul_left (mul_pos hs0 ht0)).mp (hprod.trans hpay)
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hord s t hs hst
  · simpa only [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hts)] using hord t s ht hts

private theorem signed_add_square_convex {f df : ℝ → ℝ} {a b ε : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hdf : ∀ t ∈ Ioo a b, HasDerivAt f (df t) t)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |df s - df t| ≤ 2 * |s - t|)
    (hε : |ε| = 1) : ConvexOn ℝ (Icc a b) (fun t => ε * f t + t ^ 2) := by
  let g : ℝ → ℝ := fun t => ε * f t + t ^ 2
  have hd : ∀ t ∈ interior (Icc a b), HasDerivAt g (ε * df t + 2 * t) t := by
    intro t ht
    have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    convert ((hdf t ht').const_mul ε).add ((hasDerivAt_id t).pow 2) using 1
    <;> norm_num [g]
  have hmono : MonotoneOn (deriv g) (interior (Icc a b)) := by
    intro s hs t ht hst
    rw [(hd s hs).deriv, (hd t ht).deriv]
    have h := hLip s (interior_subset hs) t (interior_subset ht)
    have hsign : |ε * (df s - df t)| ≤ 2 * (t - s) := by
      rw [abs_mul, hε, one_mul]
      simpa only [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using h
    have hu := (abs_le.mp hsign).2
    nlinarith only [hu]
  exact hmono.convexOn_of_deriv (convex_Icc a b)
    ((hf.const_mul ε).add (continuousOn_id.pow 2))
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)

private theorem chord_error_of_lipschitz_slope {f df : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hdf : ∀ t ∈ Ioo a b, HasDerivAt f (df t) t)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |df s - df t| ≤ 2 * |s - t|)
    {x : ℝ} (hx : x ∈ Icc a b) :
    |f x - endpointChord f a b x| ≤ (x - a) * (b - x) := by
  let λ : ℝ := (b - x) / (b - a)
  let μ : ℝ := (x - a) / (b - a)
  have hg : 0 < b - a := sub_pos.mpr hab
  have hλ : 0 ≤ λ := div_nonneg (sub_nonneg.mpr hx.2) hg.le
  have hμ : 0 ≤ μ := div_nonneg (sub_nonneg.mpr hx.1) hg.le
  have hsum : λ + μ = 1 := by dsimp [λ, μ]; field_simp [hg.ne']; ring
  have harg : λ * a + μ * b = x := by dsimp [λ, μ]; field_simp [hg.ne']; ring
  have hquad : λ * a ^ 2 + μ * b ^ 2 - x ^ 2 = (x - a) * (b - x) := by
    dsimp [λ, μ]
    field_simp [hg.ne']
    ring
  have hp := (signed_add_square_convex hf hdf hLip (by norm_num : |(1 : ℝ)| = 1)).2
    ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hλ hμ hsum
  have hn := (signed_add_square_convex hf hdf hLip (by norm_num : |(-1 : ℝ)| = 1)).2
    ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hλ hμ hsum
  simp only [smul_eq_mul, one_mul, neg_one_mul] at hp hn
  rw [harg] at hp hn
  have hc : endpointChord f a b x = λ * f a + μ * f b := rfl
  rw [hc]
  apply abs_le.mpr
  constructor <;> nlinarith only [hp, hn, hquad]

theorem actual_buchstab_chord_error {a b : ℝ} (ha : 2 ≤ a) (hab : a < b)
    {x : ℝ} (hx : x ∈ Icc a b) :
    |buchstab x - endpointChord buchstab a b x| ≤ (x - a) * (b - x) :=
  chord_error_of_lipschitz_slope hab continuous_buchstab.continuousOn
    (fun t ht => hasDerivAt_buchstab (by linarith only [ha, ht.1]))
    (fun s hs t ht => slope_lipschitz_two (ha.trans hs.1) (ha.trans ht.1)) hx

theorem actual_delayed_chord_error {a b : ℝ} (ha : 3 ≤ a) (hab : a < b)
    {x : ℝ} (hx : x ∈ Icc a b) :
    |delayed x - endpointChord delayed a b x| ≤ (x - a) * (b - x) := by
  have hc : Continuous delayed := continuous_buchstab.comp (continuous_id.sub continuous_const)
  apply chord_error_of_lipschitz_slope hab hc.continuousOn
    (df := fun t => slope (t - 1))
  · intro t ht
    simpa only [delayed, sub_zero, mul_one] using
      (hasDerivAt_buchstab (show 2 < t - 1 by linarith only [ha, ht.1])).comp t
        ((hasDerivAt_id t).sub_const 1)
  · intro s hs t ht
    have h := slope_lipschitz_two
      (show 2 ≤ s - 1 by linarith only [ha, hs.1])
      (show 2 ≤ t - 1 by linarith only [ha, ht.1])
    have he : (s - 1) - (t - 1) = s - t := by ring
    rwa [he] at h
  · exact hx

/-- Exact integration of the shared quadratic chord majorant gives the
denominator6; taking a uniform sup before integrating would lose it. -/
theorem actual_delayed_trapezoid_error {a b : ℝ} (ha : 3 ≤ a) (hab : a < b) :
    |localIntegral a b - trapezoid a b| ≤ (b - a) ^ 3 / 6 := by
  have hc : Continuous delayed := continuous_buchstab.comp (continuous_id.sub continuous_const)
  have hch := P2HistoricSieveTrapezoidError.continuousOn_endpointChord delayed a b
  have hfi := hc.intervalIntegrable a b
  have hchi := hch.intervalIntegrable_of_Icc hab.le
  have hq : IntervalIntegrable (fun x : ℝ => (x - a) * (b - x)) volume a b := by
    exact ((continuous_id.sub continuous_const).mul
      (continuous_const.sub continuous_id)).intervalIntegrable a b
  have hi := intervalIntegral.norm_integral_le_of_norm_le hab.le
    (f := fun x => delayed x - endpointChord delayed a b x)
    (g := fun x => (x - a) * (b - x))
    (Eventually.of_forall (fun x hx => by
      simpa only [Real.norm_eq_abs] using
        actual_delayed_chord_error ha hab ⟨hx.1.le, hx.2⟩)) hq
  have hsub : (∫ x in a..b, delayed x - endpointChord delayed a b x) =
      localIntegral a b - trapezoid a b := by
    rw [intervalIntegral.integral_sub hfi hchi,
      P2HistoricSieveTrapezoidError.integral_endpointChord delayed hab]
    dsimp [localIntegral, trapezoid, P2HistoricSieveTrapezoidError.trapezoid]
    ring
  have hint := P2HistoricSieveTrapezoidError.integral_quadratic_remainder
    (M := 2) (b := b) (show 0 < a by linarith only [ha])
  have heq : (fun x : ℝ => 2 * (x - a) * (b - x) / 2) =
      (fun x => (x - a) * (b - x)) := by funext x; ring
  rw [heq] at hint
  rw [hsub, hint, Real.norm_eq_abs] at hi
  convert hi using 1 <;> ring

/-- The actual grid allowance used by the original Omega producer. -/
theorem original_sharpCellError (i : ℕ) (hi : 3 * mesh < i) :
    SharpCellError (((i - 1 : ℕ) : ℝ) / (mesh : ℝ)) ((i : ℝ) / (mesh : ℝ)) := by
  have hm : (0 : ℝ) < mesh := by norm_num [mesh]
  have hidx : 3 * mesh ≤ i - 1 := by omega
  have ha : (3 : ℝ) ≤ ((i - 1 : ℕ) : ℝ) / (mesh : ℝ) := by
    apply (le_div_iff₀ hm).2
    exact_mod_cast hidx
  have hs : (i - 1 : ℕ) + 1 = i := by omega
  have hsR : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast hs
  have hw : (i : ℝ) / (mesh : ℝ) - ((i - 1 : ℕ) : ℝ) / (mesh : ℝ) =
      1 / (mesh : ℝ) := by
    field_simp [hm.ne']
    linarith only [hsR]
  have hab : ((i - 1 : ℕ) : ℝ) / (mesh : ℝ) < (i : ℝ) / (mesh : ℝ) := by
    have hp := one_div_pos.mpr hm
    linarith only [hw, hp]
  have h := actual_delayed_trapezoid_error ha hab
  rw [hw] at h
  unfold SharpCellError
  convert h using 1 <;> norm_num [sharpErrorQ, mesh]

/-- Uniform node soundness now has no log or local-error premise.
The pure finite producer predicate still needs its concrete byte witness. -/
theorem original_weighted_nodes (p : SourceArrays) (hp : SourceProducerValid p) :
    ∀ i : ℕ, mesh ≤ i → i < uCount →
      (OriginalN48Q112LocalProduct.decode (Uat p i)).Contains
        (((i : ℝ) / (mesh : ℝ)) * buchstab ((i : ℝ) / (mesh : ℝ))) :=
  OriginalPairedN48SmallLogSoundness.all_weighted_nodes_of_original_local_error p hp
    (fun i hi _ => original_sharpCellError i hi)

end
end ImbalancedChen.OriginalPairedN48BuchstabQuadraticError
