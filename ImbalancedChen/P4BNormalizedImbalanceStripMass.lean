import ImbalancedChen.P4BImbalanceBoundaryMass
import ImbalancedChen.P4BLabelledLogGeometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# P4B: actual normalized logarithmic wall-strip mass

SOURCE ONLY / YELLOW / UNCOMPILED.

The two P4B imports name the intended source modules of the sibling drafts;
they must be staged before a later, separately authorized compiler check.
No compiler acceptance is claimed here.  The strip below is the literal
ordered prime-pair collar with width `-delta < (log r-b log q)/log N <= 0`.
Its product maps injectively into an actual exponent-source difference,
so the previously proved unconditional arithmetic band reserve pays it.
-/

namespace ImbalancedChen.P4BNormalizedImbalanceStripMass

noncomputable section
open Filter Topology

/-- Literal normalized distance on the outside of the strict badness wall. -/
def normalizedWall (b : ℝ) (N r q : ℕ) : ℝ :=
  (Real.log (r : ℝ) - b * Real.log (q : ℝ)) / Real.log (N : ℝ)

/-- Actual ordered prime pairs in the one-sided logarithmic collar.  The
manuscript lower cutoff and inclusive product cap are kept verbatim. -/
def normalizedPrimePairStrip (b kappa delta : ℝ) (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter fun p =>
    Nat.Prime p.1 ∧ Nat.Prime p.2 ∧ p.1 ≤ p.2 ∧
      manuscriptHalfProductCutoff kappa N ≤ (p.1 * p.2 : ℕ) ∧
      p.1 * p.2 ≤ N ∧ -delta < normalizedWall b N p.1 p.2 ∧
      normalizedWall b N p.1 p.2 ≤ 0

@[simp] theorem mem_normalizedPrimePairStrip {b kappa delta : ℝ} {N r q : ℕ} :
    (r, q) ∈ normalizedPrimePairStrip b kappa delta N ↔
      Nat.Prime r ∧ Nat.Prime q ∧ r ≤ q ∧
        manuscriptHalfProductCutoff kappa N ≤ (r * q : ℕ) ∧ r * q ≤ N ∧
        -delta < normalizedWall b N r q ∧ normalizedWall b N r q ≤ 0 := by
  classical
  unfold normalizedPrimePairStrip
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · rintro ⟨hr, hq, hrq, hcut, hprod, hlow, hhigh⟩
    have hrN : r ≤ N := by
      calc
        r = r * 1 := (Nat.mul_one r).symm
        _ ≤ r * q := Nat.mul_le_mul_left r hq.one_le
        _ ≤ N := hprod
    have hqN : q ≤ N := by
      calc
        q = 1 * q := (Nat.one_mul q).symm
        _ ≤ r * q := Nat.mul_le_mul_right q hr.one_le
        _ ≤ N := hprod
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hrN),
        Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hqN)⟩,
      hr, hq, hrq, hcut, hprod, hlow, hhigh⟩

/-- The ordered factor q has a uniform positive normalized logarithm on the
manuscript product carrier.  The factor 2 only strengthens this bound. -/
theorem logq_div_logN_lower {kappa : ℝ} {N r q : ℕ}
    (hN : 2 ≤ N) (hr : Nat.Prime r) (hq : Nat.Prime q) (hrq : r ≤ q)
    (hcut : manuscriptHalfProductCutoff kappa N ≤ (r * q : ℕ)) :
    (1 - kappa) / 2 ≤ Real.log (q : ℝ) / Real.log (N : ℝ) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans hN1
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hpow : 0 < (N : ℝ) ^ (1 - kappa) :=
    Real.rpow_pos_of_pos hNpos _
  have hpowCut : (N : ℝ) ^ (1 - kappa) ≤ (r * q : ℕ) := by
    have hfactor : (N : ℝ) ^ (1 - kappa) ≤
        manuscriptHalfProductCutoff kappa N := by
      unfold manuscriptHalfProductCutoff
      linarith
    exact hfactor.trans hcut
  have hlower :=
    (P4BLabelledLogGeometry.lowerCutoff_iff_normalized_logs hN1 hpow hrR hqR).mp
      hpowCut
  have hlogPower : Real.log ((N : ℝ) ^ (1 - kappa)) / Real.log (N : ℝ) =
      1 - kappa := by
    rw [Real.log_rpow hNpos]
    field_simp [hlog.ne']
  rw [hlogPower] at hlower
  have horder :=
    (P4BLabelledLogGeometry.order_iff_normalized_logs hN1 hrR hqR).mp hrq
  linarith

/-- The lower bound is strictly positive at every fixed kappa<1. -/
theorem logq_div_logN_positive_lower {kappa : ℝ} {N r q : ℕ}
    (hkappa1 : kappa < 1) (hN : 2 ≤ N)
    (hr : Nat.Prime r) (hq : Nat.Prime q) (hrq : r ≤ q)
    (hcut : manuscriptHalfProductCutoff kappa N ≤ (r * q : ℕ)) :
    0 < (1 - kappa) / 2 ∧
      (1 - kappa) / 2 ≤ Real.log (q : ℝ) / Real.log (N : ℝ) := by
  exact ⟨by linarith, logq_div_logN_lower hN hr hq hrq hcut⟩

/-- For a previously fixed a<b, choose a positive normalized width within
the explicit geometric budget s*(b-a), where s=(1-kappa)/2. -/
theorem exists_positive_width {a b kappa : ℝ} (hab : a < b) (hkappa1 : kappa < 1) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ ((1 - kappa) / 2) * (b - a) := by
  have hs : 0 < (1 - kappa) / 2 := by linarith
  have hprod : 0 < ((1 - kappa) / 2) * (b - a) :=
    mul_pos hs (sub_pos.mpr hab)
  refine ⟨(((1 - kappa) / 2) * (b - a)) / 2, half_pos hprod, ?_⟩
  linarith

/-- A logarithmic collar point lies in the genuine exponent-source band.
The strict lower width endpoint gives the strict a-power inequality even
when delta equals its allowed budget; the b-wall remains inclusive. -/
theorem strip_product_mem_imbalanceBand {a b kappa delta : ℝ} {N r q : ℕ}
    (hab : a < b) (hN : 2 ≤ N)
    (hdelta : delta ≤ ((1 - kappa) / 2) * (b - a))
    (hpair : (r, q) ∈ normalizedPrimePairStrip b kappa delta N) :
    r * q ∈ P4BImbalanceBoundaryMass.imbalanceBand a b kappa N := by
  rcases mem_normalizedPrimePairStrip.mp hpair with
    ⟨hr, hq, hrq, hcut, hprod, hlow, hhigh⟩
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hy := logq_div_logN_lower hN hr hq hrq hcut
  have hdiff : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hdeltaY : delta ≤
      (b - a) * (Real.log (q : ℝ) / Real.log (N : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_right hy hdiff
    exact hdelta.trans (by simpa only [mul_comm] using hm)
  have hwall : normalizedWall b N r q =
      Real.log (r : ℝ) / Real.log (N : ℝ) -
        b * (Real.log (q : ℝ) / Real.log (N : ℝ)) := by
    unfold normalizedWall
    ring
  rw [hwall] at hlow hhigh
  have hlogA : a * (Real.log (q : ℝ) / Real.log (N : ℝ)) <
      Real.log (r : ℝ) / Real.log (N : ℝ) := by
    nlinarith only [hlow, hdeltaY]
  have hpowA : (q : ℝ) ^ a < (r : ℝ) :=
    (P4BLabelledLogGeometry.power_iff_normalized_logs a hN1 hrR hqR).mpr hlogA
  have hpowB : (r : ℝ) ≤ (q : ℝ) ^ b := by
    apply le_of_not_gt
    intro hbad
    have hlogBad :=
      (P4BLabelledLogGeometry.power_iff_normalized_logs b hN1 hrR hqR).mp hbad
    linarith
  exact P4BImbalanceBoundaryMass.mem_imbalanceBand_iff.mpr
    ⟨hprod, hcut, r, q, hr, hq, rfl, hrq, hpowA, hpowB⟩

/-- Multiplication is injective on these ordered prime pairs, including
prime squares; no factor of two or factor-witness multiplicity occurs. -/
theorem strip_mul_injective {b kappa delta : ℝ} {N : ℕ} {p t : ℕ × ℕ}
    (hp : p ∈ normalizedPrimePairStrip b kappa delta N)
    (ht : t ∈ normalizedPrimePairStrip b kappa delta N)
    (hprod : p.1 * p.2 = t.1 * t.2) : p = t := by
  rcases p with ⟨r, q⟩
  rcases t with ⟨s, u⟩
  rcases mem_normalizedPrimePairStrip.mp hp with ⟨hr, hq, hrq, _⟩
  rcases mem_normalizedPrimePairStrip.mp ht with ⟨hs, hu, hsu, _⟩
  obtain ⟨hrs, hqu⟩ := ordered_prime_factors_unique hr hq hs hu hrq hsu hprod
  exact Prod.ext hrs hqu

/-- The actual ordered-pair strip count is bounded by the actual arithmetic
band count through that injective product map. -/
theorem strip_card_le_imbalanceBand {a b kappa delta : ℝ} {N : ℕ}
    (hab : a < b) (hN : 2 ≤ N)
    (hdelta : delta ≤ ((1 - kappa) / 2) * (b - a)) :
    (normalizedPrimePairStrip b kappa delta N).card ≤
      (P4BImbalanceBoundaryMass.imbalanceBand a b kappa N).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1 * p.2)
  · rintro ⟨r, q⟩ hp
    exact strip_product_mem_imbalanceBand hab hN hdelta hp
  · intro p hp t ht hprod
    exact strip_mul_injective hp ht hprod

/-- Unconditional reserve for the actual normalized imbalance-wall collar.
For fixed b and kappa, the width is chosen after eta and before the single
integer threshold. The bound holds for every subsequent N, hence for every
even N there. No distribution or collar-mass premise is assumed. -/
theorem exists_normalized_strip_mass_reserve {b kappa eta : ℝ}
    (hbHalf : (1 / 2 : ℝ) < b) (hb1 : b < 1)
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N →
        ((normalizedPrimePairStrip b kappa delta N).card : ℝ) ≤
          eta * ((N : ℝ) / Real.log (N : ℝ)) := by
  obtain ⟨a, ha, haHalf, hab, ha1, hgap, N0, hN0, hband⟩ :=
    P4BImbalanceBoundaryMass.exists_parameter_boundary_mass_reserve
      hbHalf hb1 hkappa heta
  obtain ⟨delta, hdeltaPos, hdelta⟩ := exists_positive_width hab hkappa1
  refine ⟨delta, hdeltaPos, N0, hN0, ?_⟩
  intro N hNN0
  have hN : 2 ≤ N := hN0.trans hNN0
  have hcard : ((normalizedPrimePairStrip b kappa delta N).card : ℝ) ≤
      ((P4BImbalanceBoundaryMass.imbalanceBand a b kappa N).card : ℝ) := by
    exact_mod_cast strip_card_le_imbalanceBand hab hN hdelta
  exact hcard.trans (hband N hNN0)

end
end ImbalancedChen.P4BNormalizedImbalanceStripMass
