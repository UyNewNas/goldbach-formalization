import ImbalancedChen.P2HistoricQ80DefectLookup
import ImbalancedChen.P2HistoricQ80OrdinaryEstimatorSoundness
import ImbalancedChen.Certificates.PairedV2Data

/-!
# Original paired512 knots imply positive rounded chord divisors

Read-only sources: certify_sharp_184_baseline.py::pair_cell and
corpus-renewal-paired-certificate-v2-20261010.py, the latter's direct
ts/us 512-grid calls with enhance=False and diagonal=False. Their knots
are exactly the imported actual PairedV2.tLower/tUpper/uLower/uUpper.
Source SHA256 respectively:
a4ebffaf2b13123cf8d7510fed18482f85ec1a79f1bcddb220bd3d3ec8197639;
6e47caa91bd5e47678bcd8e2a1dc35659d25d44481c41dc437002be92d8b83dc.

Both affine chord gaps are fixed positive rational combinations of the
actual grid steps. Each gap exceeds one Q80 unit, so its point interval
has strictly positive integer lower endpoint. No divisor guard, saved
floor, table query licence, or final gain is assumed.

On this high-t parent grid the ascending affine plane is never accepted;
the descending plane is always accepted. The exact source skip condition
therefore reduces to s_lower<2. At s_lower=2 the chord remains eligible.
The strict crossing defect query is proved to return raw zero. Equality
at s=2 needs the bank's preceding closed-cell lookup, not the strict guard.

The historical replay does not subdivide these parent rectangles. An
arbitrarily tiny hypothetical child would not inherit this Q80 guard;
no unrelated subdivision-size bound is silently introduced here.
-/

namespace ImbalancedChen.P2HistoricChordDivisorGuard

noncomputable section

open Certificates Certificates.P2HistoricQ80DefectLookup P2DirectedLogRounding

theorem t_knot_width (i : ℕ) :
    PairedV2.tUpper i - PairedV2.tLower i = (PairedV2.d - PairedV2.mu) / 512 := by
  unfold PairedV2.tUpper PairedV2.tLower
  push_cast
  ring

theorem u_knot_width (j : ℕ) :
    PairedV2.uUpper j - PairedV2.uLower j = (PairedV2.h - PairedV2.a) / 512 := by
  unfold PairedV2.uUpper PairedV2.uLower
  push_cast
  ring

theorem t_knot_width_pos (i : ℕ) : PairedV2.tLower i < PairedV2.tUpper i := by
  have h := t_knot_width i
  norm_num [PairedV2.d, PairedV2.mu] at h
  linarith

theorem u_knot_width_pos (j : ℕ) : PairedV2.uLower j < PairedV2.uUpper j := by
  have h := u_knot_width j
  norm_num [PairedV2.h, PairedV2.a] at h
  linarith

theorem tLower_ge_mu (i : ℕ) : PairedV2.mu ≤ PairedV2.tLower i := by
  have hi : (0 : ℚ) ≤ i := Nat.cast_nonneg i
  norm_num [PairedV2.tLower, PairedV2.mu, PairedV2.d] <;> nlinarith [hi]

theorem tUpper_le_d {i : ℕ} (hi : i < 512) : PairedV2.tUpper i ≤ PairedV2.d := by
  have hcast : (i : ℚ) + 1 ≤ 512 := by exact_mod_cast Nat.succ_le_of_lt hi
  norm_num [PairedV2.tUpper, PairedV2.mu, PairedV2.d] <;> nlinarith [hcast]

theorem uLower_ge_a (j : ℕ) : PairedV2.a ≤ PairedV2.uLower j := by
  have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
  norm_num [PairedV2.uLower, PairedV2.a, PairedV2.h] <;> nlinarith [hj]

theorem uUpper_le_h {j : ℕ} (hj : j < 512) : PairedV2.uUpper j ≤ PairedV2.h := by
  have hcast : (j : ℚ) + 1 ≤ 512 := by exact_mod_cast Nat.succ_le_of_lt hj
  norm_num [PairedV2.uUpper, PairedV2.a, PairedV2.h] <;> nlinarith [hcast]

theorem ordinaryPlane0_gap (tl tr ul ur : ℚ) :
    (affineRange ordinaryPlane₀ tl tr ul ur).2 - (affineRange ordinaryPlane₀ tl tr ul ur).1 =
      (tr - tl) / 2 + (ur - ul) := by
  norm_num [affineRange, ordinaryPlane₀] <;> ring

theorem ordinaryPlane1_gap (tl tr ul ur : ℚ) :
    (affineRange ordinaryPlane₁ tl tr ul ur).2 - (affineRange ordinaryPlane₁ tl tr ul ur).1 =
      5 * (tr - tl) / 2 + (ur - ul) := by
  norm_num [affineRange, ordinaryPlane₁] <;> ring

theorem ordinaryPlane0_range (tl tr ul ur : ℚ) :
    affineRange ordinaryPlane₀ tl tr ul ur =
      (1 / 2 - 1 / 2 * tr - ur, 1 / 2 - 1 / 2 * tl - ul) := by
  apply Prod.ext <;> norm_num [affineRange, ordinaryPlane₀] <;> ring

theorem ordinaryPlane1_range (tl tr ul ur : ℚ) :
    affineRange ordinaryPlane₁ tl tr ul ur =
      (57 / 64 - 5 / 2 * tr - ur, 57 / 64 - 5 / 2 * tl - ul) := by
  apply Prod.ext <;> norm_num [affineRange, ordinaryPlane₁] <;> ring

theorem parent_plane0_gap_unit (i j : ℕ) :
    1 / (Q : ℚ) ≤
      (affineRange ordinaryPlane₀ (PairedV2.tLower i) (PairedV2.tUpper i)
        (PairedV2.uLower j) (PairedV2.uUpper j)).2 -
      (affineRange ordinaryPlane₀ (PairedV2.tLower i) (PairedV2.tUpper i)
        (PairedV2.uLower j) (PairedV2.uUpper j)).1 := by
  rw [ordinaryPlane0_gap, t_knot_width, u_knot_width]
  norm_num [PairedV2.a, PairedV2.h, PairedV2.d, PairedV2.mu, Q]

theorem parent_plane1_gap_unit (i j : ℕ) :
    1 / (Q : ℚ) ≤
      (affineRange ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
        (PairedV2.uLower j) (PairedV2.uUpper j)).2 -
      (affineRange ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
        (PairedV2.uLower j) (PairedV2.uUpper j)).1 := by
  rw [ordinaryPlane1_gap, t_knot_width, u_knot_width]
  norm_num [PairedV2.a, PairedV2.h, PairedV2.d, PairedV2.mu, Q]

/-- Exactly the Q80 rounding error bound: a gap at least one unit leaves
a strictly positive decoded lower endpoint after directed flooring. -/
theorem point_decodeLo_pos_of_unit_gap (q : ℚ) (hq : 1 / (Q : ℚ) ≤ q) :
    0 < (I80.point q).decodeLo := by
  have he := I80.lower_rounding (Enclosure.point q)
  have herr := he.2
  change q - (I80.point q).decodeLo < 1 / (Q : ℚ) at herr
  linarith

theorem point_lo_pos_of_unit_gap (q : ℚ) (hq : 1 / (Q : ℚ) ≤ q) :
    0 < (I80.point q).lo := by
  have hd := point_decodeLo_pos_of_unit_gap q hq
  have hcast : (0 : ℚ) < (I80.point q).lo := by
    exact (div_pos_iff_of_pos_right Q_pos).mp hd
  exact_mod_cast hcast

/-- These are precisely the two previously explicit hden obligations.
They hold on every actual parent, whether or not its chord is eligible. -/
theorem parent_chord_divisors_positive (i j : ℕ) :
    0 < (I80.point
      ((affineRange ordinaryPlane₀ (PairedV2.tLower i) (PairedV2.tUpper i)
        (PairedV2.uLower j) (PairedV2.uUpper j)).2 -
       (affineRange ordinaryPlane₀ (PairedV2.tLower i) (PairedV2.tUpper i)
        (PairedV2.uLower j) (PairedV2.uUpper j)).1)).lo ∧
    0 < (I80.point
      ((affineRange ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
        (PairedV2.uLower j) (PairedV2.uUpper j)).2 -
       (affineRange ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
        (PairedV2.uLower j) (PairedV2.uUpper j)).1)).lo := by
  exact ⟨point_lo_pos_of_unit_gap _ (parent_plane0_gap_unit i j),
    point_lo_pos_of_unit_gap _ (parent_plane1_gap_unit i j)⟩

theorem parent_plane1_accepted (i j : ℕ) :
    planeAccepted ordinaryPlane₁ ordinaryPlane₀ (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j) := by
  have ht := tLower_ge_mu i
  norm_num [planeAccepted, affineRange, Plane.sub, ordinaryPlane₀, ordinaryPlane₁]
  norm_num [PairedV2.mu] at ht
  linarith

theorem parent_plane0_not_accepted (i j : ℕ) :
    ¬ planeAccepted ordinaryPlane₀ ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j) := by
  intro h
  have htl := tLower_ge_mu i
  have hw := t_knot_width_pos i
  norm_num [planeAccepted, affineRange, Plane.sub, ordinaryPlane₀, ordinaryPlane₁] at h
  norm_num [PairedV2.mu] at htl
  linarith

theorem parent_ordinaryRanges (i j : ℕ) :
    ordinaryRanges (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j) =
    affineRange ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j) := by
  have htl := tLower_ge_mu i
  have htr := htl.trans (t_knot_width_pos i).le
  have hlo : 57 / 64 - 5 / 2 * PairedV2.tUpper i - PairedV2.uUpper j ≤
      1 / 2 - 1 / 2 * PairedV2.tUpper i - PairedV2.uUpper j := by
    norm_num [PairedV2.mu] at htr
    linarith
  have hhi : 57 / 64 - 5 / 2 * PairedV2.tLower i - PairedV2.uLower j ≤
      1 / 2 - 1 / 2 * PairedV2.tLower i - PairedV2.uLower j := by
    norm_num [PairedV2.mu] at htl
    linarith
  unfold ordinaryRanges
  rw [ordinaryPlane0_range, ordinaryPlane1_range]
  exact Prod.ext (min_eq_right hlo) (min_eq_right hhi)

theorem parent_plane1_gap_pos (i j : ℕ) :
    (affineRange ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j)).1 <
    (affineRange ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j)).2 := by
  have h := parent_plane1_gap_unit i j
  have hu : (0 : ℚ) < 1 / Q := one_div_pos.mpr Q_pos
  linarith

/-- The actual source continue test reduces to precisely this lower
argument check. In particular the equality s=2 takes the chord branch. -/
theorem parent_chord_eligible_iff (i j : ℕ) :
    chordEligible ordinaryPlane₁ ordinaryPlane₀ (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j) ↔
    2 ≤ (affineRange ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j)).1 / a := by
  have ha : (0 : ℚ) < a := by norm_num [a]
  have hne := ne_of_gt (parent_plane1_gap_pos i j)
  constructor
  · intro h
    exact (le_div_iff₀ ha).mpr h.2.1
  · intro h
    exact ⟨parent_plane1_accepted i j, (le_div_iff₀ ha).mp h, hne⟩

theorem parent_chord_crossing_skip (i j : ℕ)
    (hcross : (affineRange ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j)).1 / a < 2) :
    ¬ chordEligible ordinaryPlane₀ ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
        (PairedV2.uLower j) (PairedV2.uUpper j) ∧
    ¬ chordEligible ordinaryPlane₁ ordinaryPlane₀ (PairedV2.tLower i) (PairedV2.tUpper i)
        (PairedV2.uLower j) (PairedV2.uUpper j) := by
  exact ⟨fun h => parent_plane0_not_accepted i j h.1,
    fun h => (not_le_of_gt hcross) ((parent_chord_eligible_iff i j).mp h)⟩

/-- Global s-range for every actual parent; the selected E1 mask's tighter
9/4 upper endpoint is a separate data claim and is not needed here. -/
theorem parent_s_range {i j : ℕ} (hi : i < 512) (hj : j < 512) :
    1 < (affineRange ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j)).1 / a ∧
    (affineRange ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j)).2 / a < 4 := by
  have htr := tUpper_le_d hi
  have hur := uUpper_le_h hj
  have htl := tLower_ge_mu i
  have hul := uLower_ge_a j
  have ha : (0 : ℚ) < a := by norm_num [a]
  constructor
  · apply (one_lt_div ha).mpr
    norm_num [affineRange, ordinaryPlane₁, a]
    norm_num [PairedV2.d] at htr
    norm_num [PairedV2.h] at hur
    linarith
  · apply (div_lt_iff₀ ha).mpr
    norm_num [affineRange, ordinaryPlane₁, a]
    norm_num [PairedV2.mu] at htl
    norm_num [PairedV2.a] at hul
    linarith

def parentDefectQuery (i j : ℕ) : I80 :=
  let rr := ordinaryRanges (PairedV2.tLower i) (PairedV2.tUpper i)
    (PairedV2.uLower j) (PairedV2.uUpper j)
  I80.ofEnclosure ⟨rr.1 / a, rr.2 / a⟩

/-- A strict crossing triggers the exact rounded source defect guard,
independently of any values stored in the defect bank. -/
theorem parent_crossing_defect_zero (i j : ℕ) (g : ℕ) (table : ℤ → ℤ)
    (hcross : (affineRange ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j)).1 / a < 2) :
    defectLookup g table (parentDefectQuery i j) true = I80.raw 0 := by
  apply defectLookup_lower_crossing
  change ⌊((ordinaryRanges (PairedV2.tLower i) (PairedV2.tUpper i)
    (PairedV2.uLower j) (PairedV2.uUpper j)).1 / a) * Q⌋ < 2 * (Q : ℤ)
  apply Int.floor_lt.mpr
  rw [parent_ordinaryRanges]
  have h := mul_lt_mul_of_pos_right hcross Q_pos
  exact_mod_cast h

/-- The E0 upper-range condition forces a STRICT lower-range crossing
because the original knots are separated. Thus an upper endpoint exactly
at two is still on the source's skip side, without using a zero-width cell. -/
theorem parent_upper_le_two_strict_skip (i j : ℕ) (g : ℕ) (table : ℤ → ℤ)
    (hupper : (affineRange ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j)).2 / a ≤ 2) :
    (affineRange ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j)).1 / a < 2 ∧
    (¬ chordEligible ordinaryPlane₀ ordinaryPlane₁ (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j) ∧
      ¬ chordEligible ordinaryPlane₁ ordinaryPlane₀ (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j)) ∧
    defectLookup g table (parentDefectQuery i j) true = I80.raw 0 := by
  have ha : (0 : ℚ) < a := by norm_num [a]
  have hs := (div_lt_div_iff_of_pos_right ha).mpr (parent_plane1_gap_pos i j)
  have hcross := hs.trans_le hupper
  exact ⟨hcross, parent_chord_crossing_skip i j hcross,
    parent_crossing_defect_zero i j g table hcross⟩

/-- Concrete consumer: the previously explicit hden0/hden1 assumptions
are eliminated for every actual paired512 parent. Remaining licences are
the actual backend sf/log enclosures, not a target floor or row output. -/
theorem parent_savedOrdinaryRectangle_actual_lower (sf logI : ℚ → I80)
    (i j : ℕ) (_hi : i < 512) (_hj : j < 512)
    (hsf : ∀ q : ℚ, (sf q).Contains (actualExtendedThirdLowerFactor (q : ℝ)))
    (hlogT : (logI (PairedV2.tUpper i / PairedV2.tLower i)).Contains
      (Real.log ((PairedV2.tUpper i / PairedV2.tLower i : ℚ) : ℝ)))
    (hlogU : (logI (PairedV2.uUpper j / PairedV2.uLower j)).Contains
      (Real.log ((PairedV2.uUpper j / PairedV2.uLower j : ℚ) : ℝ))) :
    ((((savedOrdinaryRectangle sf logI (PairedV2.tLower i) (PairedV2.tUpper i)
      (PairedV2.uLower j) (PairedV2.uUpper j) : ℤ) : ℚ) / Q : ℚ) : ℝ) ≤
      P2SavedFloorSemantics.ordinaryCellIntegral (PairedV2.tLower i : ℝ) (PairedV2.tUpper i : ℝ)
        (PairedV2.uLower j : ℝ) (PairedV2.uUpper j : ℝ) := by
  have htl : (0 : ℚ) < PairedV2.tLower i :=
    (by norm_num [PairedV2.mu] : (0 : ℚ) < PairedV2.mu).trans_le (tLower_ge_mu i)
  have hul : (0 : ℚ) < PairedV2.uLower j :=
    (by norm_num [PairedV2.a] : (0 : ℚ) < PairedV2.a).trans_le (uLower_ge_a j)
  have hden := parent_chord_divisors_positive i j
  apply P2HistoricQ80OrdinaryEstimatorSoundness.savedOrdinaryRectangle_actual_lower sf logI
    (PairedV2.tLower i) (PairedV2.tUpper i) (PairedV2.uLower j) (PairedV2.uUpper j)
    (by exact_mod_cast htl) (by exact_mod_cast hul)
    (t_knot_width_pos i).le (u_knot_width_pos j).le (tLower_ge_mu i) hsf hlogT hlogU
  · exact fun _ => hden.1
  · exact fun _ => hden.2

end

end ImbalancedChen.P2HistoricChordDivisorGuard
