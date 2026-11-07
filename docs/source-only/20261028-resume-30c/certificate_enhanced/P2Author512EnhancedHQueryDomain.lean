import ImbalancedChen.P2Author512EnhancedChordDomain

/-!
SOURCE ONLY; UNCOMPILED; ZERO FORMAL CREDIT.

Actual enhanced h-to-mu author-512 queries live above s=3 and below s=4.1.
This proves their residual bounds, outward query ordering/coverage, literal
passed lower guard, positive residual divisor, and closed-knot two-cell
semantics. Only the real endpoint licences for actual stop cells 100..154
remain analytic inputs. They are not proved by copying the bank integers.
The final statement combines the genuine enhanced ordinary and h integrals
for the same actual pair_cell. It supplies no full selected-output fold.
-/

namespace ImbalancedChen.P2Author512EnhancedHQueryDomain

noncomputable section

open Set MeasureTheory Wu2008DoubleSieve
open Certificates.P2DirectedLogRounding
open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricI80DivisionSoundness
open P2SavedFloorSemantics
open P2HistoricQ80OrdinaryEstimatorSoundness
open P2HistoricOrdinaryParentClosed
open P2HistoricSavedOrdinaryDefectAssembly
open P2Author512EnhancedPairCell
open P2Author512EnhancedPairCellActualBindings
open P2Author512EnhancedCellGeometry
open P2Author512EnhancedDefectIntegrability
open P2Author512EnhancedDefectLogMass
open P2Author512EnhancedOrdinaryIntegral
open P2Author512EnhancedChordDomain
open scoped Interval

def wholeEnhancedBox : PairBox :=
  { tl := h, tr := mu, ul := a, ur := h, enhance := true, diagonal := false,
    diagonalMatch := by intro hf; contradiction }

def wholeRange : ℚ × ℚ := pairRanges wholeEnhancedBox

def actualRange (i j : Fin authorPairs) : ℚ × ℚ := pairRanges (enhancedL6Box i j)

def actualQuery (i j : Fin authorPairs) : I80 :=
  I80.ofEnclosure ⟨(actualRange i j).1/a,(actualRange i j).2/a⟩

/-- The exact whole enhanced rectangle admits a uniform one-ulp margin
below 4.1, and has lower normalized residual at least three. -/
theorem whole_range_bounds :
    3*a ≤ wholeRange.1 ∧
    wholeRange.1 ≤ wholeRange.2 ∧
    wholeRange.2/a + 1/(Q:ℚ) < 41/10 ∧
    1/(Q:ℚ) ≤ wholeRange.1 := by
  norm_num [wholeRange,wholeEnhancedBox,pairRanges,ordinaryRanges,
    affineRange,ordinaryPlane₀,ordinaryPlane₁,enhancedPlane₀,enhancedPlane₁,
    singletonPlane,a,h,mu,Q]

private theorem signed_coordinate_nested (m L R l r : ℚ)
    (hL : L ≤ l) (hR : r ≤ R) :
    m*(if 0 ≤ m then L else R) ≤ m*(if 0 ≤ m then l else r) ∧
    m*(if 0 ≤ m then r else l) ≤ m*(if 0 ≤ m then R else L) := by
  by_cases hm : 0 ≤ m
  · simp only [if_pos hm]
    exact ⟨mul_le_mul_of_nonneg_left hL hm,mul_le_mul_of_nonneg_left hR hm⟩
  · have hm0 : m ≤ 0 := (lt_of_not_ge hm).le
    simp only [if_neg hm]
    exact ⟨mul_le_mul_of_nonpos_left hR hm0,mul_le_mul_of_nonpos_left hL hm0⟩

/-- Signed corner ranges narrow under an actual rectangle inclusion. -/
theorem affine_range_nested (p : Plane) (b B : PairBox)
    (htl : B.tl ≤ b.tl) (htr : b.tr ≤ B.tr)
    (hul : B.ul ≤ b.ul) (hur : b.ur ≤ B.ur) :
    (affineRange p B.tl B.tr B.ul B.ur).1 ≤
      (affineRange p b.tl b.tr b.ul b.ur).1 ∧
    (affineRange p b.tl b.tr b.ul b.ur).2 ≤
      (affineRange p B.tl B.tr B.ul B.ur).2 := by
  have hb := signed_coordinate_nested p.b B.tl B.tr b.tl b.tr htl htr
  have hd := signed_coordinate_nested p.d B.ul B.ur b.ul b.ur hul hur
  exact ⟨add_le_add (add_le_add_left hb.1 p.c) hd.1,
    add_le_add (add_le_add_left hb.2 p.c) hd.2⟩

theorem enhanced_pairRanges_nested (b B : PairBox)
    (hb : b.enhance = true) (hB : B.enhance = true)
    (htl : B.tl ≤ b.tl) (htr : b.tr ≤ B.tr)
    (hul : B.ul ≤ b.ul) (hur : b.ur ≤ B.ur) :
    (pairRanges B).1 ≤ (pairRanges b).1 ∧ (pairRanges b).2 ≤ (pairRanges B).2 := by
  have h0 := affine_range_nested ordinaryPlane₀ b B htl htr hul hur
  have h1 := affine_range_nested ordinaryPlane₁ b B htl htr hul hur
  have he0 := affine_range_nested enhancedPlane₀ b B htl htr hul hur
  have he1 := affine_range_nested enhancedPlane₁ b B htl htr hul hur
  have hs := affine_range_nested singletonPlane b B htl htr hul hur
  simp only [pairRanges,hb,hB,if_true,ordinaryRanges]
  exact ⟨max_le_max (min_le_min h0.1 h1.1)
      (max_le_max (min_le_min he0.1 he1.1) hs.1),
    max_le_max (min_le_min h0.2 h1.2)
      (max_le_max (min_le_min he0.2 he1.2) hs.2)⟩

/-- The actual Fin512 indices stay inside the common physical parent. -/
theorem actual_box_in_whole (i j : Fin authorPairs) :
    h ≤ (enhancedL6Box i j).tl ∧ (enhancedL6Box i j).tr ≤ mu ∧
    a ≤ (enhancedL6Box i j).ul ∧ (enhancedL6Box i j).ur ≤ h := by
  rcases actual_box_edges i j with ⟨htl,htr,hul,hur⟩
  have hi0 : (0:ℚ) ≤ (i.val:ℚ) := Nat.cast_nonneg _
  have hj0 : (0:ℚ) ≤ (j.val:ℚ) := Nat.cast_nonneg _
  have hi : (i.val:ℚ)+1 ≤ (authorPairs:ℚ) := by
    exact_mod_cast Nat.succ_le_of_lt i.isLt
  have hj : (j.val:ℚ)+1 ≤ (authorPairs:ℚ) := by
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  have htscale : (authorPairs:ℚ)*tStep = mu-h := by
    dsimp [tStep,authorPairs]
    ring
  have huscale : (authorPairs:ℚ)*uStep = h-a := by
    dsimp [uStep,authorPairs]
    ring
  rw [htl,htr,hul,hur]
  refine ⟨le_add_of_nonneg_right (mul_nonneg hi0 tStep_pos.le),?_,
    le_add_of_nonneg_right (mul_nonneg hj0 uStep_pos.le),?_⟩
  · calc
      h+((i.val:ℚ)+1)*tStep ≤ h+(authorPairs:ℚ)*tStep :=
        add_le_add_left (mul_le_mul_of_nonneg_right hi tStep_pos.le) h
      _ = mu := by rw [htscale]; ring
  · calc
      a+((j.val:ℚ)+1)*uStep ≤ a+(authorPairs:ℚ)*uStep :=
        add_le_add_left (mul_le_mul_of_nonneg_right hj uStep_pos.le) a
      _ = h := by rw [huscale]; ring

/-- Concrete residual ranges, including their source order, not a new
abstract range supplier. -/
theorem actual_range_bounds (i j : Fin authorPairs) :
    3*a ≤ (actualRange i j).1 ∧
    (actualRange i j).1 ≤ (actualRange i j).2 ∧
    (actualRange i j).2 ≤ wholeRange.2 := by
  rcases actual_box_in_whole i j with ⟨htl,htr,hul,hur⟩
  have hn := enhanced_pairRanges_nested (enhancedL6Box i j) wholeEnhancedBox
    rfl rfl htl htr hul hur
  rcases actual_box_positive_ordered i j with ⟨_ht0,_hu0,ht,hu⟩
  have hr := enhanced_residual_in_pairRanges (enhancedL6Box i j) rfl
    (t := ((enhancedL6Box i j).tl:ℝ)) (u := ((enhancedL6Box i j).ul:ℝ))
    ⟨le_rfl,by exact_mod_cast ht⟩ ⟨le_rfl,by exact_mod_cast hu⟩
  refine ⟨whole_range_bounds.1.trans hn.1,?_,hn.2⟩
  exact_mod_cast hr.1.trans hr.2

/-- The actual outward query encloses the exact residual/a interval;
its integer endpoints are ordered as well. -/
theorem actual_query_rounding (i j : Fin authorPairs) :
    (actualQuery i j).lo ≤ (actualQuery i j).hi ∧
    (actualQuery i j).decodeLo ≤ (actualRange i j).1/a ∧
    (actualRange i j).2/a ≤ (actualQuery i j).decodeHi := by
  let E : Enclosure := ⟨(actualRange i j).1/a,(actualRange i j).2/a⟩
  have hl := (I80.lower_rounding E).1
  have hu := (I80.upper_rounding E).1
  change 0 ≤ (actualRange i j).1/a-(actualQuery i j).decodeLo at hl
  change 0 ≤ (actualQuery i j).decodeHi-(actualRange i j).2/a at hu
  have ha : (0:ℚ)<a := by norm_num [a]
  have hr := div_le_div_of_nonneg_right (actual_range_bounds i j).2.1 ha.le
  have hq : (actualQuery i j).decodeLo ≤ (actualQuery i j).decodeHi := by linarith
  have hqi : ((actualQuery i j).lo:ℚ) ≤ (actualQuery i j).hi :=
    (div_le_div_iff_of_pos_right Q_pos).mp hq
  exact ⟨by exact_mod_cast hqi,by linarith,by linarith⟩

theorem scaled_query_identity (x : I80) :
    scaledLo 50 x = (x.decodeLo-1)*50 ∧
      scaledHi 50 x = (x.decodeHi-1)*50 := by
  constructor
  · unfold scaledLo I80.decodeLo
    field_simp [Q_ne_zero] <;> ring
  · unfold scaledHi I80.decodeHi
    field_simp [Q_ne_zero] <;> ring

/-- Rounding cannot activate either source endpoint refusal on this
particular h-to-mu parent. Generic boxes crossing two are a separate case. -/
theorem actual_query_domain (i j : Fin authorPairs) :
    3 ≤ (actualQuery i j).decodeLo ∧
    (actualQuery i j).decodeHi < 41/10 ∧
    ¬ lookupGuard (actualQuery i j) true := by
  have ha : (0:ℚ)<a := by norm_num [a]
  have hs3 : (3:ℚ) ≤ (actualRange i j).1/a :=
    (le_div_iff₀ ha).mpr (actual_range_bounds i j).1
  have hlo : 3*(Q:ℤ) ≤ (actualQuery i j).lo := by
    apply Int.le_floor.mpr
    have hm := mul_le_mul_of_nonneg_right hs3 Q_pos.le
    simpa only [Int.cast_mul,Int.cast_ofNat,Int.cast_natCast] using hm
  have hloQ : 3*(Q:ℚ) ≤ ((actualQuery i j).lo:ℚ) := by exact_mod_cast hlo
  have hdecode3 : (3:ℚ) ≤ (actualQuery i j).decodeLo :=
    (le_div_iff₀ Q_pos).mpr hloQ
  have herr := (I80.upper_rounding
    (⟨(actualRange i j).1/a,(actualRange i j).2/a⟩:Enclosure)).2
  have hupper := div_le_div_of_nonneg_right (actual_range_bounds i j).2.2 ha.le
  have hdecode41 : (actualQuery i j).decodeHi < (41/10:ℚ) := by
    change (actualQuery i j).decodeHi-(actualRange i j).2/a < 1/(Q:ℚ) at herr
    linarith [whole_range_bounds.2.2.1]
  have hdecode5 : (actualQuery i j).decodeHi ≤ 5 := by linarith
  have hhiQ : ((actualQuery i j).hi:ℚ) ≤ 5*(Q:ℚ) :=
    (div_le_iff₀ Q_pos).mp hdecode5
  have hhi : (actualQuery i j).hi ≤ 5*(Q:ℤ) := by exact_mod_cast hhiQ
  have hQ0 : (0:ℤ) ≤ (Q:ℤ) := Nat.cast_nonneg _
  refine ⟨hdecode3,hdecode41,?_⟩
  unfold lookupGuard
  omega

/-- Only these 55 copied bank endpoints can be the actual last selected
closed cell. This is derived from the physical query and Q80 rounding. -/
theorem actual_stop_range (i j : Fin authorPairs) :
    100 ≤ lookupStop 50 (actualQuery i j) ∧
      lookupStop 50 (actualQuery i j) ≤ 154 := by
  have hd := actual_query_domain i j
  have ho := actual_query_rounding i j
  have hs := scaled_query_identity (actualQuery i j)
  have hdecord : (actualQuery i j).decodeLo ≤ (actualQuery i j).decodeHi := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast ho.1) Q_pos.le
  have hscale100 : (100:ℚ) ≤ scaledHi 50 (actualQuery i j) := by
    rw [hs.2]
    linarith
  have hscale155 : scaledHi 50 (actualQuery i j) < (155:ℚ) := by
    rw [hs.2]
    linarith
  have hflo : (100:ℤ) ≤ ⌊scaledHi 50 (actualQuery i j)⌋ :=
    Int.le_floor.mpr (by simpa using hscale100)
  have hfhi : ⌊scaledHi 50 (actualQuery i j)⌋ < (155:ℤ) :=
    Int.floor_lt.mpr (by simpa using hscale155)
  unfold lookupStop
  constructor
  · exact le_min (by norm_num) hflo
  · exact (min_le_right _ _).trans (by omega)

/-- Any interior exact knot covered by the unrounded actual query keeps
both adjoining closed cells after outward rounding. No floor-only query
is substituted for the source ceil(...)-1 left edge. -/
theorem actual_query_knot_both_cells (i j : Fin authorPairs) (k : ℤ)
    (hk : 1 ≤ k) (hk199 : k ≤ 199)
    (hleft : (actualRange i j).1/a ≤ 1+(k:ℚ)/50)
    (hright : 1+(k:ℚ)/50 ≤ (actualRange i j).2/a) :
    (lookupStart 50 (actualQuery i j) ≤ k-1 ∧
      k-1 ≤ lookupStop 50 (actualQuery i j)) ∧
    (lookupStart 50 (actualQuery i j) ≤ k ∧
      k ≤ lookupStop 50 (actualQuery i j)) := by
  have hr := actual_query_rounding i j
  have hs := scaled_query_identity (actualQuery i j)
  have hlo : scaledLo 50 (actualQuery i j) ≤ (k:ℚ) := by
    rw [hs.1]
    linarith [hr.2.1.trans hleft]
  have hhi : (k:ℚ) ≤ scaledHi 50 (actualQuery i j) := by
    rw [hs.2]
    linarith [hright.trans hr.2.2]
  constructor
  · apply (lookup_indices_iff 50 (actualQuery i j) (k-1)).mpr
    push_cast
    exact ⟨by omega,by omega,by linarith,by linarith⟩
  · apply (lookup_indices_iff 50 (actualQuery i j) k).mpr
    exact ⟨by omega,by simpa using hk199,by linarith,hhi⟩

/-- The actual integer lookup is below both copied adjoining entries,
including equality at a knot. This proves lookup semantics, not the
unproved analytic size of either copied bank entry. -/
theorem actual_lookup_knot_min (i j : Fin authorPairs) (k : ℤ)
    (hk : 1 ≤ k) (hk199 : k ≤ 199)
    (hleft : (actualRange i j).1/a ≤ 1+(k:ℚ)/50)
    (hright : 1+(k:ℚ)/50 ≤ (actualRange i j).2/a) :
    (actualHLookup (actualQuery i j)).lo ≤
      min (bankLowerTable (k-1)) (bankLowerTable k) := by
  have hc := actual_query_knot_both_cells i j k hk hk199 hleft hright
  have hg := (actual_query_domain i j).2.2
  apply le_min
  · simpa only [actualHLookup,defectLookup,hg,if_false,I80.raw] using
      closedSliceMin_le bankLowerTable
        (lookupStart 50 (actualQuery i j)) (lookupStop 50 (actualQuery i j))
        (k-1) hc.1.1 hc.1.2
  · simpa only [actualHLookup,defectLookup,hg,if_false,I80.raw] using
      closedSliceMin_le bankLowerTable
        (lookupStart 50 (actualQuery i j)) (lookupStop 50 (actualQuery i j))
        k hc.2.1 hc.2.2

/-- This restriction still consists of genuine copied-bank analytic
endpoint licences. No output, query, cell integral or final gain is its
premise. This file does not prove these 55 numerical inequalities. -/
def EnhancedEndpointLicences (δ : ℝ) : Prop :=
  ∀ k : ℤ, 100 ≤ k → k ≤ 154 →
    decodeQ80 (bankLowerTable k) ≤ P2TableActionSourceOnly.h δ (bankCellRight k:ℝ)

theorem enhanced_endpoint_licences_of_bank {δ : ℝ}
    (hbank : BankEndpointLicences δ) : EnhancedEndpointLicences δ := by
  intro k hk h154
  apply hbank k (by omega) (by omega)
  have hkQ : (100:ℚ) ≤ (k:ℚ) := by exact_mod_cast hk
  have hrat : (2:ℚ) ≤ bankCellRight k := by
    unfold bankCellRight
    linarith
  exact_mod_cast hrat

/-- Exact actual query endpoint comparison under only its 55 possible
original-bank endpoint licences. The whole200 premise is no longer used. -/
theorem actual_h_endpoint_lower {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hbank : EnhancedEndpointLicences δ)
    (i j : Fin authorPairs) :
    ((actualHLookup (actualQuery i j)).decodeLo:ℝ) ≤
      P2TableActionSourceOnly.h δ (((actualRange i j).2/a:ℚ):ℝ) := by
  let x := actualQuery i j
  let k := lookupStop 50 x
  have hg : ¬ lookupGuard x true := (actual_query_domain i j).2.2
  have ho : x.lo ≤ x.hi := (actual_query_rounding i j).1
  have hk := actual_stop_range i j
  have hdom := lookupStop_endpoint_domain x ho hg
  have hstart := lookupStart_le_stop 50 x true (by norm_num) ho hg
  have hmin : (actualHLookup x).lo ≤ bankLowerTable k := by
    simpa only [actualHLookup,defectLookup,hg,if_false,I80.raw,k] using
      closedSliceMin_le bankLowerTable (lookupStart 50 x) (lookupStop 50 x)
        (lookupStop 50 x) hstart le_rfl
  have hminQ : ((actualHLookup x).lo:ℚ)/Q ≤ (bankLowerTable k:ℚ)/Q :=
    div_le_div_of_nonneg_right (by exact_mod_cast hmin) Q_pos.le
  have hminR : ((actualHLookup x).decodeLo:ℝ) ≤ decodeQ80 (bankLowerTable k) := by
    exact_mod_cast hminQ
  have ha : (0:ℚ)<a := by norm_num [a]
  have hs3 : (3:ℚ) ≤ (actualRange i j).2/a :=
    (le_div_iff₀ ha).mpr ((actual_range_bounds i j).1.trans
      (actual_range_bounds i j).2.1)
  have hs2 : (2:ℝ) ≤ (((actualRange i j).2/a:ℚ):ℝ) := by
    exact_mod_cast (show (2:ℚ) ≤ (actualRange i j).2/a by linarith)
  have hs5 : (((actualRange i j).2/a:ℚ):ℝ) ≤ 5 := by
    have hsQ := div_le_div_of_nonneg_right (actual_range_bounds i j).2.2 ha.le
    have ht : (actualRange i j).2/a ≤ (5:ℚ) := by
      linarith [whole_range_bounds.2.2.1,show (0:ℚ)<1/(Q:ℚ) by positivity]
    exact_mod_cast ht
  have hright2 : (2:ℝ) ≤ (bankCellRight k:ℝ) := by exact_mod_cast hdom.2.2.1
  have hright5 : (bankCellRight k:ℝ) ≤ 5 := by exact_mod_cast hdom.2.2.2
  have hcoverQ : (actualRange i j).2/a ≤ bankCellRight k :=
    (actual_query_rounding i j).2.2.trans (lookupStop_right_covers x hg)
  have hcoverR : (((actualRange i j).2/a:ℚ):ℝ) ≤ (bankCellRight k:ℝ) := by
    exact_mod_cast hcoverQ
  have hmono := wuImprovementLimit_lower_antitone hδ hδhi
    ⟨hs2,by linarith⟩ ⟨hright2,by linarith⟩ hcoverR
  exact hminR.trans ((hbank k hk.1 hk.2).trans hmono)

/-- Every purely geometric/query/division premise of the earlier actual
h-defect leaf is discharged on the literal enhanced grid. -/
theorem actual_defect_geometric_guards (i j : Fin authorPairs) :
    0 < ((actualRange i j).1:ℝ) ∧
    (((actualRange i j).2/a:ℚ):ℝ) ≤ 5 ∧
    (actualQuery i j).lo ≤ (actualQuery i j).hi ∧
    (((actualRange i j).2/a:ℚ):ℝ) ≤ ((actualQuery i j).decodeHi:ℝ) ∧
    0 < (I80.point (actualRange i j).2).lo := by
  have ha : (0:ℚ)<a := by norm_num [a]
  have hr := actual_range_bounds i j
  have hrl : (0:ℚ)<(actualRange i j).1 :=
    (by positivity : (0:ℚ)<3*a).trans_le hr.1
  have hhi : (actualRange i j).2/a ≤ (5:ℚ) := by
    have hs := div_le_div_of_nonneg_right hr.2.2 ha.le
    linarith [whole_range_bounds.2.2.1,show (0:ℚ)<1/(Q:ℚ) by positivity]
  have hunit : 1/(Q:ℚ) ≤ (actualRange i j).2 := by
    have hn := actual_box_in_whole i j
    have hnest := enhanced_pairRanges_nested (enhancedL6Box i j) wholeEnhancedBox
      rfl rfl hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
    exact whole_range_bounds.2.2.2.trans (hnest.1.trans hr.2.1)
  exact ⟨by exact_mod_cast hrl,by exact_mod_cast hhi,
    (actual_query_rounding i j).1,
    by exact_mod_cast (actual_query_rounding i j).2.2,
    point_lo_pos_of_one_ulp_le _ hunit⟩

/-- Actual h-defect lower comparison with every range/query/division
premise discharged and only55 genuine original-bank endpoint inequalities
left. Their numerical truth is not inferred from the actual saved output. -/
theorem actual_defect_Q80_lower {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hbank : EnhancedEndpointLicences δ)
    (i j : Fin authorPairs) :
    (((defectLower actualLog (enhancedL6Box i j):ℚ)/Q:ℚ):ℝ) ≤
      enhancedDefectIntegral δ (enhancedL6Box i j).tl (enhancedL6Box i j).tr
        (enhancedL6Box i j).ul (enhancedL6Box i j).ur := by
  let b := enhancedL6Box i j
  let hlow : ℝ := ((actualHLookup (actualQuery i j)).decodeLo:ℝ)
  rcases actual_box_positive_ordered i j with ⟨htl,hul,ht,hu⟩
  rcases actual_defect_geometric_guards i j with ⟨hrl,hhi,_horder,_hupper,hrhRound⟩
  have htR : (b.tl:ℝ) ≤ b.tr := by exact_mod_cast ht
  have huR : (b.ul:ℝ) ≤ b.ur := by exact_mod_cast hu
  have htlR : (0:ℝ)<b.tl := by exact_mod_cast htl
  have hulR : (0:ℝ)<b.ul := by exact_mod_cast hul
  have hrange : ∀ t ∈ Icc (b.tl:ℝ) b.tr, ∀ u ∈ Icc (b.ul:ℝ) b.ur,
      enhancedResidual t u ∈ Icc ((actualRange i j).1:ℝ) ((actualRange i j).2:ℝ) := by
    intro t ht' u hu'
    exact enhanced_residual_in_pairRanges b rfl ht' hu'
  have hhiR : ((actualRange i j).2:ℝ)/ordinaryA ≤ 5 := by
    simpa only [Rat.cast_div,cast_source_a] using hhi
  have hh0 : 0 ≤ hlow := by
    have hz := bankDefectLookup_nonneg (actualQuery i j)
    have hq : (0:ℚ) ≤ (actualHLookup (actualQuery i j)).decodeLo :=
      div_nonneg (by exact_mod_cast hz) Q_pos.le
    exact_mod_cast hq
  have h2aQ : 2*a ≤ (actualRange i j).1 := by
    have ha : (0:ℚ)<a := by norm_num [a]
    linarith [(actual_range_bounds i j).1]
  have h2aR : 2*ordinaryA ≤ ((actualRange i j).1:ℝ) := by
    have ht : (2:ℝ)*(a:ℝ) ≤ ((actualRange i j).1:ℝ) := by exact_mod_cast h2aQ
    simpa only [cast_source_a] using ht
  have hcross : ((actualRange i j).1:ℝ)<2*ordinaryA → hlow=0 := by
    intro hlt
    exact False.elim ((not_lt_of_ge h2aR) hlt)
  have hh : 2*ordinaryA ≤ ((actualRange i j).1:ℝ) →
      hlow ≤ P2TableActionSourceOnly.h δ (((actualRange i j).2:ℝ)/ordinaryA) := by
    intro _hlo
    simpa only [hlow,Rat.cast_div,cast_source_a] using
      actual_h_endpoint_lower hδ hδhi hbank i j
  have hp := enhanced_defect_logmass_lower hδ hδhi htlR hulR hrl htR huR
    hrange hhiR hh0 hcross hh
  have hz := enhanced_defect_integral_nonneg hδ hδhi htlR hulR hrl htR huR
    hrange hhiR
  have hfloor := actual_defect_directed b rfl htl hul ht hu hrhRound
  have hmass : rectangleMassValue b.tl b.tr b.ul b.ur =
      realMass (b.tl:ℝ) b.tr b.ul b.ur := by
    simp [rectangleMassValue,realMass]
  rw [hmass] at hfloor
  change (((defectLower actualLog b:ℚ)/Q:ℚ):ℝ) ≤
    max 0 (4*hlow*realMass b.tl b.tr b.ul b.ur/((actualRange i j).2:ℝ)) at hfloor
  exact hfloor.trans (max_le hz hp)

/-- Same actual pair_cell, genuine enhanced ordinary integral and h
integral. No geometric/query/denominator hypothesis remains. The only
unproved h input is the55 copied-bank analytic endpoint licences. -/
theorem actual_enhanced_pairCell_integral_lower {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hbank : EnhancedEndpointLicences δ)
    (i j : Fin authorPairs) :
    (((pairCellQ80 actualSf actualLog (enhancedL6Box i j):ℚ)/Q:ℚ):ℝ) ≤
      enhancedOrdinaryIntegral (enhancedL6Box i j).tl (enhancedL6Box i j).tr
        (enhancedL6Box i j).ul (enhancedL6Box i j).ur +
      enhancedDefectIntegral δ (enhancedL6Box i j).tl (enhancedL6Box i j).tr
        (enhancedL6Box i j).ul (enhancedL6Box i j).ur := by
  have ho := actual_enhanced_ordinary_Q80_lower i j
  have hd := actual_defect_Q80_lower hδ hδhi hbank i j
  have hs := add_le_add ho hd
  convert hs using 1
  simp only [pairCellQ80,Int.cast_add,add_div,Rat.cast_add]

/-- Compatibility with the preceding complete200-endpoint receiver,
without requiring those extra145 unused licences for this half-domain. -/
theorem actual_enhanced_pairCell_integral_lower_of_bank {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hbank : BankEndpointLicences δ)
    (i j : Fin authorPairs) :
    (((pairCellQ80 actualSf actualLog (enhancedL6Box i j):ℚ)/Q:ℚ):ℝ) ≤
      enhancedOrdinaryIntegral (enhancedL6Box i j).tl (enhancedL6Box i j).tr
        (enhancedL6Box i j).ul (enhancedL6Box i j).ur +
      enhancedDefectIntegral δ (enhancedL6Box i j).tl (enhancedL6Box i j).tr
        (enhancedL6Box i j).ul (enhancedL6Box i j).ur :=
  actual_enhanced_pairCell_integral_lower hδ hδhi
    (enhanced_endpoint_licences_of_bank hbank) i j

end

end ImbalancedChen.P2Author512EnhancedHQueryDomain
