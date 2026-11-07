import ImbalancedChen.P2HistoricDefectIntegralMeasurability
import ImbalancedChen.P2HistoricOrdinaryParentClosed
import ImbalancedChen.P2HistoricChordDivisorGuard

/-!
SOURCE_WRITTEN_UNCOMPILED. Full author pair_cell = positive ordinary
proof-choice + positive defect. The complete saved integer is NOT bound
by the ordinary integral alone. Actual sf/log backends are already closed
by the imported source modules. The only analytic table input below is a
licence for the 200 ACTUAL copied h-bank entries at their right endpoints.
No final saved-output lower bound, numerical loss sum or gain is a premise.
-/

namespace ImbalancedChen.P2HistoricSavedOrdinaryDefectAssembly

noncomputable section

open Set MeasureTheory Wu2008DoubleSieve
open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricBackendTypeAdapters
open Certificates.PairedV2
open P2SavedFloorSemantics P2SavedFloorSubdivisionEstimator
open P2HistoricQ80OrdinaryEstimatorSoundness P2HistoricDefectIntegralMeasurability
open P2HistoricOrdinaryParentClosed
open scoped Interval

def bankCellRight (k : ℤ) : ℚ := 1 + ((k : ℚ) + 1) / 50

/-- Exactly the 200 historical h-bank entries. Entries whose right
endpoint is below two require no lower-h licence. This proposition is
NOT an enclosure of a query, saved integer, integral or final gain. -/
def BankEndpointLicences (δ : ℝ) : Prop :=
  ∀ k : ℤ, 0 ≤ k → k ≤ 199 → 2 ≤ (bankCellRight k : ℝ) →
    decodeQ80 (bankLowerTable k) ≤ P2TableActionSourceOnly.h δ (bankCellRight k : ℝ)

private theorem getD_nonneg (xs : List ℤ) (hxs : ∀ z ∈ xs, 0 ≤ z) (n : ℕ) :
    0 ≤ (xs[n]?).getD 0 := by
  induction xs generalizing n with
  | nil => simp
  | cons z xs ih =>
    cases n with
    | zero => simpa using hxs z (by simp)
    | succ n =>
      simpa using ih (fun w hw => hxs w (by simp [hw])) n

theorem bankLowerNumerators_nonneg : ∀ z ∈ bankLowerNumerators, 0 ≤ z := by
  norm_num [bankLowerNumerators]

theorem bankLowerTable_nonneg (k : ℤ) : 0 ≤ bankLowerTable k :=
  getD_nonneg bankLowerNumerators bankLowerNumerators_nonneg k.toNat

theorem bankSlice_nonneg (start stop : ℤ) : 0 ≤ closedSliceMin bankLowerTable start stop := by
  unfold closedSliceMin
  apply le_foldr_min
  · exact bankLowerTable_nonneg start
  · intro z hz
    rcases List.mem_map.mp hz with ⟨n, _hn, rfl⟩
    exact bankLowerTable_nonneg (start+n)

theorem bankDefectLookup_nonneg (x : I80) : 0 ≤ (bankDefectLookup x).lo := by
  unfold bankDefectLookup defectLookup
  split_ifs
  · exact le_rfl
  · exact bankSlice_nonneg _ _

theorem bankDefectLookup_raw (x : I80) :
    bankDefectLookup x = I80.raw (bankDefectLookup x).lo := by
  unfold bankDefectLookup defectLookup
  split_ifs <;> rfl

theorem bankDefectLookup_contains_decode (x : I80) :
    (bankDefectLookup x).Contains ((bankDefectLookup x).decodeLo : ℝ) := by
  have he := bankDefectLookup_raw x
  rw [he]
  exact I80.raw_contains _

private theorem scaledLo_decode (x : I80) : scaledLo 50 x = (x.decodeLo - 1) * 50 := by
  unfold scaledLo I80.decodeLo
  field_simp [Q_ne_zero]
  <;> ring

private theorem scaledHi_decode (x : I80) : scaledHi 50 x = (x.decodeHi - 1) * 50 := by
  unfold scaledHi I80.decodeHi
  field_simp [Q_ne_zero]
  <;> ring

/-- The selected final closed cell has right endpoint at least the rounded
query upper endpoint. Capping at cell199 preserves equality at s=5. -/
theorem lookupStop_right_covers (x : I80) (hguard : ¬ lookupGuard x true) :
    x.decodeHi ≤ bankCellRight (lookupStop 50 x) := by
  have hhi : x.hi ≤ 5*(Q:ℤ) := by
    by_contra hn
    exact hguard (Or.inr (Or.inl (lt_of_not_ge hn)))
  have hhiQ : (x.hi:ℚ) ≤ 5*(Q:ℚ) := by exact_mod_cast hhi
  have hdecode : x.decodeHi ≤ 5 := (div_le_iff₀ Q_pos).mpr hhiQ
  have htop : scaledHi 50 x ≤ 200 := by rw [scaledHi_decode]; linarith
  have hs : scaledHi 50 x ≤ ((lookupStop 50 x : ℤ):ℚ) + 1 := by
    unfold lookupStop
    simp only [show 4*(50:ℤ)-1=199 by norm_num]
    rcases le_total (199:ℤ) ⌊scaledHi 50 x⌋ with h | h
    · rw [min_eq_left h]
      simpa using htop
    · rw [min_eq_right h]
      exact (Int.lt_floor_add_one _).le
  rw [scaledHi_decode] at hs
  unfold bankCellRight
  linarith

theorem lookupStop_endpoint_domain (x : I80) (horder : x.lo ≤ x.hi)
    (hguard : ¬ lookupGuard x true) :
    0 ≤ lookupStop 50 x ∧ lookupStop 50 x ≤ 199 ∧
      2 ≤ bankCellRight (lookupStop 50 x) ∧ bankCellRight (lookupStop 50 x) ≤ 5 := by
  have hnonempty := lookupStart_le_stop 50 x true (by norm_num) horder hguard
  have hk0 : 0 ≤ lookupStop 50 x :=
    (show 0 ≤ lookupStart 50 x from le_max_left _ _).trans hnonempty
  have hk199 : lookupStop 50 x ≤ 199 := min_le_left _ _
  have hlo : 2*(Q:ℤ) ≤ x.lo := by
    by_contra hn
    exact hguard (Or.inr (Or.inr ⟨rfl,lt_of_not_ge hn⟩))
  have hloQ : 2*(Q:ℚ) ≤ (x.lo:ℚ) := by exact_mod_cast hlo
  have hdecode : 2 ≤ x.decodeLo := (le_div_iff₀ Q_pos).mpr hloQ
  have hs0 : 50 ≤ scaledLo 50 x := by rw [scaledLo_decode]; linarith
  have hindices := (lookup_indices_iff 50 x (lookupStop 50 x)).mp ⟨hnonempty,le_rfl⟩
  have hkRight : 2 ≤ bankCellRight (lookupStop 50 x) := by
    unfold bankCellRight
    linarith [hindices.2.2.1]
  have hkRight5 : bankCellRight (lookupStop 50 x) ≤ 5 := by
    have hkQ : ((lookupStop 50 x:ℤ):ℚ) ≤ 199 := by exact_mod_cast hk199
    unfold bankCellRight
    linarith
  exact ⟨hk0,hk199,hkRight,hkRight5⟩

/-- Licences for the actual 200 endpoints propagate through the exact
source slice minimum to an actual h endpoint. Guards yield literal zero. -/
theorem bankDefectLookup_endpoint_sound {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hbank : BankEndpointLicences δ) (x : I80) (horder : x.lo ≤ x.hi)
    (hs2 : 2 ≤ s) (hs5 : s ≤ 5) (hs : s ≤ (x.decodeHi : ℝ)) :
    ((bankDefectLookup x).decodeLo : ℝ) ≤ P2TableActionSourceOnly.h δ s := by
  by_cases hguard : lookupGuard x true
  · have hn := wuImprovementLimit_nonneg false hδ (by linarith : δ < 1/2)
      (by linarith : 1 ≤ s) (by linarith : s ≤ 10)
    simpa [bankDefectLookup,defectLookup,hguard,I80.raw,I80.decodeLo] using hn
  · let k : ℤ := lookupStop 50 x
    have hk := lookupStop_endpoint_domain x horder hguard
    have hstart := lookupStart_le_stop 50 x true (by norm_num) horder hguard
    have hmin : (bankDefectLookup x).lo ≤ bankLowerTable k := by
      simpa [bankDefectLookup,defectLookup,hguard,k,I80.raw] using
        closedSliceMin_le bankLowerTable (lookupStart 50 x) (lookupStop 50 x)
          (lookupStop 50 x) hstart le_rfl
    have hminQ : ((bankDefectLookup x).lo:ℚ)/Q ≤ (bankLowerTable k:ℚ)/Q :=
      div_le_div_of_nonneg_right (by exact_mod_cast hmin) Q_pos.le
    have hminR : ((bankDefectLookup x).decodeLo:ℝ) ≤ decodeQ80 (bankLowerTable k) := by
      exact_mod_cast hminQ
    have hright2 : (2:ℝ) ≤ (bankCellRight k:ℝ) := by exact_mod_cast hk.2.2.1
    have hright5 : (bankCellRight k:ℝ) ≤ 5 := by exact_mod_cast hk.2.2.2
    have hcoverQ := lookupStop_right_covers x hguard
    have hcoverR : (x.decodeHi:ℝ) ≤ (bankCellRight k:ℝ) := by exact_mod_cast hcoverQ
    have hlic := hbank k hk.1 hk.2.1 hright2
    have hmono := wuImprovementLimit_lower_antitone hδ hδhi
      ⟨hs2,by linarith : s ≤ 10⟩ ⟨hright2,by linarith : (bankCellRight k:ℝ) ≤ 10⟩
      (hs.trans hcoverR)
    exact hminR.trans (hlic.trans hmono)

end

end ImbalancedChen.P2HistoricSavedOrdinaryDefectAssembly
