import ImbalancedChen.OriginalPairedN48BuchstabQuadraticError

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Direct soundness of the ORIGINAL sourceCell and Python max-query scan.
This does not assume BridgeValid, a generic rectangle checker, QueryCover,
or the desired uniform omega bound.  The only data premise is the original
pure integer/rational SourceProducerValid, for which no array is supplied.
-/

namespace ImbalancedChen.OriginalPairedN48DirectQuerySoundness

noncomputable section
open Set
open LiLiuPrereqBuchstab
open Certificates.P2DirectedLogRounding
open OriginalN48Q112LocalProduct
open OriginalPairedKeyUniformOmegaQuery
open OriginalPairedV2Q112ParentAttachment
open P2N48ActualSixteenCostRowAttachment
open OriginalPairedN48OmegaProducerAdapter
open OriginalPairedN48OmegaStepArithmetic
open OriginalPairedN48BuchstabQuadraticError
open OriginalU2CoupledRecurrenceSourceOnly

theorem original_pointUpper_sound (p : SourceArrays) (hp : SourceProducerValid p)
    (k : ℕ) (hk : mesh ≤ k) (hkc : k < uCount) :
    buchstab ((k : ℝ) / (mesh : ℝ)) ≤ (pointUpper p k : ℝ) / (P : ℝ) := by
  have h := divided_weighted_node_contains p k hk (original_weighted_nodes p hp k hk hkc)
  simpa only [pointUpper, decode, Enclosure.Contains, Rat.cast_div,
    Rat.cast_intCast] using h.2

theorem original_bulge_rounds_outward :
    (1 : ℝ) / (4 * (mesh : ℝ) ^ 2) ≤ (bulge : ℝ) / (P : ℝ) := by
  have hP : (0 : ℝ) < (P : ℝ) := by exact_mod_cast P_pos
  have h := Int.le_ceil (P / (4 * (mesh : ℚ) ^ 2))
  have hR : (P : ℝ) / (4 * (mesh : ℝ) ^ 2) ≤ (bulge : ℝ) := by
    exact_mod_cast h
  apply (le_div_iff₀ hP).2
  calc
    ((1 : ℝ) / (4 * (mesh : ℝ) ^ 2)) * (P : ℝ) =
        (P : ℝ) / (4 * (mesh : ℝ) ^ 2) := by ring
    _ ≤ (bulge : ℝ) := hR

/-- Every full original cell uses its actual endpoint U divisions, the
quadratic h²/4 bulge, and the independently proved actual C0 cap. -/
theorem original_sourceCell_sound (p : SourceArrays) (hp : SourceProducerValid p)
    (k : ℕ) (hk : 2 * mesh ≤ k) (hkc : k + 1 < uCount)
    {x : ℝ} (hx : x ∈ Icc ((k : ℝ) / (mesh : ℝ))
      (((k + 1 : ℕ) : ℝ) / (mesh : ℝ))) :
    buchstab x ≤ (sourceCell p k : ℝ) / (P : ℝ) := by
  let a : ℝ := (k : ℝ) / (mesh : ℝ)
  let b : ℝ := ((k + 1 : ℕ) : ℝ) / (mesh : ℝ)
  let M : ℝ := (max (pointUpper p k) (pointUpper p (k + 1)) : ℝ) / (P : ℝ)
  have hm : (0 : ℝ) < mesh := by norm_num [mesh]
  have hmN : 0 < mesh := by norm_num [mesh]
  have hP : (0 : ℝ) < (P : ℝ) := by exact_mod_cast P_pos
  have ha : 2 ≤ a := by
    dsimp [a]
    apply (le_div_iff₀ hm).2
    exact_mod_cast hk
  have hw : b - a = 1 / (mesh : ℝ) := by
    dsimp [a, b]
    push_cast
    ring
  have hab : a < b := by
    have hh := one_div_pos.mpr hm
    linarith only [hw, hh]
  have hxa : a ≤ x := hx.1
  have hxb : x ≤ b := hx.2
  have hleft := original_pointUpper_sound p hp k (by omega) (by omega)
  have hright := original_pointUpper_sound p hp (k + 1) (by omega) hkc
  have hleftM : buchstab a ≤ M := by
    exact hleft.trans (div_le_div_of_nonneg_right
      (by exact_mod_cast (le_max_left (pointUpper p k) (pointUpper p (k + 1)))) hP.le)
  have hrightM : buchstab b ≤ M := by
    exact hright.trans (div_le_div_of_nonneg_right
      (by exact_mod_cast (le_max_right (pointUpper p k) (pointUpper p (k + 1)))) hP.le)
  let λ : ℝ := (b - x) / (b - a)
  let μ : ℝ := (x - a) / (b - a)
  have hg : 0 < b - a := sub_pos.mpr hab
  have hλ : 0 ≤ λ := div_nonneg (sub_nonneg.mpr hxb) hg.le
  have hμ : 0 ≤ μ := div_nonneg (sub_nonneg.mpr hxa) hg.le
  have hsum : λ + μ = 1 := by dsimp [λ, μ]; field_simp [hg.ne']; ring
  have hchord : endpointChord buchstab a b x ≤ M := by
    change λ * buchstab a + μ * buchstab b ≤ M
    calc
      λ * buchstab a + μ * buchstab b ≤ λ * M + μ * M :=
        add_le_add (mul_le_mul_of_nonneg_left hleftM hλ)
          (mul_le_mul_of_nonneg_left hrightM hμ)
      _ = M := by rw [← add_mul, hsum, one_mul]
  have hpoint := (abs_le.mp (actual_buchstab_chord_error ha hab hx)).2
  have hshape : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by
    nlinarith only [sq_nonneg (x - (a + b) / 2)]
  have hbulge : (b - a) ^ 2 / 4 ≤ (bulge : ℝ) / (P : ℝ) := by
    rw [hw]
    convert original_bulge_rounds_outward using 1
    <;> field_simp [hm.ne']
    <;> ring
  have hmeshBound : buchstab x ≤
      ((max (pointUpper p k) (pointUpper p (k + 1)) + bulge : ℤ) : ℝ) / (P : ℝ) := by
    have hh : buchstab x ≤ M + (bulge : ℝ) / (P : ℝ) := by
      linarith only [hpoint, hchord, hshape, hbulge]
    simpa only [M, Int.cast_add, add_div] using hh
  have hcap := P2SeedOmegaGlobalEnvelope.actual_buchstab_global_cap
    (show 2 ≤ x by linarith only [ha, hxa])
  have hcapC : buchstab x ≤ (C0 : ℝ) := by
    simpa only [C0, P2SeedOmegaLiteralFibre.omegaCap, Rat.cast_div,
      Rat.cast_ofNat] using hcap
  have hroundedC : (C0 : ℝ) ≤ ((rational C0).hi : ℝ) / (P : ℝ) := by
    simpa only [decode, Enclosure.Contains, Rat.cast_div, Rat.cast_intCast] using
      (rational_contains C0).2
  have hC := hcapC.trans hroundedC
  unfold sourceCell
  rw [if_neg (by omega : ¬k < 2 * mesh)]
  apply (le_div_iff₀ hP).2
  have hlo := (le_div_iff₀ hP).mp hC
  have hhi := (le_div_iff₀ hP).mp hmeshBound
  simpa only [Int.cast_min] using le_min hlo hhi

private theorem le_foldl_max_acc (xs : List ℤ) (a : ℤ) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih =>
    exact (le_max_left a x).trans (ih (max a x))

private theorem le_foldl_max_of_mem (xs : List ℤ) (a x : ℤ) (hx : x ∈ xs) :
    x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => cases hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right a y).trans (le_foldl_max_acc ys (max a y))
    · exact ih (max a y) hx

/-- Each original scanned cell is below the exact max fold.  No relation
between the original producer and a different checker is used. -/
theorem scanned_cell_le_query (p : SourceArrays) (hp : SourceProducerValid p)
    (k : ℕ) (hfirst : firstCell ≤ k) (hlast : k ≤ lastCell) (hkc : k < cellCount) :
    cellAt p k ≤ p.queryMax := by
  rcases hp with ⟨_, hlen, hquery, _, _, _, _⟩
  have hkarray : k < p.cell.length := by omega
  let xs := (p.cell.drop firstCell).take (lastCell - firstCell + 1)
  have hjdrop : k - firstCell < (p.cell.drop firstCell).length := by
    simp only [List.length_drop]
    omega
  have hjtake : k - firstCell < lastCell - firstCell + 1 := by omega
  have hj : k - firstCell < xs.length := by
    dsimp [xs]
    simp only [List.length_take]
    omega
  have hmem : cellAt p k ∈ xs := by
    refine List.mem_iff_getElem.mpr ⟨k - firstCell, hj, ?_⟩
    dsimp [xs]
    rw [List.getElem_take, List.getElem_drop]
    have he : firstCell + (k - firstCell) = k := by omega
    simp only [he, cellAt, List.getElem?_eq_getElem hkarray, Option.getD_some]
  rw [hquery]
  exact le_foldl_max_of_mem xs 0 (cellAt p k) hmem

/-- The fixed native-key query endpoints are non-grid-aligned rationals.
These are four scalar exact-rational facts, not an array/checker run. -/
theorem native_query_grid_endpoints :
    2 * mesh ≤ firstCell ∧ lastCell < cellCount ∧
      (firstCell : ℝ) ≤ (argumentLower : ℝ) * (mesh : ℝ) ∧
      (argumentUpper : ℝ) * (mesh : ℝ) < (lastCell : ℝ) + 1 := by
  norm_num [firstCell, lastCell, argumentLower, argumentUpper, mesh, cellCount]

/-- A real argument in the original query range belongs to a scanned
original cell; endpoints are included, with no grid-index offset. -/
theorem native_query_cell_cover {s : ℝ}
    (hs : s ∈ Icc (argumentLower : ℝ) (argumentUpper : ℝ)) :
    ∃ k : ℕ, firstCell ≤ k ∧ k ≤ lastCell ∧ k < cellCount ∧
      s ∈ Icc ((k : ℝ) / (mesh : ℝ)) (((k + 1 : ℕ) : ℝ) / (mesh : ℝ)) := by
  let k : ℕ := ⌊s * (mesh : ℝ)⌋₊
  have hm : (0 : ℝ) < mesh := by norm_num [mesh]
  have hs0 : 0 ≤ s := by
    have hA : (0 : ℝ) ≤ (argumentLower : ℝ) := by norm_num [argumentLower]
    exact hA.trans hs.1
  have hklo : (k : ℝ) ≤ s * (mesh : ℝ) := Nat.floor_le (mul_nonneg hs0 hm.le)
  have hkhi : s * (mesh : ℝ) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hend := native_query_grid_endpoints
  have hfirst : firstCell ≤ k :=
    Nat.le_floor (hend.2.2.1.trans (mul_le_mul_of_nonneg_right hs.1 hm.le))
  have hlastR : (k : ℝ) < (lastCell : ℝ) + 1 :=
    hklo.trans_lt ((mul_le_mul_of_nonneg_right hs.2 hm.le).trans_lt hend.2.2.2)
  have hlastN : k < lastCell + 1 := by exact_mod_cast hlastR
  have hlast : k ≤ lastCell := by omega
  have hkc : k < cellCount := hlast.trans_lt hend.2.1
  refine ⟨k, hfirst, hlast, hkc, ?_, ?_⟩
  · exact (div_le_iff₀ hm).2 hklo
  · apply (le_div_iff₀ hm).2
    push_cast
    exact hkhi.le

/-- Direct original query soundness: all analytic and cover obligations
are discharged.  Only the original finite arithmetic data validity remains. -/
theorem original_query_uniform (p : SourceArrays) (hp : SourceProducerValid p)
    {s : ℝ} (hs : s ∈ Icc (argumentLower : ℝ) (argumentUpper : ℝ)) :
    buchstab s ≤ (p.queryMax : ℝ) / (P : ℝ) := by
  obtain ⟨k, hfirst, hlast, hkc, hcell⟩ := native_query_cell_cover hs
  have hk2 : 2 * mesh ≤ k := native_query_grid_endpoints.1.trans hfirst
  have hic : k + 1 < uCount := by dsimp [uCount, cellCount] at *; omega
  have hu := original_sourceCell_sound p hp k hk2 hic hcell
  have heq := (hp.2.2.2.2.2.2 ⟨k, hkc⟩).1
  have hscan := scanned_cell_le_query p hp k hfirst hlast hkc
  rw [← heq] at hu
  exact hu.trans (div_le_div_of_nonneg_right
    (by exact_mod_cast hscan) (show (0 : ℝ) ≤ (P : ℝ) by exact_mod_cast P_pos.le))

/-- The same native saved-parent argument, rather than a proxy argument,
is now supplied with the original algorithm's uniform upper endpoint. -/
theorem original_query_on_actual_native_box (p : SourceArrays) (hp : SourceProducerValid p)
    {v : Fin 4 → ℝ} (hv : v ∈ nativeBox keySavedRow) :
    buchstab (argument v) ≤ (p.queryMax : ℝ) / (P : ℝ) :=
  original_query_uniform p hp (actual_key_box_argument_range hv)

/-- This is the original producer's point-valued upper proxy.  It is used
as an upper *constant* for omega, not asserted to enclose every omega value. -/
def originalQueryToken (p : SourceArrays) : Token := ⟨p.queryMax, p.queryMax⟩

def originalCostUpperToken (p : SourceArrays) : ℤ :=
  (omegaCostToken (originalQueryToken p)
    OriginalPairedKeyQ112UpperMassCost.keyUpperProxyPoint).hi

/-- The same original query endpoint pays K times the TRUE mass Z_B of
the same row1014347 ordered native parent.  The mass upper proxy is the
existing exact tied-parent geometry bound, not a lower estimator or a
proxy domain.  No stored historical cost endpoint is identified here. -/
theorem original_cost_upper_safe (p : SourceArrays) (hp : SourceProducerValid p) :
    P2N48SavedParentRowRecost.anchorK * ((p.queryMax : ℝ) / (P : ℝ)) *
        OriginalPairedV2Q112ParentAttachment.actualMass keySavedRow ≤
      (originalCostUpperToken p : ℝ) / (P : ℝ) := by
  have hquery0 : 0 ≤ p.queryMax := hp.2.2.2.1
  have hP : (0 : ℝ) < (P : ℝ) := by exact_mod_cast P_pos
  have hq : (0 : ℝ) ≤ (p.queryMax : ℝ) / (P : ℝ) :=
    div_nonneg (by exact_mod_cast hquery0) hP.le
  have htoken : (decode (originalQueryToken p)).Contains
      ((p.queryMax : ℝ) / (P : ℝ)) := by
    constructor <;> simp only [originalQueryToken, decode, Enclosure.Contains,
      Rat.cast_div, Rat.cast_intCast, le_refl]
  have ht := (omegaCostToken_contains (originalQueryToken p)
    OriginalPairedKeyQ112UpperMassCost.keyUpperProxyPoint htoken
    OriginalPairedKeyQ112UpperMassCost.keyUpperProxyPoint_contains_upper).2
  have hmono := mul_le_mul_of_nonneg_left
    OriginalPairedKeyQ112UpperMassCost.actual_key_mass_le_upper_token
    (mul_nonneg (by norm_num [K0] : (0 : ℝ) ≤ (K0 : ℝ)) hq)
  have hK : (K0 : ℝ) = P2N48SavedParentRowRecost.anchorK := by
    norm_num [K0, P2N48SavedParentRowRecost.anchorK]
  rw [← hK]
  exact hmono.trans (by
    simpa only [originalCostUpperToken, decode, Enclosure.Contains,
      Rat.cast_div, Rat.cast_intCast] using ht)

end
end ImbalancedChen.OriginalPairedN48DirectQuerySoundness
