import ImbalancedChen.P5ZU1011LiteralH248IntervalBounds
import ImbalancedChen.P5U6RetainedAdoptedIntegral
import ImbalancedChen.P2ContinuousSieveRational

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Directed rational rectangles for the ORIGINAL adopted sixth integrand.
The adopted LOWER h array is distinct from the upper H array used by the
imported interval module. Only its exact reachable-state GEOMETRY is reused.
All singleton adjacent-min knots, including s=2, retain their actual values.
The complete denominator is R*u*t, R=1/2-u-t. A box may cross the product
wall: the pointwise statements restrict it to the original product domain.
No cell-bound, integral, table recurrence or numerical endpoint is assumed.
-/

namespace ImbalancedChen.P5U6OriginalRationalBoxBounds

noncomputable section

open Set Classical
open scoped BigOperators
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open P5Z.U1011H248Partition
open P5U6AdoptedH248BindingSourceOnly P5U6RetainedAdoptedIntegralSourceOnly
open P2ContinuousSieveRational


def lowerAtom (i : Fin 200) : ℚ := (adoptedH248Numerators i : ℚ) / 2 ^ 80
def lowerKnot (j : Fin 201) : ℚ :=
  if h0 : j.val = 0 then lowerAtom 0
  else if hlast : j.val = 200 then lowerAtom 199
  else min (lowerAtom ⟨j.val - 1, by omega⟩) (lowerAtom ⟨j.val, by omega⟩)
def lowerValue : AtomState → ℚ
  | none => 0
  | some (.inl i) => lowerAtom i
  | some (.inr j) => lowerKnot j

theorem lowerValue_cast (b : FloorAtom) :
    (lowerValue (some b) : ℝ) = floorAtomValue adoptedH248Numerators b := by
  cases b with
  | inl i => simp only [lowerValue, lowerAtom, floorAtomValue, floorValue,
      Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
  | inr j =>
    unfold lowerValue lowerKnot floorAtomValue floorKnotValue
    split_ifs <;> simp only [lowerAtom, floorValue, Rat.cast_div,
      Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_min]

/-- The geometry's scalar state can evaluate ANY lower array above two.
This theorem does not identify the adopted lower and upper arrays. -/
theorem adoptedFloor_eq_lowerValue {s : ℝ} (hs : 2 ≤ s) {a : AtomState}
    (ha : s ∈ scalarCell a) : adoptedH248Floor s = (lowerValue a : ℝ) := by
  have hm : max 2 s = s := max_eq_right hs
  rw [adoptedH248Floor, ← upperFloor_eq_lowerFloor_of_two_le _ hs]
  cases a with
  | none =>
    change upperFloor adoptedH248Numerators s = 0
    unfold upperFloor
    apply Finset.sum_eq_zero
    intro b _
    exact indicator_of_notMem (by simpa only [hm] using ha b) _
  | some b =>
    rw [lowerValue_cast]
    have hb : s ∈ upperAtomSet b := by simpa only [hm] using ha
    unfold upperFloor
    calc
      _ = (upperAtomSet b).indicator
          (fun _ => floorAtomValue adoptedH248Numerators b) s := by
        apply Finset.sum_eq_single b
        · intro c _ hcb
          exact indicator_of_notMem (fun hc => hcb
            (P5Z.U11H248.upperAtom_unique hc hb)) _
        · intro h
          exact (h (Finset.mem_univ b)).elim
      _ = _ := indicator_of_mem hb _

theorem lowerValue_nonneg (a : AtomState) : 0 ≤ lowerValue a := by
  cases a with
  | none => rfl
  | some b =>
    have h := adoptedAtomValue_nonneg b
    rw [← lowerValue_cast] at h
    exact_mod_cast h

def lowerValues (l u : ℚ) : Finset ℚ :=
  (P5Z.LiteralH248IntervalBounds.reachableStates l u).image lowerValue

theorem lowerValues_nonempty {l u : ℚ} (hlu : l ≤ u) :
    (lowerValues l u).Nonempty := by
  have hs := chosenState_mem (l : ℝ)
  have hr := P5Z.LiteralH248IntervalBounds.reachable_of_state (le_refl (l : ℝ))
    (by exact_mod_cast hlu) hs
  exact ⟨lowerValue (chosenState (l : ℝ)), Finset.mem_image.mpr
    ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩, rfl⟩⟩

def hLower (l u : ℚ) : ℚ :=
  if h : l ≤ u then (lowerValues l u).min' (lowerValues_nonempty h) else 0
def hUpper (l u : ℚ) : ℚ :=
  if h : l ≤ u then (lowerValues l u).max' (lowerValues_nonempty h) else 0

theorem hLower_nonneg (l u : ℚ) : 0 ≤ hLower l u := by
  unfold hLower
  split_ifs with hlu
  · obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp
      (Finset.min'_mem (lowerValues l u) (lowerValues_nonempty hlu))
    simpa only [← heq] using lowerValue_nonneg a
  · rfl

/-- Actual lower-table interval extrema, not upper-table certificates. -/
theorem adoptedFloor_interval {l u : ℚ} (hl2 : 2 ≤ l) {s : ℝ}
    (hl : (l : ℝ) ≤ s) (hu : s ≤ (u : ℝ)) :
    (hLower l u : ℝ) ≤ adoptedH248Floor s ∧
      adoptedH248Floor s ≤ (hUpper l u : ℝ) := by
  have hlu : l ≤ u := by exact_mod_cast hl.trans hu
  let a := chosenState s
  have ha : s ∈ scalarCell a := chosenState_mem s
  have hr := P5Z.LiteralH248IntervalBounds.reachable_of_state hl hu ha
  have hmem : lowerValue a ∈ lowerValues l u := Finset.mem_image.mpr
    ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩, rfl⟩
  have hL : hLower l u ≤ lowerValue a := by
    rw [hLower, dif_pos hlu]
    exact Finset.min'_le _ _ hmem
  have hU : lowerValue a ≤ hUpper l u := by
    rw [hUpper, dif_pos hlu]
    exact Finset.le_max' _ _ hmem
  rw [adoptedFloor_eq_lowerValue ((by exact_mod_cast hl2 : (2 : ℝ) ≤ l).trans hl) ha]
  exact ⟨by exact_mod_cast hL, by exact_mod_cast hU⟩

theorem adopted_s_two : adoptedH248Floor 2 =
    min (floorValue adoptedH248Numerators 49) (floorValue adoptedH248Numerators 50) := by
  have ha : (2 : ℝ) ∈ scalarCell (some (.inr P5Z.U1011H248Clamp.clampKnot)) := by
    change max 2 (2 : ℝ) ∈ Icc 1 5 ∩ {floorGrid 50}
    norm_num [floorGrid]
  rw [adoptedFloor_eq_lowerValue (by norm_num) ha, lowerValue_cast]
  exact P5Z.U1011H248Clamp.clampKnot_value _

theorem logLower_nonneg (n : ℕ) (q : ℚ) (hq : 2 ≤ q) : 0 ≤ logLower n q := by
  unfold logLower
  have hq0 : 0 < q := by linarith
  have hz : 0 ≤ (q - 2) / q := div_nonneg (by linarith) hq0.le
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg
    (fun k _ => div_nonneg (pow_nonneg hz _) (by positivity)))

/-- Only rational geometric admission, with no integrand-bound premise. -/
structure Box where
  uLo : ℚ
  uHi : ℚ
  tLo : ℚ
  tHi : ℚ

def Box.Admissible (b : Box) : Prop :=
  0 < b.uLo ∧ 0 < b.tLo ∧ b.uHi + b.tHi < 1 / 2
def Box.cell (b : Box) : Set (Fin 2 → ℝ) :=
  {x | (b.uLo : ℝ) ≤ x 0 ∧ x 0 ≤ (b.uHi : ℝ) ∧
    (b.tLo : ℝ) ≤ x 1 ∧ x 1 ≤ (b.tHi : ℝ)}
def Box.rLo (b : Box) : ℚ := 1 / 2 - b.uHi - b.tHi
def Box.rHi (b : Box) : ℚ := 1 / 2 - b.uLo - b.tLo
def Box.sLo (b : Box) : ℚ := max 2 (b.rLo / (417 / 5000))
def Box.sHi (b : Box) : ℚ := b.rHi / (417 / 5000)
def Box.denLo (b : Box) : ℚ := b.rLo * b.uLo * b.tLo
def Box.denHi (b : Box) : ℚ := b.rHi * b.uHi * b.tHi
def Box.kernelLower (b : Box) (n : ℕ) : ℚ :=
  4 * (logLower n b.sLo + hLower b.sLo b.sHi) / b.denHi
def Box.kernelUpper (b : Box) (n : ℕ) : ℚ :=
  4 * (logUpper n b.sHi + hUpper b.sLo b.sHi) / b.denLo
def Box.enhancementLower (b : Box) : ℚ := 4 * hLower b.sLo b.sHi / b.denHi
def Box.enhancementUpper (b : Box) : ℚ := 4 * hUpper b.sLo b.sHi / b.denLo

theorem Box.residual_bounds (b : Box) {x : Fin 2 → ℝ} (hx : x ∈ b.cell) :
    (b.rLo : ℝ) ≤ originalResidual x ∧ originalResidual x ≤ (b.rHi : ℝ) := by
  rcases hx with ⟨hu, hu', ht, ht'⟩
  simp only [Box.rLo, Box.rHi, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
  unfold originalResidual
  constructor <;> linarith

theorem Box.profile_bounds (b : Box) {x : Fin 2 → ℝ}
    (hx : x ∈ b.cell) (hD : x ∈ currentChenUpsilon6LogDomain 0) :
    (b.sLo : ℝ) ≤ currentChenUpsilon6OrdinaryProfile x ∧
      currentChenUpsilon6OrdinaryProfile x ≤ (b.sHi : ℝ) := by
  have hR := b.residual_bounds hx
  have hs2 := (P5U6RunboEnhancedFloorInterfaceSourceOnly.profile_range
    (by norm_num : (0 : ℝ) ≤ 0) hD).1
  have heq : currentChenUpsilon6OrdinaryProfile x = originalResidual x / (417 / 5000) := rfl
  simp only [Box.sLo, Box.sHi, Rat.cast_max, Rat.cast_div, Rat.cast_ofNat]
  rw [heq] at hs2 ⊢
  exact ⟨max_le hs2 (div_le_div_of_nonneg_right hR.1 (by norm_num)),
    div_le_div_of_nonneg_right hR.2 (by norm_num)⟩

theorem Box.denominator_bounds (b : Box) (hb : b.Admissible)
    {x : Fin 2 → ℝ} (hx : x ∈ b.cell) :
    0 < (b.denLo : ℝ) ∧
      (b.denLo : ℝ) ≤ originalResidual x * x 0 * x 1 ∧
      originalResidual x * x 0 * x 1 ≤ (b.denHi : ℝ) := by
  have hu : (0 : ℝ) < b.uLo := by exact_mod_cast hb.1
  have ht : (0 : ℝ) < b.tLo := by exact_mod_cast hb.2.1
  have hr : (0 : ℝ) < b.rLo := by
    have h : 0 < b.rLo := by dsimp [Box.rLo]; linarith [hb.2.2]
    exact_mod_cast h
  have hR := b.residual_bounds hx
  have hRpos := hr.trans_le hR.1
  have hupos := hu.trans_le hx.1
  have htpos := ht.trans_le hx.2.2.1
  have huhi := hupos.trans_le hx.2.1
  have hrhi := hRpos.trans_le hR.2
  simp only [Box.denLo, Box.denHi, Rat.cast_mul]
  refine ⟨by positivity, ?_, ?_⟩
  · exact mul_le_mul
      (mul_le_mul hR.1 hx.1 hu.le hRpos.le) hx.2.2.1 ht.le (by positivity)
  · exact mul_le_mul
      (mul_le_mul hR.2 hx.2.1 hupos.le hrhi.le) hx.2.2.2 htpos.le (by positivity)

private theorem Box.divide_bounds (b : Box) (hb : b.Admissible)
    {x : Fin 2 → ℝ} (hx : x ∈ b.cell) {lo v hi : ℝ}
    (hlo : 0 ≤ lo) (hloV : lo ≤ v) (hVhi : v ≤ hi) :
    lo / (b.denHi : ℝ) ≤ v / (originalResidual x * x 0 * x 1) ∧
      v / (originalResidual x * x 0 * x 1) ≤ hi / (b.denLo : ℝ) := by
  obtain ⟨hd, hdL, hdU⟩ := b.denominator_bounds hb hx
  have hd0 := hd.trans_le hdL
  have hhi : 0 ≤ hi := hlo.trans (hloV.trans hVhi)
  exact ⟨(div_le_div_of_nonneg_left hlo hd0 hdU).trans
    (div_le_div_of_nonneg_right hloV hd0.le),
    (div_le_div_of_nonneg_right hVhi hd0.le).trans
      (div_le_div_of_nonneg_left hhi hd hdL)⟩

/-- Genuine pointwise directed rational bounds for the actual h enhancement. -/
theorem Box.enhancement_bounds (b : Box) (hb : b.Admissible)
    {x : Fin 2 → ℝ} (hx : x ∈ b.cell) (hD : x ∈ currentChenUpsilon6LogDomain 0) :
    (b.enhancementLower : ℝ) ≤ originalEnhancement adoptedH248Floor x ∧
      originalEnhancement adoptedH248Floor x ≤ (b.enhancementUpper : ℝ) := by
  have hs := b.profile_bounds hx hD
  have hLo : (2 : ℚ) ≤ b.sLo := le_max_left _ _
  have hh := adoptedFloor_interval hLo hs.1 hs.2
  have hn : (0 : ℝ) ≤ 4 * (hLower b.sLo b.sHi : ℝ) := by
    exact mul_nonneg (by norm_num) (by exact_mod_cast hLower_nonneg b.sLo b.sHi)
  have h := b.divide_bounds hb hx hn
    (mul_le_mul_of_nonneg_left hh.1 (by norm_num))
    (mul_le_mul_of_nonneg_left hh.2 (by norm_num))
  simpa only [Box.enhancementLower, Box.enhancementUpper, Rat.cast_div,
    Rat.cast_mul, Rat.cast_ofNat, originalEnhancement] using h

/-- Complete original ordinary+adopted lower kernel bounds. The log uses
the actual first-strip formula, not a guessed normalization. -/
theorem Box.kernel_bounds (b : Box) (hb : b.Admissible) (n : ℕ)
    {x : Fin 2 → ℝ} (hx : x ∈ b.cell) (hD : x ∈ currentChenUpsilon6LogDomain 0) :
    (b.kernelLower n : ℝ) ≤ adoptedKernel x ∧
      adoptedKernel x ≤ (b.kernelUpper n : ℝ) := by
  have hs := b.profile_bounds hx hD
  have hLo : (2 : ℚ) ≤ b.sLo := le_max_left _ _
  have hLU : b.sLo ≤ b.sHi := by exact_mod_cast hs.1.trans hs.2
  have hHi : (2 : ℚ) ≤ b.sHi := hLo.trans hLU
  have hs2 : (2 : ℝ) ≤ currentChenUpsilon6OrdinaryProfile x :=
    (by exact_mod_cast hLo : (2 : ℝ) ≤ b.sLo).trans hs.1
  have hh := adoptedFloor_interval hLo hs.1 hs.2
  have hlL := (log_bounds n b.sLo hLo).1
  have hlU := (log_bounds n b.sHi hHi).2
  have hlogL : (logLower n b.sLo : ℝ) ≤
      Real.log (currentChenUpsilon6OrdinaryProfile x - 1) := hlL.trans
    (Real.log_le_log (by exact_mod_cast (show 0 < b.sLo - 1 by linarith))
      (by linarith only [hs.1]))
  have hlogU : Real.log (currentChenUpsilon6OrdinaryProfile x - 1) ≤
      (logUpper n b.sHi : ℝ) :=
    (Real.log_le_log (by linarith only [hs2]) (by linarith only [hs.2])).trans hlU
  have hn : (0 : ℝ) ≤ 4 * ((logLower n b.sLo : ℝ) + (hLower b.sLo b.sHi : ℝ)) :=
    mul_nonneg (by norm_num) (add_nonneg
      (by exact_mod_cast logLower_nonneg n b.sLo hLo)
      (by exact_mod_cast hLower_nonneg b.sLo b.sHi))
  have h := b.divide_bounds hb hx hn
    (mul_le_mul_of_nonneg_left (add_le_add hlogL hh.1) (by norm_num))
    (mul_le_mul_of_nonneg_left (add_le_add hlogU hh.2) (by norm_num))
  rw [adoptedKernel_eq_original_log]
  simpa only [Box.kernelLower, Box.kernelUpper, Rat.cast_div, Rat.cast_mul,
    Rat.cast_add, Rat.cast_ofNat] using h

/-- Direct binding to the TRUE normalized continuous lower sieve factor. -/
theorem Box.normalized_enhanced_bounds (b : Box) (hb : b.Admissible) (n : ℕ)
    {x : Fin 2 → ℝ} (hx : x ∈ b.cell) (hD : x ∈ currentChenUpsilon6LogDomain 0) :
    (b.kernelLower n : ℝ) ≤ currentChenUpsilon6NormalizedSieveKernel x +
        originalEnhancement adoptedH248Floor x ∧
      currentChenUpsilon6NormalizedSieveKernel x + originalEnhancement adoptedH248Floor x ≤
        (b.kernelUpper n : ℝ) := by
  rw [currentChenUpsilon6NormalizedSieveKernel_eq_ordinary (by norm_num) hD]
  exact b.kernel_bounds hb n hx hD

end

end ImbalancedChen.P5U6OriginalRationalBoxBounds
