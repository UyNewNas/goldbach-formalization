import ImbalancedChen.P4AOriginalMuSplitInvariant
import ImbalancedChen.ActualThirdOriginalPositive256LogRange32IntegerGuard

/-!
SOURCE_WRITTEN / UNCOMPILED / MAIN OPEN30.
Literal original seeds: D=48000*2^24, H=int(D/100), R=int(19D/96),
M=int(25D/128), t'=min(R,3*t//2), sorted finite sets, then adjacent zip.
Every finite prefix of the source seed loop satisfies the range invariant;
no historical stopping count, tree bytes, or evaluated numerical leaf is used.
Global ratio<32 does not assert the stronger unit-ratio<=2 for all tent leaves.
-/
namespace ImbalancedChen.P4AOriginalSeedRange32InvariantSourceOnly

noncomputable section
open OriginalThirdCompactPartitionSourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly P4AOriginalMuSplitInvariantSourceOnly
open OriginalThirdPositiveLogSourceOnly

def originalHInteger : ℤ := (48000*2^24)/100
def originalRInteger : ℤ := (19*(48000*2^24))/96

theorem original_integer_ranges :
    0 < originalHInteger ∧ originalHInteger ≤ originalMuInteger ∧
      originalMuInteger ≤ originalRInteger ∧
      originalRInteger ≤ 2*originalMuInteger ∧
      128*originalMuInteger = 25*(48000*2^24 : ℤ) ∧
      96*originalRInteger = 19*(48000*2^24 : ℤ) := by
  norm_num [originalHInteger, originalMuInteger, originalRInteger]

theorem original_R_div_H_lt_32 :
    (originalRInteger : ℝ)/(originalHInteger : ℝ) < 32 := by
  norm_num [originalHInteger, originalRInteger]

/-- Exact integer loop transition; no replacement geometric mesh. -/
def seedCutState (H M R : ℤ) : ℕ → ℤ × Finset ℤ
  | 0 => (H, {H,M,R})
  | n+1 =>
      let old := seedCutState H M R n
      let next := min R (old.1*3/2)
      (next, insert next old.2)

theorem seedCutState_range (H M R : ℤ) (hH : 0 < H) (hHM : H ≤ M) (hMR : M ≤ R)
    (n : ℕ) :
    H ≤ (seedCutState H M R n).1 ∧ (seedCutState H M R n).1 ≤ R ∧
      ∀ p ∈ (seedCutState H M R n).2, H ≤ p ∧ p ≤ R := by
  induction n with
  | zero =>
      refine ⟨le_rfl, hHM.trans hMR, ?_⟩
      intro p hp
      have he : p=H ∨ p=M ∨ p=R := by simpa only [seedCutState,
        Finset.mem_insert, Finset.mem_singleton] using hp
      rcases he with rfl | rfl | rfl
      · exact ⟨le_rfl, hHM.trans hMR⟩
      · exact ⟨hHM, hMR⟩
      · exact ⟨hHM.trans hMR, le_rfl⟩
  | succ n ih =>
      have ht : 0 ≤ (seedCutState H M R n).1 := hH.le.trans ih.1
      have hstep : (seedCutState H M R n).1 ≤ (seedCutState H M R n).1*3/2 := by
        apply (Int.le_ediv_iff_mul_le (by norm_num : (0:ℤ)<2)).mpr
        omega
      have hlo : H ≤ min R ((seedCutState H M R n).1*3/2) :=
        le_min (hHM.trans hMR) (ih.1.trans hstep)
      have hhi : min R ((seedCutState H M R n).1*3/2) ≤ R := min_le_left _ _
      refine ⟨hlo, hhi, ?_⟩
      intro p hp
      change p ∈ insert (min R ((seedCutState H M R n).1*3/2))
        (seedCutState H M R n).2 at hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact ⟨hlo,hhi⟩
      · exact ih.2.2 p hp

theorem seedCutState_mu_mem (H M R : ℤ) (n : ℕ) : M ∈ (seedCutState H M R n).2 := by
  induction n with
  | zero => simp [seedCutState]
  | succ n ih => exact Finset.mem_insert_of_mem ih

def originalSeedCuts (n : ℕ) : Finset ℤ :=
  (seedCutState originalHInteger originalMuInteger originalRInteger n).2

theorem originalSeedCuts_range (n : ℕ) (p : ℤ) (hp : p ∈ originalSeedCuts n) :
    originalHInteger ≤ p ∧ p ≤ originalRInteger := by
  exact (seedCutState_range _ _ _ original_integer_ranges.1
    original_integer_ranges.2.1 original_integer_ranges.2.2.1 n).2.2 p hp

theorem originalSeedCuts_mu_mem (n : ℕ) : originalMuInteger ∈ originalSeedCuts n := by
  exact seedCutState_mu_mem _ _ _ n

theorem ordered_nodup_consecutive_lt (cuts : List ℤ) :
    cuts.Pairwise (· ≤ ·) → cuts.Nodup →
      ∀ {x y : ℤ}, (x,y) ∈ consecutivePairs cuts → x < y := by
  induction cuts with
  | nil => intro _ _ x y h; simp [consecutivePairs] at h
  | cons a tail ih =>
      intro ho hn x y h
      cases tail with
      | nil => simp [consecutivePairs] at h
      | cons b rest =>
          have horder := List.pairwise_cons.mp ho
          have hnodup := List.nodup_cons.mp hn
          change (x,y) ∈ (a,b) :: consecutivePairs (b::rest) at h
          rcases List.mem_cons.mp h with h | h
          · have he : x=a ∧ y=b := by simpa only [Prod.mk.injEq] using h
            rcases he with ⟨rfl,rfl⟩
            have hne : a ≠ b := by intro he; apply hnodup.1; simp [he]
            exact lt_of_le_of_ne (horder.1 b (by simp)) hne
          · exact ih horder.2 hnodup.2 h

theorem sourceSeedXYCuts_mem_range (z0 M R H p : ℤ)
    (hz : H ≤ z0 ∧ z0 ≤ R) (hM : H ≤ M ∧ M ≤ R)
    (hp : p ∈ sourceSeedXYCuts z0 M R) : H ≤ p ∧ p ≤ R := by
  by_cases hs : z0 < M
  · have he : p=z0 ∨ p=M ∨ p=R := by simpa [sourceSeedXYCuts, hs] using hp
    rcases he with rfl | rfl | rfl
    · exact hz
    · exact hM
    · exact ⟨hz.1.trans hz.2, le_rfl⟩
  · have he : p=z0 ∨ p=R := by simpa [sourceSeedXYCuts, hs] using hp
    rcases he with rfl | rfl
    · exact hz
    · exact ⟨hz.1.trans hz.2, le_rfl⟩

theorem sourceSeedXYCuts_consecutive_lt (z0 M R x y : ℤ) (hzR : z0 < R)
    (h : (x,y) ∈ consecutivePairs (sourceSeedXYCuts z0 M R)) : x < y := by
  apply ordered_nodup_consecutive_lt (sourceSeedXYCuts z0 M R) _ _ h
  · by_cases hs : z0 < M
    · simpa only [sourceSeedXYCuts, if_pos hs] using
        (Finset.pairwise_sort ({z0,M,R} : Finset ℤ) (· ≤ ·))
    · simpa [sourceSeedXYCuts, hs] using hzR.le
  · by_cases hs : z0 < M
    · simpa only [sourceSeedXYCuts, if_pos hs] using
        (Finset.sort_nodup ({z0,M,R} : Finset ℤ) (· ≤ ·))
    · simp [sourceSeedXYCuts, hs, ne_of_lt hzR]

def integerBoxRange (a b : IntegerPoint) : Prop :=
  ∀ i, originalHInteger ≤ a i ∧ a i < b i ∧ b i ≤ originalRInteger

/-- Every exact source seed (including boundary/outside boxes) has positive
coordinate widths and lies in the original [H,R] range. -/
theorem source_seed_integerBoxRange (n : ℕ) (z0 z1 x0 x1 y0 y1 : ℤ)
    (hz : (z0,z1) ∈ consecutivePairs ((originalSeedCuts n).sort (· ≤ ·)))
    (hx : (x0,x1) ∈ consecutivePairs (sourceSeedXYCuts z0 originalMuInteger originalRInteger))
    (hy : (y0,y1) ∈ consecutivePairs (sourceSeedXYCuts z0 originalMuInteger originalRInteger)) :
    integerBoxRange (seedLower x0 y0 z0) (seedUpper x1 y1 z1) := by
  have hze := consecutivePairs_mem_endpoints _ hz
  have hz0 := originalSeedCuts_range n z0 (Finset.mem_sort.mp hze.1)
  have hz1 := originalSeedCuts_range n z1 (Finset.mem_sort.mp hze.2)
  have hzlt := ordered_nodup_consecutive_lt _ (Finset.pairwise_sort _ _)
    (Finset.sort_nodup _ _) hz
  have hzR : z0 < originalRInteger := hzlt.trans_le hz1.2
  have hM : originalHInteger ≤ originalMuInteger ∧ originalMuInteger ≤ originalRInteger :=
    ⟨original_integer_ranges.2.1, original_integer_ranges.2.2.1⟩
  have hxe := consecutivePairs_mem_endpoints _ hx
  have hye := consecutivePairs_mem_endpoints _ hy
  have hx0 := sourceSeedXYCuts_mem_range _ _ _ _ _ hz0 hM hxe.1
  have hx1 := sourceSeedXYCuts_mem_range _ _ _ _ _ hz0 hM hxe.2
  have hy0 := sourceSeedXYCuts_mem_range _ _ _ _ _ hz0 hM hye.1
  have hy1 := sourceSeedXYCuts_mem_range _ _ _ _ _ hz0 hM hye.2
  have hxlt := sourceSeedXYCuts_consecutive_lt _ _ _ _ _ hzR hx
  have hylt := sourceSeedXYCuts_consecutive_lt _ _ _ _ _ hzR hy
  intro i
  fin_cases i
  · exact ⟨hx0.1,hxlt,hx1.2⟩
  · exact ⟨hy0.1,hylt,hy1.2⟩
  · exact ⟨hz0.1,hzlt,hz1.2⟩

/-- Arbitrary source cuts can only increase lower and decrease upper endpoints. -/
theorem integerLeafBoxes_nested (tree : ClosedCutTree) (a b : IntegerPoint)
    (bounds : IntegerPoint × IntegerPoint) (hb : bounds ∈ integerLeafBoxes tree a b) :
    ∀ i, a i ≤ bounds.1 i ∧ bounds.2 i ≤ b i := by
  induction tree generalizing a b with
  | leaf =>
      have he : bounds=(a,b) := by simpa only [integerLeafBoxes,List.mem_singleton] using hb
      subst bounds
      intro i
      exact ⟨le_rfl,le_rfl⟩
  | split axis cut left right ihL ihR =>
      change bounds ∈ integerLeafBoxes left a (leftIntegerUpper b axis cut) ++
        integerLeafBoxes right (rightIntegerLower a axis cut) b at hb
      rcases List.mem_append.mp hb with hb | hb
      · intro i
        have hi := ihL _ _ hb i
        exact ⟨hi.1,hi.2.trans (leftIntegerUpper_le b axis i cut)⟩
      · intro i
        have hi := ihR _ _ hb i
        exact ⟨(le_rightIntegerLower a axis i cut).trans hi.1,hi.2⟩

theorem integerLeafBoxes_range (tree : ClosedCutTree) (a b : IntegerPoint)
    (hr : integerBoxRange a b) (bounds : IntegerPoint × IntegerPoint)
    (hb : bounds ∈ integerLeafBoxes tree a b) (hw : ∀ i, bounds.1 i < bounds.2 i) :
    integerBoxRange bounds.1 bounds.2 := by
  intro i
  have hn := integerLeafBoxes_nested tree a b bounds hb i
  exact ⟨(hr i).1.trans hn.1,hw i,hn.2.trans (hr i).2.2⟩

/-- Both strict-width children force the source midpoint to lie inside the
parent. The inside-cut assertion is a conclusion, not a premise. -/
theorem cut_inside_of_both_child_widths (a b : IntegerPoint) (axis : Fin 3) (cut : ℤ)
    (hl : a axis < leftIntegerUpper b axis cut axis)
    (hr : rightIntegerLower a axis cut axis < b axis) : a axis < cut ∧ cut < b axis := by
  change a axis < min (b axis) cut at hl
  change max (a axis) cut < b axis at hr
  exact ⟨hl.trans_le (min_le_right _ _),(le_max_right _ _).trans_lt hr⟩

theorem integerBoxRange_ratio32 (a b : IntegerPoint) (hr : integerBoxRange a b) (i : Fin 3) :
    0 < a i ∧ (b i : ℝ)/(a i : ℝ) ≤
      (originalRInteger : ℝ)/(originalHInteger : ℝ) ∧ (b i : ℝ)/(a i : ℝ) < 32 := by
  have hH : (0:ℝ)<(originalHInteger:ℝ) := by exact_mod_cast original_integer_ranges.1
  have hlo : (originalHInteger:ℝ)≤(a i:ℝ) := by exact_mod_cast (hr i).1
  have hhi : (b i:ℝ)≤(originalRInteger:ℝ) := by exact_mod_cast (hr i).2.2
  have hHR : originalHInteger ≤ originalRInteger :=
    original_integer_ranges.2.1.trans original_integer_ranges.2.2.1
  have hHRreal : (originalHInteger:ℝ)≤(originalRInteger:ℝ) := by exact_mod_cast hHR
  have hR : (0:ℝ)≤(originalRInteger:ℝ) := hH.le.trans hHRreal
  have hlopos : (0:ℝ)<(a i:ℝ) := hH.trans_le hlo
  have hratio : (b i:ℝ)/(a i:ℝ)≤(originalRInteger:ℝ)/(originalHInteger:ℝ) :=
    (div_le_div_of_nonneg_right hhi hlopos.le).trans
      (div_le_div₀ hR le_rfl hH hlo)
  exact ⟨by exact_mod_cast hlopos,hratio,hratio.trans_lt original_R_div_H_lt_32⟩

/-- The missing literal-operation bridge: when the actual ratio is <=2,
the original full ln32 has exactly the original unit branch, including k=0. -/
theorem originalLn32_eq_originalLnUnit_of_le_two {x : ℝ} (h : x ≤ 2) :
    originalLn32 x = originalLnUnit x := by
  simp only [originalLn32,if_pos h,originalLogBranch,originalLnUnit,Nat.cast_zero]

theorem original_range_noCross_log32_pos (a b : IntegerPoint) (hr : integerBoxRange a b)
    (i : Fin 3) (hc : noCrossMu originalMuInteger i a b) :
    0 < (originalLn32 ((b i:ℝ)/(a i:ℝ))).lo := by
  have hg := integerBoxRange_ratio32 a b hr i
  rcases hc with hbelow | habove
  · have hm : 128*b i ≤ 25*(48000*2^24:ℤ) := by
      calc
        128*b i ≤ 128*originalMuInteger := mul_le_mul_of_nonneg_left hbelow (by norm_num)
        _ = 25*(48000*2^24:ℤ) := original_integer_ranges.2.2.2.2.1
    exact original_integer_below_mu_log32_guard (a i) (b i) hg.1 (hr i).2.1 hm hg.2.2.le
  · have hmu : 25*(48000*2^24:ℤ) ≤ 128*a i := by
      calc
        25*(48000*2^24:ℤ) = 128*originalMuInteger := original_integer_ranges.2.2.2.2.1.symm
        _ ≤ 128*a i := mul_le_mul_of_nonneg_left habove (by norm_num)
    have hrho : 96*b i ≤ 19*(48000*2^24:ℤ) := by
      calc
        96*b i ≤ 96*originalRInteger := mul_le_mul_of_nonneg_left (hr i).2.2 (by norm_num)
        _ = 19*(48000*2^24:ℤ) := original_integer_ranges.2.2.2.2.2
    have htwo : b i ≤ 2*a i := (hr i).2.2.trans
      (original_integer_ranges.2.2.2.1.trans (mul_le_mul_of_nonneg_left habove (by norm_num)))
    have haR : (0:ℝ)<(a i:ℝ) := by exact_mod_cast hg.1
    have htwoR : (b i:ℝ)/(a i:ℝ) ≤ 2 := (div_le_iff₀ haR).mpr (by exact_mod_cast htwo)
    rw [originalLn32_eq_originalLnUnit_of_le_two htwoR]
    exact (original_integer_above_mu_log_guards (a i) (b i) (hr i).2.1 hmu hrho).2.1

/-- Reusable six-tent unit-path supplier: a genuine unit-ratio guard gives
literal equality with the producer's full ln and the actual positive lo.
The global range32 estimate is never promoted to a false unit-ratio bound. -/
theorem original_range_unit_log_guards (a b : IntegerPoint) (hr : integerBoxRange a b)
    (i : Fin 3) (hc : noCrossMu originalMuInteger i a b)
    (hunit : (b i:ℝ)/(a i:ℝ) ≤ 2) :
    originalLn32 ((b i:ℝ)/(a i:ℝ)) = originalLnUnit ((b i:ℝ)/(a i:ℝ)) ∧
      0 < (originalLnUnit ((b i:ℝ)/(a i:ℝ))).lo := by
  have he := originalLn32_eq_originalLnUnit_of_le_two hunit
  refine ⟨he,?_⟩
  rw [← he]
  exact original_range_noCross_log32_pos a b hr i hc

theorem decoded_ratio_eq_integer_ratio (a b : IntegerPoint) (i : Fin 3)
    (ha : 0 < a i) :
    decodeCoordinates b i / decodeCoordinates a i = (b i:ℝ)/(a i:ℝ) := by
  have haR : (0:ℝ)<(a i:ℝ) := by exact_mod_cast ha
  unfold decodeCoordinates
  field_simp [original_coordinateDenominator_pos.ne',haR.ne']

/-- Real-coordinate consumer without changing the producer's log operand. -/
theorem original_range_decoded_log32_pos (a b : IntegerPoint) (hr : integerBoxRange a b)
    (i : Fin 3) (hc : noCrossMu originalMuInteger i a b) :
    decodeCoordinates b i / decodeCoordinates a i < 32 ∧
      0 < (originalLn32 (decodeCoordinates b i / decodeCoordinates a i)).lo := by
  have hg := integerBoxRange_ratio32 a b hr i
  rw [decoded_ratio_eq_integer_ratio a b i hg.1]
  exact ⟨hg.2.2,original_range_noCross_log32_pos a b hr i hc⟩

/-- The genuine source seed list supplies no-crossing on z as well as x/y. -/
theorem source_seed_noCross_all (n : ℕ) (z0 z1 x0 x1 y0 y1 : ℤ)
    (hz : (z0,z1) ∈ consecutivePairs ((originalSeedCuts n).sort (· ≤ ·)))
    (hx : (x0,x1) ∈ consecutivePairs (sourceSeedXYCuts z0 originalMuInteger originalRInteger))
    (hy : (y0,y1) ∈ consecutivePairs (sourceSeedXYCuts z0 originalMuInteger originalRInteger)) :
    ∀ i, noCrossMu originalMuInteger i (seedLower x0 y0 z0) (seedUpper x1 y1 z1) := by
  have hxy := source_seed_noCross_xy z0 z1 originalMuInteger originalRInteger x0 x1 y0 y1 hx hy
  have hzm : originalMuInteger ∈ (originalSeedCuts n).sort (· ≤ ·) :=
    Finset.mem_sort.mpr (originalSeedCuts_mu_mem n)
  have hzc := ordered_cutList_consecutive_noCross _ originalMuInteger
    (Finset.pairwise_sort _ _) hzm hz
  intro i
  fin_cases i
  · exact hxy.1
  · exact hxy.2
  · simpa only [noCrossMu,seedLower,seedUpper,Matrix.cons_val_two] using hzc

/-- End-to-end actual descendant supplier: range, strict ratio<32 and raw
original ln32.lo>0 for every coordinate. Only actual positive widths remain. -/
theorem source_seed_descendants_range32_log_guards (tree : ClosedCutTree) (n : ℕ)
    (z0 z1 x0 x1 y0 y1 : ℤ)
    (hz : (z0,z1) ∈ consecutivePairs ((originalSeedCuts n).sort (· ≤ ·)))
    (hx : (x0,x1) ∈ consecutivePairs (sourceSeedXYCuts z0 originalMuInteger originalRInteger))
    (hy : (y0,y1) ∈ consecutivePairs (sourceSeedXYCuts z0 originalMuInteger originalRInteger))
    (bounds : IntegerPoint × IntegerPoint)
    (hb : bounds ∈ integerLeafBoxes tree (seedLower x0 y0 z0) (seedUpper x1 y1 z1))
    (hw : ∀ i, bounds.1 i < bounds.2 i) :
    integerBoxRange bounds.1 bounds.2 ∧ ∀ i,
      (bounds.2 i:ℝ)/(bounds.1 i:ℝ) ≤ (originalRInteger:ℝ)/(originalHInteger:ℝ) ∧
      (bounds.2 i:ℝ)/(bounds.1 i:ℝ) < 32 ∧
      0 < (originalLn32 ((bounds.2 i:ℝ)/(bounds.1 i:ℝ))).lo := by
  have hr := integerLeafBoxes_range tree _ _
    (source_seed_integerBoxRange n z0 z1 x0 x1 y0 y1 hz hx hy) bounds hb hw
  have hcross := source_seed_noCross_all n z0 z1 x0 x1 y0 y1 hz hx hy
  refine ⟨hr,?_⟩
  intro i
  have hratio := integerBoxRange_ratio32 bounds.1 bounds.2 hr i
  exact ⟨hratio.2.1,hratio.2.2,original_range_noCross_log32_pos _ _ hr i
    (integerLeafBoxes_noCrossMu tree originalMuInteger i _ _ (hcross i) bounds hb)⟩

end
end ImbalancedChen.P4AOriginalSeedRange32InvariantSourceOnly
