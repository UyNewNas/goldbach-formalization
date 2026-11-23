import ImbalancedChen.P2HistoricalScheduledPointReads
import ImbalancedChen.P5ZU11ActualH248Ordinary

/-! Archived point rows read prescribed cells. The scalar profile uses
adjacent minima at knots. Here their difference is computed on the actual
chronological H248 table, using one original lower Buchstab product. -/
namespace ImbalancedChen.P2HistoricalPointProfile

noncomputable section
open Set Wu2008DoubleSieve
open scoped Classical BigOperators
open P2TableActionSourceOnly P2SimultaneousTableSourceOnly
open P2HistoricalSourceJSON (Value)
open P2Historical248Authentication P2HistoricalScheduledPointReads
open P2HistoricalHighPointAncestry P2HistoricalBankLogWeights
open P2HistoricalLowerBankAncestry (UpperEndpoints iterate_nonnegative)
open Part5OriginalUpsilon5CausalDictionary (FloorAtom floorGrid floorValue floorKnotValue floorAtomValue)
open Part5UpperTables (upperAtomSet upperFloor)

theorem suffix_head (W : LogWeights) (old : Table) (side : Bool) {k : ℕ} (hk : k < 200) :
    suffixNumerator W old side k = suffixNumerator W old side (k+1) +
      read old side k * W.numerator k / (tableQ : ℤ) := by
  unfold suffixNumerator
  have hr : 200-k = (200-(k+1))+1 := by omega
  conv_lhs => rw [hr,Finset.sum_range_succ',Nat.add_zero]
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Consecutive high cells differ by their first rounded suffix summand. -/
theorem high_neighbour (g : ℕ) (i : Fin 200) (hi : 100 ≤ i.val) (hn : i.val+1 < 200) :
    outputAt (g+1) true i = outputAt (g+1) true ⟨i.val+1, hn⟩ +
      read (outputAt g) false (i.val-49) * historicalLogWeights.numerator (i.val-49) / (tableQ : ℤ) := by
  let j : Fin 200 := ⟨i.val+1,hn⟩
  have hj : 100 ≤ j.val := by dsimp [j]; omega
  rw [high_last_suffix _ _ designated_low_writes g i hi,
    high_last_suffix _ _ designated_low_writes g j hj]
  have hp : max 50 (i.val-49) = i.val-49 := by omega
  have hq : max 50 (j.val-49) = (i.val-49)+1 := by dsimp [j]; omega
  rw [hp,hq]
  exact suffix_head _ _ _ (by omega)

private theorem profile_at (nums : Fin 200 → ℤ) {s : ℝ} {a : FloorAtom}
    (ha : s ∈ upperAtomSet a) : upperFloor nums s = floorAtomValue nums a := by
  unfold upperFloor
  calc
    _ = (upperAtomSet a).indicator (fun _ => floorAtomValue nums a) s := by
      apply Finset.sum_eq_single a
      · intro b _ hb
        exact indicator_of_notMem (fun h => hb (P5Z.U11H248.upperAtom_unique h ha)) _
      · intro h
        exact (h (Finset.mem_univ a)).elim
    _ = _ := indicator_of_mem ha _

private theorem grid_cast' (k : ℕ) : (gridAt k : ℝ) = floorGrid k := by
  simp [gridAt,floorGrid]

/-- Q80-normalized exact excess of a prescribed historical read at an
internal high knot. Nothing from the 430 iteration is used. -/
def knotExcess (g : ℕ) (i : Fin 200) : ℝ :=
  if i.val+1 < 200 then
    ((read (outputAt g) false (i.val-49) * historicalLogWeights.numerator (i.val-49) /
      (tableQ : ℤ) : ℤ) : ℝ)/tableQ
  else 0

theorem knotExcess_nonneg (g : ℕ) (i : Fin 200) : 0 ≤ knotExcess g i := by
  unfold knotExcess
  split_ifs
  · have hread := read_nonnegative (iterate_nonnegative designatedW1 designatedW2 g) false (i.val-49)
    have hw := historicalLogWeights.nonnegative (i.val-49) (by omega)
    exact div_nonneg (by exact_mod_cast Int.ediv_nonneg (mul_nonneg hread hw)
      (show (0 : ℤ) ≤ tableQ by positivity)) (by positivity)
  · rfl

private theorem final_knot (g : ℕ) (i : Fin 200) (hi : i.val+1 = 200) :
    upperFloor (outputAt g true) (floorGrid (i.val+1)) = (outputAt g true i : ℝ)/tableQ := by
  have hb : floorGrid (i.val+1) ∈ upperAtomSet (.inr i.succ) := by
    change floorGrid (i.val+1) ∈ Icc 1 5 ∩ {floorGrid (i.val+1)}
    exact ⟨by norm_num [hi,floorGrid],rfl⟩
  rw [profile_at _ hb]
  have he : (199 : Fin 200) = i := Fin.ext (by omega)
  simp [floorAtomValue,floorKnotValue,floorValue,tableQ,hi,he,show i.val+1 ≠ 0 by omega]

private theorem internal_high_knot (g : ℕ) (i : Fin 200) (hi : 100 ≤ i.val)
    (hn : i.val+1 < 200) :
    (outputAt (g+1) true i : ℝ)/tableQ =
      upperFloor (outputAt (g+1) true) (floorGrid (i.val+1)) + knotExcess g i := by
  let j : Fin 200 := ⟨i.val+1,hn⟩
  have hg := tableGrid_bounds (show i.val+1 ≤ 200 by omega)
  have hb : floorGrid (i.val+1) ∈ upperAtomSet (.inr i.succ) := by
    change floorGrid (i.val+1) ∈ Icc 1 5 ∩ {floorGrid (i.val+1)}
    exact ⟨hg,rfl⟩
  have hd := high_neighbour g i hi hn
  have hdec : (outputAt (g+1) true i : ℝ)/tableQ =
      (outputAt (g+1) true j : ℝ)/tableQ + knotExcess g i := by
    have hr : (outputAt (g+1) true i : ℝ) = (outputAt (g+1) true j : ℝ) +
        ((read (outputAt g) false (i.val-49) * historicalLogWeights.numerator (i.val-49) /
          (tableQ : ℤ) : ℤ) : ℝ) := by exact_mod_cast hd
    rw [hr, add_div, knotExcess, if_pos hn]
  have hle : floorValue (outputAt (g+1) true) j ≤ floorValue (outputAt (g+1) true) i := by
    simp only [floorValue, show (2^80 : ℝ) = tableQ by norm_num [tableQ]]
    linarith only [hdec,knotExcess_nonneg g i]
  rw [profile_at _ hb]
  have hleft : (⟨i.val+1-1, by omega⟩ : Fin 200) = i := Fin.ext (by omega)
  change _ = floorKnotValue (outputAt (g+1) true) i.succ + _
  simp only [floorKnotValue,Fin.val_succ,dif_neg (show i.val+1 ≠ 0 by omega),
    dif_neg (show i.val+1 ≠ 200 by omega),hleft,show (⟨i.val+1,hn⟩ : Fin 200)=j by rfl,
    min_eq_right hle, floorValue, show (2^80 : ℝ) = tableQ by norm_num [tableQ]]
  exact hdec

/-- A genuine archived point contributes the scalar at the same argument,
plus a single, explicitly specified correction if it is a right knot.
At the final endpoint the sole adjoining cell already gives the scalar. -/
theorem scheduled_point_profile (g : ℕ) {i : Fin 200} {x : ℚ} (hx : HighPoint i x) :
    (outputAt (g+1) true i : ℝ)/tableQ = upperFloor (outputAt (g+1) true) (x : ℝ) +
      if x = gridAt (i.val+1) then knotExcess g i else 0 := by
  rcases hx with ⟨hi,h3,hlo,hhi⟩
  by_cases he : x = gridAt (i.val+1)
  · rw [if_pos he,he,grid_cast']
    by_cases hn : i.val+1 < 200
    · exact internal_high_knot g i hi hn
    · have hk : i.val+1 = 200 := by omega
      rw [final_knot (g+1) i hk,knotExcess,if_neg hn,add_zero]
  · rw [if_neg he,add_zero]
    have hxl : floorGrid i.val < (x:ℝ) := by
      rw [← grid_cast']; exact_mod_cast hlo
    have hxr : (x:ℝ) < floorGrid (i.val+1) := by
      rw [← grid_cast']; exact_mod_cast lt_of_le_of_ne hhi he
    have ht := tableGrid_bounds (show i.val+1 ≤ 200 by omega)
    have h3r : (3:ℝ) < (x:ℝ) := by exact_mod_cast h3
    have hb : (x:ℝ) ∈ upperAtomSet (.inl i) :=
      ⟨⟨by linarith, hxr.le.trans ht.2⟩,hxl,hxr⟩
    rw [profile_at _ hb]
    rfl

/-- The prescribed point, including any knot excess, is paid by the
actual upper limit if the preceding endpoint enclosure is available. -/
theorem archived_point_le_actual {δ : ℝ} (hd : 0 < δ) (hd' : δ ≤ 1/10)
    (g : ℕ) {i : Fin 200} {x : ℚ} (hx : HighPoint i x) (hold : UpperEndpoints δ (outputAt g)) :
    (outputAt g true i : ℝ)/tableQ ≤ H δ (x : ℝ) := by
  have hR : (3:ℝ) < (x:ℝ) := by exact_mod_cast hx.2.1
  have he : (x:ℝ) ≤ tableGrid (i.val+1) := by
    change (x:ℝ) ≤ floorGrid (i.val+1)
    rw [← grid_cast']; exact_mod_cast hx.2.2.2
  have hb := tableGrid_bounds (show i.val+1 ≤ 200 by omega)
  exact (hold i).trans (wuImprovementLimit_upper_antitone hd hd'
    ⟨by linarith,he.trans (hb.2.trans (by norm_num))⟩
    ⟨hb.1,hb.2.trans (by norm_num)⟩ he)

theorem w1_point_price {δ : ℝ} (hd : 0 < δ) (hd' : δ ≤ 1/10) (g : ℕ)
    {a : SourceW1} (ha : a ∈ sourceW1Schedule g) (hold : UpperEndpoints δ (outputAt g)) :
    (outputAt g true a.pointIndex : ℝ)/tableQ ≤ H δ (a.s0 : ℝ) :=
  archived_point_le_actual hd hd' g (scheduled_w1_point g ha) hold

theorem w2_point_price {δ : ℝ} (hd : 0 < δ) (hd' : δ ≤ 1/10) (g : ℕ)
    {b : Value × P2OriginalW2CandidateIntegerABI.Action} (hb : b ∈ taggedW2 g)
    (hold : UpperEndpoints δ (outputAt g)) :
    (sourcePointSum (outputAt g) b.2.points : ℝ)/tableQ/5 ≤
      (4*H δ (anchor0 b.1 : ℝ) + H δ (anchor1 b.1 : ℝ))/5 := by
  obtain ⟨p,r,hr,hm,hm',hp,hs⟩ := scheduled_w2_points g hb
  have h₁ := archived_point_le_actual hd hd' g hp hold
  have h₂ := archived_point_le_actual hd hd' g hs hold
  simp only [hr,sourcePointSum,hm,hm',mul_one,add_zero,Int.cast_add,Int.cast_mul,Int.cast_ofNat,add_div]
  have he : (outputAt g true p.index : ℝ)*4/tableQ = 4*((outputAt g true p.index : ℝ)/tableQ) := by ring
  rw [he]
  linarith only [h₁,h₂]

private theorem upper_cell_value_le {δ : ℝ} (hd : 0<δ) (hd' : δ≤1/10)
    {old : Table} (hold : UpperEndpoints δ old) (i : Fin 200) {s : ℝ}
    (hs : s ∈ Icc (floorGrid i.val) (floorGrid (i.val+1))) :
    floorValue (old true) i ≤ H δ s := by
  have hlo := tableGrid_bounds (show i.val ≤ 200 by omega)
  have hhi := tableGrid_bounds (show i.val+1 ≤ 200 by omega)
  change s ∈ Icc (tableGrid i.val) (tableGrid (i.val+1)) at hs
  have he := actual_cell_enclosure true hd hd' hlo.1 (hs.1.trans hs.2)
    (hhi.2.trans (by norm_num : (5:ℝ)≤10)) (hold i) s hs
  simpa only [floorValue,tableQ,H] using he

/-- The complete scalar H profile is below the true preceding Wu
function when the preceding endpoints have been paid. All knot atoms,
including the endpoint at five, are covered by this comparison. -/
theorem upper_profile_le_actual {δ : ℝ} (hd : 0<δ) (hd' : δ≤1/10)
    {old : Table} (hold : UpperEndpoints δ old) {s : ℝ} (hs : s ∈ Icc (1:ℝ) 5) :
    upperFloor (old true) s ≤ H δ s := by
  by_cases hex : ∃ a : FloorAtom, s ∈ upperAtomSet a
  · obtain ⟨a,ha⟩ := hex
    rw [profile_at _ ha]
    rcases a with i | k
    · exact upper_cell_value_le hd hd' hold i ⟨ha.2.1.le,ha.2.2.le⟩
    · have he : s = floorGrid k.val := ha.2
      rw [he]
      change floorKnotValue (old true) k ≤ _
      by_cases hz : k.val = 0
      · rw [floorKnotValue,dif_pos hz]
        exact upper_cell_value_le hd hd' hold 0 ⟨by simp [hz],by simpa [hz] using tableGrid_mono (show 0≤1 by omega)⟩
      · by_cases hk : k.val = 200
        · rw [floorKnotValue,dif_neg hz,dif_pos hk]
          exact upper_cell_value_le hd hd' hold 199 ⟨by simpa [hk] using
            tableGrid_mono (show 199≤200 by omega),by simp [hk]⟩
        · rw [floorKnotValue,dif_neg hz,dif_neg hk]
          let i : Fin 200 := ⟨k.val,by omega⟩
          apply (min_le_right _ (floorValue (old true) i)).trans
          exact upper_cell_value_le hd hd' hold i ⟨le_rfl, tableGrid_mono (Nat.le_succ _)⟩
  · have hzero : upperFloor (old true) s = 0 := by
      unfold upperFloor
      exact Finset.sum_eq_zero (fun a _ => indicator_of_notMem (fun ha => hex ⟨a,ha⟩) _)
    rw [hzero]
    exact wuImprovementLimit_nonneg true hd (by linarith : δ<1/2) hs.1 (hs.2.trans (by norm_num))

end
end ImbalancedChen.P2HistoricalPointProfile
