import ImbalancedChen.P2OriginalSixthProperAffineWalls
import ImbalancedChen.P2OriginalSixthCompactArithmeticFibre
import ImbalancedChen.P1ActualMovingAffineSlab

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual arithmetic payment for the omitted part of the original eleven
sixth source cells.  The compact index is fixed BEFORE N tends to infinity.
The estimate uses the installed endpoint-uniform prime-interval theorem,
finite coordinate disintegration, and the retained closed prime atom.
No continuous omitted-gain or omitted-density estimate is a hypothesis.

The test version covers every uniformly bounded signed tuple test.  It
does not assert a bound for unbounded AP errors or for a subsequent
absolute small-divisor sum: those arithmetic factors must still be paid.
-/

namespace ImbalancedChen.P2OriginalSixthOmittedArithmeticMass

noncomputable section
open Classical Filter Set
open scoped BigOperators Topology
open Certificates.P2OriginalSixthElevenLogSemantics
open P2OriginalSixthSourceCompactCores P2OriginalSixthCompactArithmeticFibre
open P2OriginalSixthProperAffineWalls
open P1ActualMovingAffineWallMass P1ActualMovingAffineSlab
open P1ActualMovingCoordinateSlab P1ActualMovingPrimeIntervalEnvelope
open P1OriginalFourthMovingPrimeIntervalBound

def lower : Fin 6 → ℝ := fun _ => 53 / 4608
def upper : Fin 6 → ℝ := fun _ => 19 / 96
def radius (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

theorem radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity
theorem radius_tendsto : Tendsto radius atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def rowTuples (r : Row) (n N : ℕ) : Finset (Fin 6 → ℕ) :=
  (actualPrimeBoxTuples N lower upper).filter
    (fun p => |r.eval (actualPrimeTupleLog N p)| ≤ radius n)

def rowMass (r : Row) (n N : ℕ) : ℝ :=
  ∑ p ∈ rowTuples r n N, tupleWeight p

def omittedMass (c : Cell) (n N : ℕ) : ℝ :=
  ∑ p ∈ omittedTuples c n N, tupleWeight p

theorem original_tuple_mem_positive_box (c : Cell) (N : ℕ) (hN : 1 < N)
    {p : Fin 6 → ℕ} (hp : p ∈ originalTuples c N) :
    p ∈ actualPrimeBoxTuples N lower upper := by
  obtain ⟨hpbox,hc⟩ := Finset.mem_filter.mp hp
  have hraw := (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hpbox
  apply (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
  refine ⟨hraw.1,mem_logPrimeBox.mpr (fun i => ⟨?_,(mem_logPrimeBox.mp hraw.2 i).2⟩)⟩
  have hlo : (53 / 4608 : ℝ) < actualPrimeTupleLog N p i := by
    fin_cases i <;> linarith [hc.compactCutoff,hc.order.1,hc.order.2.1,
      hc.order.2.2.1,hc.order.2.2.2.1,hc.order.2.2.2.2]
  exact hlo.le

theorem rowMass_nonneg (r : Row) (n N : ℕ) : 0 ≤ rowMass r n N := by
  apply Finset.sum_nonneg
  intro p hp
  exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

theorem rowMass_eq_affine (r : Row) (n N : ℕ) :
    rowMass r n N = affineSlabMass N lower upper
      (fun i => (r.coefficient i : ℝ)) (-(r.constant : ℝ)) (radius n) := by
  have hs : rowTuples r n N = affineSlabTuples N lower upper
      (fun i => (r.coefficient i : ℝ)) (-(r.constant : ℝ)) (radius n) := by
    apply Finset.filter_congr
    intro p hp
    have he : r.eval (actualPrimeTupleLog N p) =
        affineValue (fun i => (r.coefficient i : ℝ)) (actualPrimeTupleLog N p) -
          (-(r.constant : ℝ)) := by
      simp only [Row.eval,affineValue]
      ring
    rw [he]
  simp only [rowMass,affineSlabMass,hs]

/-- Two independent thresholds.  In particular the proof does not choose
the mesh/table at the moving index n=N. -/
theorem proper_row_uniform_rectangle (r : Row)
    (hr : (∃ j : Fin 6, r.coefficient j ≠ 0) ∨
      ((∀ j : Fin 6, r.coefficient j = 0) ∧ r.constant ≠ 0))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N → rowMass r n N < eps := by
  rcases hr with ⟨j,hj⟩ | ⟨hcoeff,hconst⟩
  · let v : Fin 6 → ℝ := fun i => r.coefficient i
    have hv : v j ≠ 0 := by exact_mod_cast hj
    have ha : ∀ i, 0 < lower i := by intro i; norm_num [lower]
    have hab : ∀ i, lower i < upper i := by intro i; norm_num [lower,upper]
    let a := j.removeNth lower
    let b := j.removeNth upper
    let limit : ℝ := ∏ i : Fin 5, Real.log (b i / a i)
    let B : ℝ := |limit| + 1
    have hB : 0 < B := by dsimp [B]; positivity
    have hlimit : limit < B := by dsimp [B]; linarith [le_abs_self limit]
    have hbox : Tendsto (fun N : ℕ => actualPrimeBoxMass N a b) atTop (𝓝 limit) :=
      tendsto_actualPrimeBoxMass a b (fun i => ha (j.succAbove i))
        (fun i => hab (j.succAbove i))
    obtain ⟨K,hK,hinterval⟩ := exists_uniform_reciprocal_interval_bound
    have hmain : Tendsto (fun n => 2 * (radius n / |v j|) / lower j)
        atTop (𝓝 0) := by
      simpa only [zero_div,mul_zero] using
        ((radius_tendsto.div_const |v j|).const_mul 2).div_const (lower j)
    obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp
      (hmain.eventually (gt_mem_nhds (div_pos heps (by positivity : 0 < 2*B))))
    have hzero : Tendsto (fun N : ℕ => envelope K (lower j) (upper j) 0 N)
        atTop (𝓝 0) :=
      tendsto_envelope_zero K _ _ (ha j) (hab j) (fun _ => 0) tendsto_const_nhds
    have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ lower j) atTop atTop :=
      (tendsto_rpow_atTop (ha j)).comp tendsto_natCast_atTop_atTop
    have hevent : ∀ᶠ N : ℕ in atTop,
        2 ≤ N ∧ 3 ≤ (N : ℝ) ^ lower j ∧ actualPrimeBoxMass N a b < B ∧
          envelope K (lower j) (upper j) 0 N < eps/(2*B) := by
      filter_upwards [eventually_ge_atTop (2 : ℕ),
        hp.eventually (eventually_ge_atTop (3 : ℝ)),
        hbox.eventually (gt_mem_nhds hlimit),
        hzero.eventually (gt_mem_nhds (div_pos heps (by positivity : 0 < 2*B)))]
        with N hN hA hM hE
      exact ⟨hN,hA,hM,hE⟩
    obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hevent
    refine ⟨n₀,max 2 N₀,le_max_left _ _,?_⟩
    intro n hn N hN
    obtain ⟨hN2,hA,hM,hE⟩ := hN₀ N ((le_max_right _ _).trans hN)
    have hmainlt := hn₀ n hn
    have hEl : envelope K (lower j) (upper j) (radius n/|v j|) N < eps/B := by
      have hsplit : eps/(2*B) + eps/(2*B) = eps/B := by
        field_simp [hB.ne']
        <;> ring
      dsimp only [envelope] at hE ⊢
      linarith
    have hmass := affineSlabMass_le_envelope K (by linarith) hinterval N (by omega)
      lower upper v j hv (ha j) (hab j) (-(r.constant : ℝ)) (radius n)
      (radius_pos n).le hA
    rw [← rowMass_eq_affine] at hmass
    have hM0 : 0 ≤ actualPrimeBoxMass N a b := actualPrimeBoxMass_nonneg N a b
    have hprod : envelope K (lower j) (upper j) (radius n/|v j|) N *
        actualPrimeBoxMass N a b < eps := by
      calc
        _ ≤ (eps/B)*actualPrimeBoxMass N a b :=
          mul_le_mul_of_nonneg_right hEl.le hM0
        _ < (eps/B)*B := mul_lt_mul_of_pos_left hM (div_pos heps hB)
        _ = eps := div_mul_cancel₀ eps hB.ne'
    exact hmass.trans_lt hprod
  · have hc : (0 : ℝ) < |(r.constant : ℝ)| := by
      apply abs_pos.mpr
      exact_mod_cast hconst
    obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp (radius_tendsto.eventually (gt_mem_nhds hc))
    refine ⟨n₀,2,le_rfl,?_⟩
    intro n hn N hN
    have hempty : rowTuples r n N = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro p hp
      have hh := (Finset.mem_filter.mp hp).2
      simp only [Row.eval,hcoeff,Rat.cast_zero,zero_mul,Finset.sum_const_zero,add_zero] at hh
      exact (not_le.mpr (hn₀ n hn)) hh
    simpa only [rowMass,hempty,Finset.sum_empty] using heps

theorem omittedMass_nonneg (c : Cell) (n N : ℕ) : 0 ≤ omittedMass c n N := by
  apply Finset.sum_nonneg
  intro p hp
  exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1

/-- A finite union estimate on the actual target-deleted prime carrier.
Overlapping strips may overcount on the right; no atom is discarded. -/
theorem omittedMass_le_rows (c : Cell) (n N : ℕ) (hN : 1 < N) :
    omittedMass c n N ≤ ∑ i : RowIndex, rowMass (sourceRow c i) n N := by
  let box := actualPrimeBoxTuples N lower upper
  have hsub : omittedTuples c n N ⊆ box := by
    intro p hp
    exact original_tuple_mem_positive_box c N hN (Finset.mem_filter.mp hp).1
  have hfilter : box.filter (fun p => p ∈ omittedTuples c n N) = omittedTuples c n N := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hsub h,h⟩⟩
  have hpwise (p : Fin 6 → ℕ) (hp : p ∈ box) :
      (if p ∈ omittedTuples c n N then tupleWeight p else 0) ≤
        ∑ i : RowIndex, if |(sourceRow c i).eval (actualPrimeTupleLog N p)| ≤ radius n
          then tupleWeight p else 0 := by
    have hw : 0 ≤ tupleWeight p := actualPrimeBoxWeight_nonneg hp
    have hnneg (i : RowIndex) : 0 ≤
        (if |(sourceRow c i).eval (actualPrimeTupleLog N p)| ≤ radius n
          then tupleWeight p else 0) := by split_ifs <;> positivity
    by_cases ho : p ∈ omittedTuples c n N
    · obtain ⟨hpold,hout⟩ := Finset.mem_filter.mp ho
      have hc := (Finset.mem_filter.mp hpold).2
      obtain ⟨i,hi0,hi⟩ := omitted_has_positive_row c n (actualPrimeTupleLog N p) ⟨hc,hout⟩
      have hit : |(sourceRow c i).eval (actualPrimeTupleLog N p)| ≤ radius n := by
        rw [abs_of_pos hi0]
        exact hi.le
      rw [if_pos ho]
      simpa only [if_pos hit] using
        Finset.single_le_sum (fun j _ => hnneg j) (Finset.mem_univ i)
    · rw [if_neg ho]
      exact Finset.sum_nonneg (fun i _ => hnneg i)
  calc
    omittedMass c n N = ∑ p ∈ box,
        if p ∈ omittedTuples c n N then tupleWeight p else 0 := by
      rw [omittedMass,← Finset.sum_filter,hfilter]
    _ ≤ ∑ p ∈ box, ∑ i : RowIndex,
        if |(sourceRow c i).eval (actualPrimeTupleLog N p)| ≤ radius n
          then tupleWeight p else 0 := Finset.sum_le_sum hpwise
    _ = _ := by rw [Finset.sum_comm]; simp only [rowMass,rowTuples,Finset.sum_filter]

local instance : Fintype Cell :=
  ⟨allCells.toFinset,fun c => List.mem_toFinset.mpr (allCells_complete c)⟩

/-- ONE compact index works for all eleven original cells and every larger
index; then ONE target threshold works for all N, including all even N. -/
theorem exists_common_omittedMass_rectangle (eps : ℝ) (heps : 0 < eps) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N →
      ∀ c : Cell, omittedMass c n N < eps := by
  let count : ℝ := Fintype.card RowIndex + 1
  have hcount : 0 < count := by dsimp [count]; positivity
  choose n₀ N₀ hN₀ hbound using fun c i => proper_row_uniform_rectangle
    (sourceRow c i) (sourceRow_nontrivial c i) (eps/count) (div_pos heps hcount)
  let nstar : ℕ := Finset.univ.sup (fun c : Cell => Finset.univ.sup (n₀ c))
  let Nstar : ℕ := max 2 (Finset.univ.sup (fun c : Cell => Finset.univ.sup (N₀ c)))
  refine ⟨nstar,Nstar,le_max_left _ _,?_⟩
  intro n hn N hN c
  have hrow (i : RowIndex) : rowMass (sourceRow c i) n N ≤ eps/count := by
    apply (hbound c i n _ N _).le
    · exact (Finset.le_sup (f := n₀ c) (Finset.mem_univ i)).trans
        ((Finset.le_sup (f := fun c : Cell => Finset.univ.sup (n₀ c))
          (Finset.mem_univ c)).trans hn)
    · exact (Finset.le_sup (f := N₀ c) (Finset.mem_univ i)).trans
        ((Finset.le_sup (f := fun c : Cell => Finset.univ.sup (N₀ c))
          (Finset.mem_univ c)).trans ((le_max_right _ _).trans hN))
  have hs : (∑ i : RowIndex, rowMass (sourceRow c i) n N) ≤
      (Fintype.card RowIndex : ℝ)*(eps/count) := by
    calc
      _ ≤ ∑ _i : RowIndex, eps/count := Finset.sum_le_sum (fun i _ => hrow i)
      _ = _ := by simp
  have hstrict : (Fintype.card RowIndex : ℝ)*(eps/count) < eps := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hcount).2
    dsimp [count]
    nlinarith
  exact (omittedMass_le_rows c n N (by have := (le_max_left 2 _).trans hN; omega)).trans_lt
    (hs.trans_lt hstrict)

def signedOmitted (c : Cell) (n N : ℕ) (F : (Fin 6 → ℕ) → ℝ) : ℝ :=
  ∑ p ∈ omittedTuples c n N, tupleWeight p * F p

theorem abs_signedOmitted_le (c : Cell) (n N : ℕ) (F : (Fin 6 → ℕ) → ℝ) (B : ℝ)
    (hb : ∀ p ∈ omittedTuples c n N, |F p| ≤ B) :
    |signedOmitted c n N F| ≤ B * omittedMass c n N := by
  calc
    _ ≤ ∑ p ∈ omittedTuples c n N, |tupleWeight p * F p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ omittedTuples c n N, B * tupleWeight p := by
      apply Finset.sum_le_sum
      intro p hp
      have hw : 0 ≤ tupleWeight p := actualPrimeBoxWeight_nonneg
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
      rw [abs_mul,abs_of_nonneg hw]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb p hp) hw
    _ = _ := by rw [omittedMass,Finset.mul_sum]

theorem exists_common_signedOmitted_rectangle (B : ℝ) (hB : 0 ≤ B) (eps : ℝ) (heps : 0 < eps) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N → ∀ c F,
      (∀ p ∈ omittedTuples c n N, |F p| ≤ B) → |signedOmitted c n N F| < eps := by
  have hp : 0 < B+1 := by linarith
  obtain ⟨n₀,N₀,hN₀,h⟩ := exists_common_omittedMass_rectangle (eps/(B+1)) (div_pos heps hp)
  refine ⟨n₀,N₀,hN₀,?_⟩
  intro n hn N hN c F hb
  have hm := h n hn N hN c
  have hmul := mul_lt_mul_of_pos_left hm hp
  have hcancel : (B+1)*(eps/(B+1)) = eps := by field_simp [hp.ne']
  rw [hcancel] at hmul
  exact (abs_signedOmitted_le c n N F B hb).trans_lt
    ((mul_le_mul_of_nonneg_right (show B ≤ B+1 by linarith) (omittedMass_nonneg c n N)).trans_lt hmul)

end
end ImbalancedChen.P2OriginalSixthOmittedArithmeticMass
