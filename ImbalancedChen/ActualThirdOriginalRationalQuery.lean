import ImbalancedChen.ActualThirdOriginalLiteralNodes

/-!
SOURCEONLY / UNCOMPILED / OPEN30.
Original IndependentSieve.at rational queries on the entire closed[2,12].
The literal node theorem is an explicit dependency, not a query-bound premise.
No node induction, adaptive leaf/tree or saved U2 numeral is repeated here.
The rational floors/ceilings below are bound to the original integer divmod
and signed integer divisions by exact algebra at the end of this tail.
-/

namespace ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly

noncomputable section
open Set

private theorem queryP_pos : (0 : ℝ) < (originalWeightP : ℝ) := by
  norm_num [originalWeightP]

theorem query_floor_div_literal (x d : ℤ) (hd : 0 < d) :
    ⌊(x : ℚ)/(d : ℚ)⌋ = x/d := by
  simpa using Int.floor_div_cast_of_nonneg (k := ℚ) hd.le (x : ℚ)

theorem query_ceil_div_literal (x d : ℤ) (hd : 0 < d) :
    ⌈(x : ℚ)/(d : ℚ)⌉ = -(-x/d) := by
  have hneg : ⌈(x : ℚ)/(d : ℚ)⌉ = -⌊-((x : ℚ)/(d : ℚ))⌋ := by
    have h := Int.floor_neg (a := (x : ℚ)/(d : ℚ))
    omega
  rw [hneg, show -((x : ℚ)/(d : ℚ)) = ((-x : ℤ) : ℚ)/(d : ℚ) by simp only [Int.cast_neg, neg_div],
    query_floor_div_literal (-x) d hd]

/-- Original query-cell curvature ceiling, distinct from the integrated
node-update allowance with denominator12. -/
def queryErrorDen (i : ℕ) : ℤ := 8*16384*((i : ℤ)-16384)
def queryError (i : ℕ) : ℤ := -(-originalWeightP/queryErrorDen i)

theorem query_error_rounds_up (i : ℕ) (hi : 32768 ≤ i) :
    1/(8*16384*((i : ℝ)-16384)) ≤ nodeValue (queryError i) := by
  have hiZ : (32768 : ℤ) ≤ (i : ℤ) := by exact_mod_cast hi
  have hd : 0 < queryErrorDen i := by
    unfold queryErrorDen
    have hD : 0 < (i : ℤ)-16384 := by omega
    positivity
  have h := Int.le_ceil ((originalWeightP : ℚ)/(queryErrorDen i : ℚ))
  rw [query_ceil_div_literal originalWeightP (queryErrorDen i) hd] at h
  have hR : (originalWeightP : ℝ)/(queryErrorDen i : ℝ) ≤ (queryError i : ℝ) := by
    exact_mod_cast h
  have hs := div_le_div_of_nonneg_right hR queryP_pos.le
  have he : ((originalWeightP : ℝ)/(queryErrorDen i : ℝ))/(originalWeightP : ℝ) =
      1/(8*16384*((i : ℝ)-16384)) := by
    calc
      _ = ((originalWeightP : ℝ)/(originalWeightP : ℝ))/(queryErrorDen i : ℝ) := by ring
      _ = _ := by rw [div_self queryP_pos.ne']; norm_num [queryErrorDen]
  rw [he] at hs
  exact hs

/-- Exact rational form of the residual divmod interpolation coefficient. -/
def queryCellWeight (i : ℕ) (q : ℚ) : ℚ := 16384*q-(i : ℚ)

def queryInterpolationLo (i : ℕ) (q : ℚ) : ℤ :=
  ⌊((originalFinalNodes i).Llo : ℚ)*(1-queryCellWeight i q)+
    ((originalFinalNodes (i+1)).Llo : ℚ)*queryCellWeight i q⌋

def queryInterpolationHi (i : ℕ) (q : ℚ) : ℤ :=
  ⌈((originalFinalNodes i).Lhi : ℚ)*(1-queryCellWeight i q)+
    ((originalFinalNodes (i+1)).Lhi : ℚ)*queryCellWeight i q⌉

/-- One arbitrary original cell, with its literal node values and exact
query curvature ceiling. The node intervals are proved by the actual V2
node theorem; no endpoint/query enclosure is passed by the caller. -/
theorem original_general_cell_numerator_encloses
    (i : ℕ) (hi : 32768 ≤ i) (hnext : i+1 ≤ 196608)
    {q : ℚ} (hql : (i : ℚ)/16384 ≤ q) (hqr : q ≤ ((i : ℚ)+1)/16384) :
    nodeValue (queryInterpolationLo i q) ≤ L (q : ℝ) ∧
      L (q : ℝ) ≤ nodeValue (queryInterpolationHi i q+queryError i) := by
  have h0 := (originalFinalNodes_enclose_actual i hi (by omega)).1
  have h1 := (originalFinalNodes_enclose_actual (i+1) (by omega) hnext).1
  have hright : cellRight i = cellLeft (i+1) := by simp [cellRight, cellLeft]
  rw [← hright] at h1
  have hw0Q : 0 ≤ queryCellWeight i q := by unfold queryCellWeight; linarith
  have hw1Q : queryCellWeight i q ≤ 1 := by unfold queryCellWeight; linarith
  have hw0 : (0 : ℝ) ≤ (queryCellWeight i q : ℝ) := by exact_mod_cast hw0Q
  have hw1 : (queryCellWeight i q : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hw1Q
  have hrest : (0 : ℝ) ≤ 1-(queryCellWeight i q : ℝ) := by linarith
  have ht : (q : ℝ) ∈ Icc (cellLeft i) (cellRight i) := by
    constructor
    · dsimp [cellLeft]
      simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
        (Rat.cast_mono (K := ℝ) hql)
    · dsimp [cellRight]
      simpa only [Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one,
        Rat.cast_ofNat] using (Rat.cast_mono (K := ℝ) hqr)
  have hchord : endpointChord L (cellLeft i) (cellRight i) (q : ℝ) =
      (1-(queryCellWeight i q : ℝ))*L (cellLeft i)+
        (queryCellWeight i q : ℝ)*L (cellRight i) := by
    unfold endpointChord
    simp only [original_cell_width]
    dsimp [cellLeft, cellRight, queryCellWeight]
    push_cast
    ring
  have hfloor : (queryInterpolationLo i q : ℝ) ≤
      ((originalFinalNodes i).Llo : ℝ)*(1-(queryCellWeight i q : ℝ))+
        ((originalFinalNodes (i+1)).Llo : ℝ)*(queryCellWeight i q : ℝ) := by
    exact_mod_cast (Int.floor_le
      (((originalFinalNodes i).Llo : ℚ)*(1-queryCellWeight i q)+
        ((originalFinalNodes (i+1)).Llo : ℚ)*queryCellWeight i q))
  have hceil :
      ((originalFinalNodes i).Lhi : ℝ)*(1-(queryCellWeight i q : ℝ))+
        ((originalFinalNodes (i+1)).Lhi : ℝ)*(queryCellWeight i q : ℝ) ≤
      (queryInterpolationHi i q : ℝ) := by
    exact_mod_cast (Int.le_ceil
      (((originalFinalNodes i).Lhi : ℚ)*(1-queryCellWeight i q)+
        ((originalFinalNodes (i+1)).Lhi : ℚ)*queryCellWeight i q))
  have hloRound : nodeValue (queryInterpolationLo i q) ≤
      (1-(queryCellWeight i q : ℝ))*nodeValue (originalFinalNodes i).Llo+
        (queryCellWeight i q : ℝ)*nodeValue (originalFinalNodes (i+1)).Llo := by
    have h := div_le_div_of_nonneg_right hfloor queryP_pos.le
    calc
      nodeValue (queryInterpolationLo i q) ≤
          (((originalFinalNodes i).Llo : ℝ)*(1-(queryCellWeight i q : ℝ))+
            ((originalFinalNodes (i+1)).Llo : ℝ)*(queryCellWeight i q : ℝ))/
              (originalWeightP : ℝ) := h
      _ = (1-(queryCellWeight i q : ℝ))*nodeValue (originalFinalNodes i).Llo+
          (queryCellWeight i q : ℝ)*nodeValue (originalFinalNodes (i+1)).Llo := by
        unfold nodeValue
        ring
  have hhiRound :
      (1-(queryCellWeight i q : ℝ))*nodeValue (originalFinalNodes i).Lhi+
        (queryCellWeight i q : ℝ)*nodeValue (originalFinalNodes (i+1)).Lhi ≤
      nodeValue (queryInterpolationHi i q) := by
    have h := div_le_div_of_nonneg_right hceil queryP_pos.le
    calc
      (1-(queryCellWeight i q : ℝ))*nodeValue (originalFinalNodes i).Lhi+
          (queryCellWeight i q : ℝ)*nodeValue (originalFinalNodes (i+1)).Lhi =
          (((originalFinalNodes i).Lhi : ℝ)*(1-(queryCellWeight i q : ℝ))+
            ((originalFinalNodes (i+1)).Lhi : ℝ)*(queryCellWeight i q : ℝ))/
              (originalWeightP : ℝ) := by
        unfold nodeValue
        ring
      _ ≤ nodeValue (queryInterpolationHi i q) := h
  have hloChord : nodeValue (queryInterpolationLo i q) ≤
      endpointChord L (cellLeft i) (cellRight i) (q : ℝ) := by
    rw [hchord]
    exact hloRound.trans (add_le_add (mul_le_mul_of_nonneg_left h0.1 hrest)
      (mul_le_mul_of_nonneg_left h1.1 hw0))
  have hhiChord : endpointChord L (cellLeft i) (cellRight i) (q : ℝ) ≤
      nodeValue (queryInterpolationHi i q) := by
    rw [hchord]
    exact (add_le_add (mul_le_mul_of_nonneg_left h0.2 hrest)
      (mul_le_mul_of_nonneg_left h1.2 hw0)).trans hhiRound
  have hs := original_L_cell_chord i hi ht
  have herr := hs.2.1.trans hs.2.2
  have he := query_error_rounds_up i hi
  constructor
  · exact hloChord.trans (by linarith only [hs.1])
  · rw [nodeValue_add]
    linarith only [herr, hhiChord, he]

def originalQueryIndex (q : ℚ) : ℕ := ⌊q*16384⌋₊

/-- All compact queries own one legal node; non-grid queries will own the
next node as well. The strict right inequality prevents access past12*n. -/
theorem original_query_cell_geometry {q : ℚ} (hq2 : 2 ≤ q) (hq12 : q ≤ 12) :
    32768 ≤ originalQueryIndex q ∧ originalQueryIndex q ≤ 196608 ∧
    0 ≤ queryCellWeight (originalQueryIndex q) q ∧
    queryCellWeight (originalQueryIndex q) q < 1 ∧
    (originalQueryIndex q : ℚ)/16384 ≤ q ∧
    q < ((originalQueryIndex q : ℚ)+1)/16384 := by
  have hnonneg : (0 : ℚ) ≤ q*16384 := by linarith
  have hfloor : (originalQueryIndex q : ℚ) ≤ q*16384 := Nat.floor_le hnonneg
  have hnext : q*16384 < (originalQueryIndex q : ℚ)+1 := Nat.lt_floor_add_one _
  have hlo : 32768 ≤ originalQueryIndex q := by
    have h := Nat.floor_mono (by linarith : (32768 : ℚ) ≤ q*16384)
    simpa only [Nat.floor_ofNat, originalQueryIndex] using h
  have hhi : originalQueryIndex q ≤ 196608 := by
    have h := Nat.floor_mono (by linarith : q*16384 ≤ (196608 : ℚ))
    simpa only [Nat.floor_ofNat, originalQueryIndex] using h
  refine ⟨hlo, hhi, ?_, ?_, ?_, ?_⟩
  · unfold queryCellWeight
    linarith
  · unfold queryCellWeight
    linarith
  · linarith
  · linarith

def originalQueryNumeratorLo (q : ℚ) : ℤ :=
  let i := originalQueryIndex q
  if queryCellWeight i q=0 then (originalFinalNodes i).Llo else queryInterpolationLo i q

def originalQueryNumeratorHi (q : ℚ) : ℤ :=
  let i := originalQueryIndex q
  if queryCellWeight i q=0 then (originalFinalNodes i).Lhi else
    queryInterpolationHi i q+queryError i

theorem original_compact_numerator_encloses {q : ℚ}
    (hq2 : 2 ≤ q) (hq12 : q ≤ 12) :
    nodeValue (originalQueryNumeratorLo q) ≤ L (q : ℝ) ∧
      L (q : ℝ) ≤ nodeValue (originalQueryNumeratorHi q) := by
  have hg := original_query_cell_geometry hq2 hq12
  by_cases hz : queryCellWeight (originalQueryIndex q) q=0
  · have hqgrid : q = (originalQueryIndex q : ℚ)/16384 := by
      unfold queryCellWeight at hz
      linarith
    have hqgridR : (q : ℝ) = cellLeft (originalQueryIndex q) := by
      dsimp [cellLeft]
      simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
        congrArg (fun r : ℚ => (r : ℝ)) hqgrid
    have h := (originalFinalNodes_enclose_actual (originalQueryIndex q) hg.1 hg.2.1).1
    simpa only [originalQueryNumeratorLo, originalQueryNumeratorHi, if_pos hz, hqgridR] using h
  · have hwpos : 0 < queryCellWeight (originalQueryIndex q) q :=
      lt_of_le_of_ne hg.2.2.1 (Ne.symm hz)
    have hiQ : (originalQueryIndex q : ℚ) < 196608 := by
      unfold queryCellWeight at hwpos
      linarith
    have hi : originalQueryIndex q < 196608 := by exact_mod_cast hiQ
    have h := original_general_cell_numerator_encloses (originalQueryIndex q)
      hg.1 (by omega) hg.2.2.2.2.1 hg.2.2.2.2.2.le
    simpa only [originalQueryNumeratorLo, originalQueryNumeratorHi, if_neg hz] using h

/-- Literal IndependentSieve.at branches: zero clamp,terminal fallback,
then the second outward division. The theorem below concerns[2,12],so the
fallback above12 is recorded exactly but is not used in its proof. -/
def originalQueryLo112 (q : ℚ) : ℤ :=
  if q ≤ 2 then 0 else if 12 < q then (originalFinalNodes 196608).Llo/12 else
    ⌊(originalQueryNumeratorLo q : ℚ)/q⌋

def originalQueryHi112 (q : ℚ) : ℤ :=
  if q ≤ 2 then 0 else if 12 < q then -(-(originalFinalNodes 196608).Hhi/12) else
    ⌈(originalQueryNumeratorHi q : ℚ)/q⌉

/-- Every rational query in the ENTIRE closed compact interval. Exact grid
nodes use their own values with no curvature charge or successor access;
off-grid queries use the original local ceiling and both rounding stages. -/
theorem original_compact_query_112bit_encloses {q : ℚ}
    (hq2 : 2 ≤ q) (hq12 : q ≤ 12) :
    nodeValue (originalQueryLo112 q) ≤ actualExtendedThirdLowerFactor (q : ℝ) ∧
      actualExtendedThirdLowerFactor (q : ℝ) ≤ nodeValue (originalQueryHi112 q) := by
  by_cases hclamp : q ≤ 2
  · have hqR : (q : ℝ) ≤ 2 := by exact_mod_cast hclamp
    rw [actualExtendedThirdLowerFactor_of_le_two hqR]
    norm_num [originalQueryLo112, originalQueryHi112, hclamp, nodeValue]
  · have hqpos : (0 : ℚ) < q := by linarith
    have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
    have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    have hnotfar : ¬ 12 < q := not_lt.mpr hq12
    have hn := original_compact_numerator_encloses hq2 hq12
    have hactual : L (q : ℝ)/(q : ℝ) = actualExtendedThirdLowerFactor (q : ℝ) := by
      simp [L, hqposR.ne', lower_eq_actual hq2R]
    have hlo : (⌊(originalQueryNumeratorLo q : ℚ)/q⌋ : ℝ) ≤
        (originalQueryNumeratorLo q : ℝ)/(q : ℝ) := by
      exact_mod_cast Int.floor_le ((originalQueryNumeratorLo q : ℚ)/q)
    have hhi : (originalQueryNumeratorHi q : ℝ)/(q : ℝ) ≤
        (⌈(originalQueryNumeratorHi q : ℚ)/q⌉ : ℝ) := by
      exact_mod_cast Int.le_ceil ((originalQueryNumeratorHi q : ℚ)/q)
    simp only [originalQueryLo112, originalQueryHi112, if_neg hclamp, if_neg hnotfar]
    rw [← hactual]
    constructor
    · calc
        nodeValue ⌊(originalQueryNumeratorLo q : ℚ)/q⌋ ≤
            ((originalQueryNumeratorLo q : ℝ)/(q : ℝ))/(originalWeightP : ℝ) :=
          div_le_div_of_nonneg_right hlo queryP_pos.le
        _ = nodeValue (originalQueryNumeratorLo q)/(q : ℝ) := by unfold nodeValue; ring
        _ ≤ _ := div_le_div_of_nonneg_right hn.1 hqposR.le
    · calc
        L (q : ℝ)/(q : ℝ) ≤ nodeValue (originalQueryNumeratorHi q)/(q : ℝ) :=
          div_le_div_of_nonneg_right hn.2 hqposR.le
        _ = ((originalQueryNumeratorHi q : ℝ)/(q : ℝ))/(originalWeightP : ℝ) := by
          unfold nodeValue
          ring
        _ ≤ nodeValue ⌈(originalQueryNumeratorHi q : ℚ)/q⌉ :=
          div_le_div_of_nonneg_right hhi queryP_pos.le

def originalQueryLo160 (q : ℚ) : ℤ := originalQueryLo112 q*2^48
def originalQueryHi160 (q : ℚ) : ℤ := originalQueryHi112 q*2^48

theorem original_compact_query_160bit_encloses {q : ℚ}
    (hq2 : 2 ≤ q) (hq12 : q ≤ 12) :
    (originalQueryLo160 q : ℝ)/2^160 ≤ actualExtendedThirdLowerFactor (q : ℝ) ∧
      actualExtendedThirdLowerFactor (q : ℝ) ≤ (originalQueryHi160 q : ℝ)/2^160 := by
  have hs (z : ℤ) : (((z*2^48 : ℤ) : ℝ)/2^160) = nodeValue z := by
    dsimp [nodeValue]
    push_cast
    norm_num [originalWeightP]
    ring
  simp only [originalQueryLo160, originalQueryHi160, hs]
  exact original_compact_query_112bit_encloses hq2 hq12

/-- The closed right endpoint is an exact node. No next-node access occurs
in originalQueryNumeratorLo/Hi whenq=12. -/
theorem original_query_right_endpoint_grid :
    originalQueryIndex (12 : ℚ)=196608 ∧
      queryCellWeight (originalQueryIndex (12 : ℚ)) 12=0 := by
  norm_num [originalQueryIndex, queryCellWeight]

/-- Integer-divmod binding for any positive-denominator representationq=a/b.
The natural floor is exactly the nonnegative original integer quotient. -/
theorem original_query_index_literal_divmod (a b : ℤ) (hb : 0 < b) (ha : 0 ≤ a) :
    (originalQueryIndex ((a : ℚ)/(b : ℚ)) : ℤ) = a*16384/b := by
  have hbQ : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have haQ : (0 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  unfold originalQueryIndex
  rw [Int.natCast_floor_eq_floor (by positivity : (0 : ℚ) ≤ ((a : ℚ)/(b : ℚ))*16384)]
  have he : ((a : ℚ)/(b : ℚ))*16384 = ((a*16384 : ℤ) : ℚ)/(b : ℚ) := by
    push_cast
    ring
  rw [he, query_floor_div_literal (a*16384) b hb]

theorem original_query_weight_literal_divmod (a b : ℤ) (hb : 0 < b) (ha : 0 ≤ a) :
    queryCellWeight (originalQueryIndex ((a : ℚ)/(b : ℚ))) ((a : ℚ)/(b : ℚ)) =
      ((a*16384 % b : ℤ) : ℚ)/(b : ℚ) := by
  have hi : (originalQueryIndex ((a : ℚ)/(b : ℚ)) : ℚ) =
      ((a*16384/b : ℤ) : ℚ) := by
    exact_mod_cast original_query_index_literal_divmod a b hb ha
  unfold queryCellWeight
  rw [hi, Int.emod_def]
  push_cast
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp [hbQ]

theorem original_query_exact_grid_iff_literal (a b : ℤ) (hb : 0 < b) (ha : 0 ≤ a) :
    queryCellWeight (originalQueryIndex ((a : ℚ)/(b : ℚ))) ((a : ℚ)/(b : ℚ))=0 ↔
      a*16384%b=0 := by
  rw [original_query_weight_literal_divmod a b hb ha]
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with hnum | hden
    · exact_mod_cast hnum
    · exact (hbQ hden).elim
  · intro h
    rw [h]
    simp

theorem original_query_clamps_literal (a b : ℤ) (hb : 0 < b) :
    (((a : ℚ)/(b : ℚ) ≤ 2) ↔ a ≤ 2*b) ∧
      ((12 < (a : ℚ)/(b : ℚ)) ↔ 12*b < a) := by
  have hbQ : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  constructor
  · rw [div_le_iff₀ hbQ]
    norm_cast
  · rw [lt_div_iff₀ hbQ]
    norm_cast

/-- Exact binding of each interpolation floor/ceiling to the original
integer formula(z0*(b-r)+z1*r)//b, r=divmod(a*n,b). It applies independently
to the selected lower or upper endpoint integers and changes no precision. -/
theorem original_query_interpolation_literal (a b z0 z1 : ℤ)
    (hb : 0 < b) (ha : 0 ≤ a) :
    (⌊(z0 : ℚ)*(1-queryCellWeight (originalQueryIndex ((a : ℚ)/(b : ℚ)))
          ((a : ℚ)/(b : ℚ)))+
        (z1 : ℚ)*queryCellWeight (originalQueryIndex ((a : ℚ)/(b : ℚ)))
          ((a : ℚ)/(b : ℚ))⌋ =
      (z0*(b-a*16384%b)+z1*(a*16384%b))/b) ∧
    (⌈(z0 : ℚ)*(1-queryCellWeight (originalQueryIndex ((a : ℚ)/(b : ℚ)))
          ((a : ℚ)/(b : ℚ)))+
        (z1 : ℚ)*queryCellWeight (originalQueryIndex ((a : ℚ)/(b : ℚ)))
          ((a : ℚ)/(b : ℚ))⌉ =
      -(-(z0*(b-a*16384%b)+z1*(a*16384%b))/b)) := by
  simp only [original_query_weight_literal_divmod a b hb ha]
  have he : (z0 : ℚ)*(1-((a*16384%b : ℤ) : ℚ)/(b : ℚ))+
      (z1 : ℚ)*(((a*16384%b : ℤ) : ℚ)/(b : ℚ)) =
      ((z0*(b-a*16384%b)+z1*(a*16384%b) : ℤ) : ℚ)/(b : ℚ) := by
    push_cast
    have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    field_simp [hbQ]
  simp only [he]
  exact ⟨query_floor_div_literal _ b hb, query_ceil_div_literal _ b hb⟩

/-- The second query division is exactly the original multiply-byb,
divide-bya rule, including the signed-integer ceiling. -/
theorem original_query_final_division_literal (a b z : ℤ) (ha : 0 < a) :
    (⌊(z : ℚ)/((a : ℚ)/(b : ℚ))⌋ = z*b/a) ∧
      (⌈(z : ℚ)/((a : ℚ)/(b : ℚ))⌉ = -(-(z*b)/a)) := by
  have he : (z : ℚ)/((a : ℚ)/(b : ℚ)) = ((z*b : ℤ) : ℚ)/(a : ℚ) := by
    push_cast
    rw [div_div_eq_mul_div]
  rw [he]
  exact ⟨query_floor_div_literal _ a ha, query_ceil_div_literal _ a ha⟩

/-- Literal Python integer quotient, cast to a natural array index only in
the mathematical definition. Its equality to the legal floor index is proved. -/
def literalQueryIndex (a b : ℤ) : ℕ := (a*16384/b).toNat

def literalQueryNumeratorLo (a b : ℤ) : ℤ :=
  let i := literalQueryIndex a b
  let r := a*16384%b
  if r=0 then (originalFinalNodes i).Llo else
    ((originalFinalNodes i).Llo*(b-r)+(originalFinalNodes (i+1)).Llo*r)/b

def literalQueryNumeratorHi (a b : ℤ) : ℤ :=
  let i := literalQueryIndex a b
  let r := a*16384%b
  if r=0 then (originalFinalNodes i).Lhi else
    -(-((originalFinalNodes i).Lhi*(b-r)+(originalFinalNodes (i+1)).Lhi*r)/b)+
      queryError i

def literalQueryLo112 (a b : ℤ) : ℤ :=
  if a ≤ 2*b then 0 else if 12*b < a then (originalFinalNodes 196608).Llo/12 else
    literalQueryNumeratorLo a b*b/a

def literalQueryHi112 (a b : ℤ) : ℤ :=
  if a ≤ 2*b then 0 else if 12*b < a then -(-(originalFinalNodes 196608).Hhi/12) else
    -(-(literalQueryNumeratorHi a b*b)/a)

def literalQueryLo160 (a b : ℤ) : ℤ := literalQueryLo112 a b*2^48
def literalQueryHi160 (a b : ℤ) : ℤ := literalQueryHi112 a b*2^48

/-- Exact equivalence of the real-proof numerator rules to the literal
integer divmod/interpolation implementation, including the r=0 branch. -/
theorem original_query_numerators_literal (a b : ℤ) (hb : 0 < b) (ha : 0 ≤ a) :
    originalQueryNumeratorLo ((a : ℚ)/(b : ℚ)) = literalQueryNumeratorLo a b ∧
      originalQueryNumeratorHi ((a : ℚ)/(b : ℚ)) = literalQueryNumeratorHi a b := by
  have hi : originalQueryIndex ((a : ℚ)/(b : ℚ)) = literalQueryIndex a b := by
    have h := congrArg Int.toNat (original_query_index_literal_divmod a b hb ha)
    simpa [literalQueryIndex] using h
  have hg : queryCellWeight (literalQueryIndex a b) ((a : ℚ)/(b : ℚ))=0 ↔
      a*16384%b=0 := by
    simpa only [hi] using original_query_exact_grid_iff_literal a b hb ha
  by_cases hr : a*16384%b=0
  · have hw := hg.mpr hr
    constructor <;> simp only [originalQueryNumeratorLo, originalQueryNumeratorHi,
      literalQueryNumeratorLo, literalQueryNumeratorHi, hi, if_pos hw, if_pos hr]
  · have hw : ¬ queryCellWeight (literalQueryIndex a b) ((a : ℚ)/(b : ℚ))=0 := by
      intro h
      exact hr (hg.mp h)
    simp only [originalQueryNumeratorLo, originalQueryNumeratorHi,
      literalQueryNumeratorLo, literalQueryNumeratorHi, hi, if_neg hw, if_neg hr]
    have hl := (original_query_interpolation_literal a b
      (originalFinalNodes (literalQueryIndex a b)).Llo
      (originalFinalNodes (literalQueryIndex a b+1)).Llo hb ha).1
    have hh := (original_query_interpolation_literal a b
      (originalFinalNodes (literalQueryIndex a b)).Lhi
      (originalFinalNodes (literalQueryIndex a b+1)).Lhi hb ha).2
    constructor
    · simpa only [hi, queryInterpolationLo] using hl
    · have hh' : queryInterpolationHi (literalQueryIndex a b) ((a : ℚ)/(b : ℚ)) =
          -(-((originalFinalNodes (literalQueryIndex a b)).Lhi*(b-a*16384%b)+
            (originalFinalNodes (literalQueryIndex a b+1)).Lhi*(a*16384%b))/b) := by
        simpa only [hi, queryInterpolationHi] using hh
      rw [hh']

/-- The full clamp/fallback/division rule is literally the original integer
program; no semantic query enclosure is assumed in this algebraic identity. -/
theorem original_query_112bit_literal (a b : ℤ) (hb : 0 < b) (ha : 0 ≤ a) :
    originalQueryLo112 ((a : ℚ)/(b : ℚ)) = literalQueryLo112 a b ∧
      originalQueryHi112 ((a : ℚ)/(b : ℚ)) = literalQueryHi112 a b := by
  have hc := original_query_clamps_literal a b hb
  by_cases hz : a ≤ 2*b
  · have hq := hc.1.mpr hz
    constructor <;> simp only [originalQueryLo112, originalQueryHi112, literalQueryLo112,
      literalQueryHi112, if_pos hq, if_pos hz]
  · have hq : ¬ (a : ℚ)/(b : ℚ) ≤ 2 := fun h => hz (hc.1.mp h)
    by_cases hf : 12*b < a
    · have hfar := hc.2.mpr hf
      constructor <;> simp only [originalQueryLo112, originalQueryHi112, literalQueryLo112,
        literalQueryHi112, if_neg hq, if_neg hz, if_pos hfar, if_pos hf]
    · have hfar : ¬ 12 < (a : ℚ)/(b : ℚ) := fun h => hf (hc.2.mp h)
      have ha0 : 0 < a := by omega
      have hn := original_query_numerators_literal a b hb ha
      simp only [originalQueryLo112, originalQueryHi112, literalQueryLo112,
        literalQueryHi112, if_neg hq, if_neg hz, if_neg hfar, if_neg hf, hn.1, hn.2]
      exact ⟨(original_query_final_division_literal a b (literalQueryNumeratorLo a b) ha0).1,
        (original_query_final_division_literal a b (literalQueryNumeratorHi a b) ha0).2⟩

/-- ENTIRE original compact160-bit integer query interface. Inputs are the
original integersa,b,b>0 with2*b<=a<=12*b. All arrays,divmod,floor/ceiling,
local allowance and2^48 rescaling are literal; the only semantic dependency
is the proved actual all-node theorem,not a desired query-bound hypothesis. -/
theorem literal_compact_query_160bit_encloses
    (a b : ℤ) (hb : 0 < b) (ha2 : 2*b ≤ a) (ha12 : a ≤ 12*b) :
    (literalQueryLo160 a b : ℝ)/2^160 ≤
        actualExtendedThirdLowerFactor ((a : ℝ)/(b : ℝ)) ∧
      actualExtendedThirdLowerFactor ((a : ℝ)/(b : ℝ)) ≤
        (literalQueryHi160 a b : ℝ)/2^160 := by
  have hbQ : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have hq2 : (2 : ℚ) ≤ (a : ℚ)/(b : ℚ) :=
    (le_div_iff₀ hbQ).2 (by exact_mod_cast ha2)
  have hq12 : (a : ℚ)/(b : ℚ) ≤ 12 :=
    (div_le_iff₀ hbQ).2 (by exact_mod_cast ha12)
  have ha : 0 ≤ a := by omega
  have h := original_compact_query_160bit_encloses hq2 hq12
  have he := original_query_112bit_literal a b hb ha
  simpa only [originalQueryLo160, originalQueryHi160, he.1, he.2,
    literalQueryLo160, literalQueryHi160, Rat.cast_div, Rat.cast_intCast] using h

end
end ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly
