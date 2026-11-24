import ImbalancedChen.P2Winner9CompleteSeedTypes
import ImbalancedChen.P2Winner9CompleteSeedVertices
import ImbalancedChen.P2Winner9DyadicQ6
import ImbalancedChen.P2Winner9RationalSimplexCaps
import ImbalancedChen.P2Winner9RawFirstMomentDecoder
import ImbalancedChen.P2Winner9ReducedExactAssembly

/-! Executable exact arithmetic checks for the original Winner9 rows. -/

namespace ImbalancedChen.P2Winner9RowArithmeticChecker

open P2Winner9CompleteSeedTypes (RawRow)
open P2Winner9CompleteSeedVertices (coordinates)
open P2Winner9Row22Arithmetic (RationalVertices rawFactor rawGap rawP)
open P2Winner9SelectedRowEdgeGeometry (edgeMatrix)
open P2Winner9RawFirstMomentDecoder (affineMeanQ gapMomentQ)
open P2Winner9RationalSimplexData (Input toSimplexData gapDen)
open P2Winner9CurvatureFullExactAssembly (SimplexData ExactFraction value)
open P2Winner9CurvatureExactMomentFloor
open P2Winner9DyadicQ6 (Q80Check)
open P2Winner9FastExactAssembly (t10Fast t10_eq)
open P2Winner9MixedDegreeSixExactAssembly (total)
open P2Winner9ReducedExactAssembly (totalValueReduced totalValueReduced_eq Q80_of_value)

private def forceNat {α : Type} (n : Nat) (k : (x : Nat) → x = n → α) : α :=
  match n with
  | 0 => k 0 rfl
  | m + 1 => k (m + 1) rfl

private theorem forceNat_eq {α : Type} (n : Nat) (k : (x : Nat) → x = n → α) :
    forceNat n k = k n rfl := by cases n <;> rfl

private def forceInt {α : Type} (n : Int) (k : (x : Int) → x = n → α) : α :=
  match n with
  | .ofNat m => forceNat m fun x h => k (.ofNat x) (congrArg Int.ofNat h)
  | .negSucc m => forceNat m fun x h => k (.negSucc x) (congrArg Int.negSucc h)

private theorem forceInt_eq {α : Type} (n : Int) (k : (x : Int) → x = n → α) :
    forceInt n k = k n rfl := by cases n <;> simp only [forceInt, forceNat_eq]

private def forceFn {α β : Type} (force : (x : β) → ((y : β) → y = x → α) → α)
    {n : Nat} : (f : Fin n → β) → ((g : Fin n → β) → g = f → α) → α :=
  Nat.rec (motive := fun m => (f : Fin m → β) → ((g : Fin m → β) → g = f → α) → α)
    (fun _ k => k Fin.elim0 (funext fun i => i.elim0))
    (fun _ recurse f k => force (f 0) fun x hx =>
      recurse (fun i => f i.succ) fun t ht =>
        k (Fin.cons x t) (by rw [hx, ht]; exact Fin.cons_self_tail f)) n

private theorem forceFn_eq {α β : Type} (force : (x : β) → ((y : β) → y = x → α) → α)
    (hs : ∀ x k, force x k = k x rfl) {n : Nat} (f : Fin n → β)
    (k : (g : Fin n → β) → g = f → α) : forceFn force f k = k f rfl := by
  induction n with
  | zero =>
    have hf : f = Fin.elim0 := funext fun i => i.elim0
    subst f
    rfl
  | succ n ih =>
    change (force (f 0) fun x hx =>
      forceFn force (fun i : Fin n => f i.succ) fun t ht =>
        k (Fin.cons x t) (by rw [hx, ht]; exact Fin.cons_self_tail f)) = k f rfl
    rw [hs, ih]
    generalize_proofs h
    congr 1

private def forceRat {α : Type} (q : ℚ) (k : (x : ℚ) → x = q → α) : α :=
  forceInt q.num fun a ha => forceNat q.den fun b hb =>
    k ⟨a, b, hb.symm ▸ q.den_nz, by rw [ha, hb]; exact q.reduced⟩ (Rat.ext ha hb)

private theorem forceRat_eq {α : Type} (q : ℚ) (k : (x : ℚ) → x = q → α) :
    forceRat q k = k q rfl := by
  simp only [forceRat, forceInt_eq, forceNat_eq]

private def forceRaw {α : Type} (r : RawRow) (k : RawRow → α) : α :=
  forceFn forceRat r.means fun means _ =>
    forceRat r.physicalVolume fun volume _ =>
      forceRat r.meanGap fun meanGap _ =>
        forceRat r.jensen fun jensen _ =>
          k {r with means := means, physicalVolume := volume, meanGap := meanGap, jensen := jensen}

private theorem forceRaw_eq {α : Type} (r : RawRow) (k : RawRow → α) :
    forceRaw r k = k r := by
  simp only [forceRaw, forceFn_eq _ forceRat_eq, forceRat_eq]

/-- Reduce archived rationals before the branch evaluates repeated arithmetic. -/
def withRowNumerics {α : Type} (v : RationalVertices) (r : RawRow)
    (k : RationalVertices → RawRow → α) : α :=
  forceFn (fun row u => forceFn forceRat row u) v (fun v' _ => forceRaw r (k v'))

theorem withRowNumerics_eq {α : Type} (v : RationalVertices) (r : RawRow)
    (k : RationalVertices → RawRow → α) : withRowNumerics v r k = k v r := by
  simp only [withRowNumerics, forceFn_eq _ (fun t u => forceFn_eq _ forceRat_eq t u), forceRaw_eq]

/-- The complement remaining after eliminating the first column. -/
private def pivotMinor {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    Matrix (Fin n) (Fin n) ℚ := fun i j =>
  A i.succ j.succ - A i.succ 0 / A 0 0 * A 0 j.succ

private theorem pivotMinor_det {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hp : A 0 0 ≠ 0) : A.det = A 0 0 * (pivotMinor A).det := by
  let c : Fin (n + 1) → ℚ := fun i => if i = 0 then 0 else -(A i 0 / A 0 0)
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := fun i j => A i j + c i * A 0 j
  have hdet : E.det = A.det := Matrix.det_eq_of_forall_row_eq_smul_add_const c 0
    (by simp [c]) (fun _ _ => rfl)
  have hz (i : Fin (n + 1)) (hi : i ≠ 0) : E i 0 = 0 := by
    simp [E, c, hi, div_mul_cancel₀ (A i 0) hp]
  have h00 : E 0 0 = A 0 0 := by simp [E, c]
  have hminor : E.submatrix (0 : Fin (n + 1)).succAbove Fin.succ = pivotMinor A := by
    ext i j
    change E ((0 : Fin (n + 1)).succAbove i) j.succ = pivotMinor A i j
    rw [Fin.succAbove_zero]
    simp [E, c, pivotMinor, sub_eq_add_neg]
  rw [← hdet, Matrix.det_succ_column_zero, Finset.sum_eq_single 0, h00, hminor]
  · simp
  · intro i _ hi
    simp [hz i hi]
  · simp

private def swapPivot {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (p : Fin (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  A.submatrix (Equiv.swap 0 p) id

private theorem swapPivot_det {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (p : Fin (n + 1)) : (swapPivot A p).det = (if p = 0 then 1 else -1) * A.det := by
  unfold swapPivot
  by_cases hp : p = 0
  · subst p
    simp
  · rw [Matrix.det_permute, Equiv.Perm.sign_swap (Ne.symm hp), if_neg hp]
    norm_num

/-- Exact Gaussian determinant over ℚ with first-column pivoting. -/
private def fastDetCore {n : ℕ} : Matrix (Fin n) (Fin n) ℚ → ℚ :=
  Nat.rec (motive := fun m => Matrix (Fin m) (Fin m) ℚ → ℚ) (fun _ => 1)
    (fun m recurse A =>
      match (List.finRange (m + 1)).find? (fun i => A i 0 != 0) with
      | none => 0
      | some p =>
          let B := swapPivot A p
          (if p = 0 then 1 else -1) * B 0 0 * recurse (pivotMinor B)) n

private theorem fastDetCore_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : fastDetCore A = A.det := by
  induction n with
  | zero => simp [fastDetCore]
  | succ n ih =>
      change (match (List.finRange (n + 1)).find? (fun i => A i 0 != 0) with
        | none => 0
        | some p =>
          let B := swapPivot A p
          (if p = 0 then 1 else -1) * B 0 0 * fastDetCore (pivotMinor B)) = A.det
      split <;> rename_i h
      · rw [Matrix.det_succ_column_zero]
        symm
        apply Finset.sum_eq_zero
        intro i _
        have hi := List.find?_eq_none.mp h i (List.mem_finRange i)
        have hz : A i 0 = 0 := by simpa using hi
        simp [hz]
      · rename_i p
        have hp : A p 0 ≠ 0 := by simpa using List.find?_some h
        have h00 : swapPivot A p 0 0 = A p 0 := by simp [swapPivot]
        change (if p = 0 then 1 else -1) * swapPivot A p 0 0 *
          fastDetCore (pivotMinor (swapPivot A p)) = A.det
        rw [ih, mul_assoc, ← pivotMinor_det _ (h00 ▸ hp), swapPivot_det]
        split_ifs <;> ring

/-- Materialize the exact rational entries once before Gaussian reduction. -/
def fastDet {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : ℚ :=
  forceFn (fun row k => forceFn forceRat row k) (fun i j => A i j) (fun B _ => fastDetCore B)

theorem fastDet_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : fastDet A = A.det := by
  unfold fastDet
  rw [forceFn_eq _ (fun r k => forceFn_eq _ forceRat_eq r k)]
  exact fastDetCore_eq A

/-- Ordered vertices selected by the row's original vertex IDs. -/
def archiveVertices (r : RawRow) : RationalVertices :=
  fun i => coordinates[r.vertexIds i]!

/-- The rational identities and guards required for the physical row. -/
abbrev BasicChecks (v : RationalVertices) (r : RawRow) : Prop :=
  0 < r.physicalVolume ∧
    |fastDet (edgeMatrix v)| = ((8 : ℕ).factorial : ℚ) * r.physicalVolume ∧
    (∀ i, 0 ≤ rawGap v i) ∧ 0 < ∑ i, rawGap v i ∧
    (∀ i j, 0 < rawFactor v i j) ∧ (∀ j, 0 < r.means j) ∧
    gapMomentQ (rawGap v) = r.meanGap / ((8 : ℕ).factorial : ℚ) ∧
    (∀ j, affineMeanQ (rawGap v) (fun i => rawFactor v i j) = r.means j) ∧
    affineMeanQ (rawGap v) (rawP v r.means) = 1 ∧
    r.jensen = 4 * (((8 : ℕ).factorial : ℚ) * r.physicalVolume) *
      gapMomentQ (rawGap v) / ∏ j, r.means j

/-- A successful arithmetic check supplies the exact rational row premises. -/
structure BasicFacts (v : RationalVertices) (r : RawRow) : Prop where
  det_ne : (edgeMatrix v).det ≠ 0
  det_abs : |(edgeMatrix v).det| = ((8 : ℕ).factorial : ℚ) * r.physicalVolume
  gap_nonneg : ∀ i, 0 ≤ rawGap v i
  gap_sum_pos : 0 < ∑ i, rawGap v i
  factor_pos : ∀ i j, 0 < rawFactor v i j
  means_pos : ∀ j, 0 < r.means j
  gap_mean : gapMomentQ (rawGap v) = r.meanGap / ((8 : ℕ).factorial : ℚ)
  factor_mean : ∀ j, affineMeanQ (rawGap v) (fun i => rawFactor v i j) = r.means j
  p_mean : affineMeanQ (rawGap v) (rawP v r.means) = 1
  jensen_eq : r.jensen = 4 * |(edgeMatrix v).det| * gapMomentQ (rawGap v) / ∏ j, r.means j

theorem basic_sound {v : RationalVertices} {r : RawRow} (h : BasicChecks v r) :
    BasicFacts v r := by
  obtain ⟨hvol, hdet, hgap, hG, hfac, hmus, hmg, hmf, hmp, hJ⟩ := h
  rw [fastDet_eq] at hdet
  have hne : (edgeMatrix v).det ≠ 0 := by
    intro he
    rw [he, abs_zero] at hdet
    exact (mul_pos (by norm_num : (0 : ℚ) < ((8 : ℕ).factorial : ℚ)) hvol).ne' hdet.symm
  exact ⟨hne, hdet, hgap, hG, hfac, hmus, hmg, hmf, hmp, hdet ▸ hJ⟩

theorem BasicFacts.p_pos {v : RationalVertices} {r : RawRow} (h : BasicFacts v r) (i : Fin 9) :
    0 < rawP v r.means i := by
  unfold rawP
  exact div_pos (Finset.sum_pos (fun j _ => div_pos (h.factor_pos i j) (h.means_pos j))
    Finset.univ_nonempty) (by norm_num)

theorem BasicFacts.jensen_pos {v : RationalVertices} {r : RawRow} (h : BasicFacts v r) :
    0 < r.jensen := by
  rw [h.jensen_eq]
  exact div_pos (mul_pos (mul_pos (by norm_num) (abs_pos.mpr h.det_ne))
    (P2Winner9RawFirstMomentDecoder.gapMomentQ_pos _ h.gap_sum_pos))
    (Finset.prod_pos fun j _ => h.means_pos j)

/-- Reconstruct the integral scales from a row with checked rational fields. -/
def input (v : RationalVertices) (r : RawRow) (h : BasicChecks v r) : Input :=
  let facts := basic_sound h
  P2Winner9RationalSimplexCaps.ofPhysicalVertices v r.means r.jensen
    facts.gap_nonneg facts.gap_sum_pos (facts.p_pos 0) facts.jensen_pos.le

theorem input_normalization (v : RationalVertices) (r : RawRow) (h : BasicChecks v r) :
    let a := input v r h
    P2Winner9Row22Arithmetic.VertexNormalization v r.means
      (P2Winner9RationalSimplexCaps.upper v r.means) (toSimplexData a) (gapDen a) :=
  P2Winner9RationalSimplexCaps.ofPhysicalVertices_normalization v r.means r.jensen
    (basic_sound h).gap_nonneg (basic_sound h).gap_sum_pos (BasicFacts.p_pos (basic_sound h) 0)
    (BasicFacts.jensen_pos (basic_sound h)).le

theorem input_jensen (v : RationalVertices) (r : RawRow) (h : BasicChecks v r) :
    let d := toSimplexData (input v r h)
    r.jensen = (d.jensenNum : ℚ) / d.jensenDen :=
  P2Winner9RationalSimplexData.jensen_eq (input v r h)

/-- Materialize repeated integer inputs before evaluating the correction. -/
private def forceData {α : Type} (d : SimplexData) (k : SimplexData → α) : α :=
  forceNat d.L fun L hL =>
    forceNat d.U fun U hU =>
      forceNat d.jensenNum fun jNum _ =>
        forceNat d.jensenDen fun jDen hDen =>
          forceFn forceNat d.gaps fun gaps hg =>
            forceFn forceNat d.y fun y _ =>
              forceFn forceNat d.maxima fun maxima hm =>
                forceFn (fun row tail => forceFn forceInt row tail) d.deviations fun b _ =>
                  k { gaps := gaps, y := y, L := L, U := U, deviations := b, maxima := maxima,
                      jensenNum := jNum, jensenDen := jDen,
                      gapsPos := hg.symm ▸ d.gapsPos, LPos := hL.symm ▸ d.LPos,
                      UPos := hU.symm ▸ d.UPos, maximaPos := hm.symm ▸ d.maximaPos,
                      jensenDenPos := hDen.symm ▸ d.jensenDenPos }

private theorem forceData_eq {α : Type} (d : SimplexData) (k : SimplexData → α) :
    forceData d k = k d := by
  unfold forceData
  simp only [forceNat_eq, forceFn_eq _ forceNat_eq,
    forceFn_eq (fun row tail => forceFn forceInt row tail) (fun r t => forceFn_eq _ forceInt_eq r t)]


private def curvatureTotalFast (d : SimplexData) : ExactFraction :=
  P2Winner9CurvatureFullExactAssembly.add (t10Fast d)
    (P2Winner9CurvatureFullExactAssembly.sumFractions
      (P2Winner9CurvatureFullExactAssembly.transverseTerms d))

private theorem curvatureTotalFast_eq (d : SimplexData) :
    curvatureTotalFast d = P2Winner9CurvatureFullExactAssembly.total d := by
  simp only [curvatureTotalFast, P2Winner9CurvatureFullExactAssembly.total, t10_eq]

/-- Directed rounding for the original Q80 curvature and Q96 product fields. -/
def CurvatureChecks (r : RawRow) (d : SimplexData) : Prop :=
  curvatureFloorQ80 (curvatureTotalFast d).num (curvatureTotalFast d).den r.curvatureTotalQ80 ∧
    jensenProductFloorQ96 d.jensenNum d.jensenDen r.curvatureTotalQ80 r.curvatureRaw

instance (r : RawRow) (d : SimplexData) : Decidable (CurvatureChecks r d) := by
  unfold CurvatureChecks curvatureFloorQ80 jensenProductFloorQ96
  infer_instance

/-- Directed rounding for the original Q80 mixed correction and Q96 product fields. -/
def Q6Checks (r : RawRow) (d : SimplexData) : Prop :=
  ⌊(q80 : ℚ) * totalValueReduced d⌋ = (r.mixedTotalQ80 : ℤ) ∧
    jensenProductFloorQ96 d.jensenNum d.jensenDen r.mixedTotalQ80 r.mixedRaw

private theorem q80_floor_iff_source (d : SimplexData) (n : ℤ) :
    ⌊(q80 : ℚ) * totalValueReduced d⌋ = n ↔
      curvatureFloorQ80 (total d).num (total d).den n := by
  rw [totalValueReduced_eq, Int.floor_eq_iff]
  have hscale : 0 < (q80 : ℚ) := by norm_num [q80]
  constructor
  · rintro ⟨hlo, hhi⟩
    apply Q80_of_value
    · exact (div_le_iff₀ hscale).2 (by simpa only [mul_comm] using hlo)
    · exact (lt_div_iff₀ hscale).2 (by simpa only [Int.cast_add, Int.cast_one, mul_comm] using hhi)
  · intro h
    have hh := curvature_floor_Q80_semantics h
    change (n : ℚ) / q80 ≤ value (total d) ∧
      value (total d) < ((n + 1 : ℤ) : ℚ) / q80 at hh
    constructor
    · simpa only [mul_comm] using (div_le_iff₀ hscale).mp hh.1
    · simpa only [Int.cast_add, Int.cast_one, mul_comm] using (lt_div_iff₀ hscale).mp hh.2

instance (r : RawRow) (d : SimplexData) : Decidable (Q6Checks r d) := by
  have h := (Q80Check.iff_source d r.mixedTotalQ80).trans
    (q80_floor_iff_source d r.mixedTotalQ80).symm
  unfold Q6Checks jensenProductFloorQ96
  exact decidable_of_iff _ (and_congr h Iff.rfl)

theorem curvature_lower {r : RawRow} {d : SimplexData} (h : CurvatureChecks r d) :
    (r.curvatureRaw : ℚ) / q96 ≤ ((d.jensenNum : ℚ) / d.jensenDen) *
      (1 + value (P2Winner9CurvatureFullExactAssembly.total d)) := by
  obtain ⟨h80, h96⟩ := h
  rw [curvatureTotalFast_eq] at h80
  exact P2Winner9CurvatureFullExactAssembly.total_directed_floor_semantics _ _ _ h80 h96

theorem q6_lower {r : RawRow} {d : SimplexData} (h : Q6Checks r d) :
    (r.mixedRaw : ℚ) / q96 ≤ ((d.jensenNum : ℚ) / d.jensenDen) *
      (1 + value (P2Winner9MixedDegreeSixExactAssembly.total d)) := by
  obtain ⟨h80, h96⟩ := h
  exact P2Winner9MixedDegreeSixExactAssembly.mixed_directed_floor_semantics _ _ _
    ((q80_floor_iff_source d r.mixedTotalQ80).mp h80) h96

/-- Check the numerical fields for a row supplied by the Q6 branch. -/
def checkQ6 (v : RationalVertices) (r : RawRow) : Bool :=
  withRowNumerics v r fun v' r' =>
    if h : BasicChecks v' r' then
      forceData (toSimplexData (input v' r' h)) (fun d => decide (Q6Checks r' d))
    else false

theorem checkQ6_sound {v : RationalVertices} {r : RawRow} (h : checkQ6 v r = true) :
    ∃ basic : BasicChecks v r, Q6Checks r (toSimplexData (input v r basic)) := by
  rw [checkQ6, withRowNumerics_eq] at h
  split at h
  · rw [forceData_eq] at h
    exact ⟨‹BasicChecks v r›, of_decide_eq_true h⟩
  · contradiction

theorem q6_lower_normalized {v : RationalVertices} {r : RawRow} (hb : BasicChecks v r)
    (h : Q6Checks r (toSimplexData (input v r hb))) :
    (r.mixedRaw : ℚ) / q96 ≤ r.jensen *
      (1 + value (P2Winner9MixedDegreeSixExactAssembly.total (toSimplexData (input v r hb)))) := by
  rw [input_jensen v r hb]
  exact q6_lower h

/-- The numerical checks keep the two originally recorded directed stages. -/
def check (v : RationalVertices) (r : RawRow) : Bool :=
  withRowNumerics v r fun v' r' =>
    if h : BasicChecks v' r' then
      forceData (toSimplexData (input v' r' h)) (fun d =>
        decide (CurvatureChecks r' d ∧ Q6Checks r' d))
    else false

theorem check_sound {v : RationalVertices} {r : RawRow} (h : check v r = true) :
    ∃ basic : BasicChecks v r,
      CurvatureChecks r (toSimplexData (input v r basic)) ∧
        Q6Checks r (toSimplexData (input v r basic)) := by
  rw [check, withRowNumerics_eq] at h
  split at h
  · rw [forceData_eq] at h
    exact ⟨‹BasicChecks v r›, of_decide_eq_true h⟩
  · contradiction

end ImbalancedChen.P2Winner9RowArithmeticChecker
