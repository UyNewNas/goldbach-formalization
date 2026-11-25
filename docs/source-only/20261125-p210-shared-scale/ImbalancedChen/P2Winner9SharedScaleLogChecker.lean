import ImbalancedChen.P2Winner9SelectedArchiveChecker

/-!
SOURCE-ONLY PERFORMANCE CANDIDATE / NO COMPILATION OR REPLAY CREDIT.

Materialize the same rational and integer log inputs as the accepted
materialized checker, with each common denominator evaluated before its
coordinate formulas. The source normalization, integer cross-product,
BasicChecks, final price comparison, branch selection, and Q6 branch remain
unchanged. The generic equalities below express this exact boundary; any
performance benefit still requires normal compilation and independent replay.
-/

namespace ImbalancedChen.P2Winner9SharedScaleLogChecker

open P2Winner9CompleteSeedTypes (RawRow)
open P2Winner9Row22Arithmetic (RationalVertices rawGap rawFactor)
open P2Winner9CurvatureFullExactAssembly (SimplexData)
open P2Winner9RationalSimplexData (Input toSimplexData gapDen scale)
open P2Winner9GenericLogBranch
  (Geometry factorTop factorTop_pos rawFactor_le_top logPriceQ)
open P2Winner9FastLogCertificates (logFloorCheck logFloorCheckData)
open P2Winner9RowArithmeticChecker
  (BasicChecks basicDecidable withRowNumerics withRowNumerics_eq archiveVertices checkQ6)
open P2Winner9SelectedArchiveChecker (logGeometry logFloors checkLog checkSelected)
open P2Winner9CurvatureExactMomentFloor (q96)

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

/-- Only these rational fields are used to normalize an original log factor. -/
private def forceLogInput {α : Type} (a : Input) (k : Input → α) : α :=
  forceFn forceRat a.gaps fun gaps hg =>
    forceFn forceRat a.p fun p hp =>
      forceRat a.upper fun upper hu =>
        k { gaps := gaps, p := p, deviations := a.deviations, upper := upper,
            maxima := a.maxima, jensen := a.jensen,
            gaps_nonneg := hg.symm ▸ a.gaps_nonneg,
            gaps_pos := hg.symm ▸ a.gaps_pos,
            upper_pos := hu.symm ▸ a.upper_pos,
            p_le_upper := by simpa only [hp, hu] using a.p_le_upper,
            maxima_pos := a.maxima_pos,
            jensen_nonneg := a.jensen_nonneg }

private theorem forceLogInput_eq {α : Type} (a : Input) (k : Input → α) :
    forceLogInput a k = k a := by
  unfold forceLogInput
  rw [forceFn_eq _ forceRat_eq, forceFn_eq _ forceRat_eq, forceRat_eq]

/-- Evaluate the two original common denominators before the nine coordinate
formulas. Each displayed integer expression unfolds the corresponding field
of `toSimplexData`; the remaining fields are retained from that same value. -/
private def withSharedLogData {α : Type} (a : Input) (k : SimplexData → α) : α :=
  forceNat (gapDen a) fun g hg =>
    forceNat (scale a) fun s hs =>
      let d := toSimplexData a
      k { gaps := fun i => ((a.gaps i).num * (g / (a.gaps i).den : ℕ)).toNat,
          y := fun i => (a.upper.num * (s / a.upper.den : ℕ) -
            (a.p i).num * (s / (a.p i).den : ℕ)).toNat,
          L := d.L,
          U := (a.upper.num * (s / a.upper.den : ℕ)).toNat,
          deviations := d.deviations, maxima := d.maxima,
          jensenNum := d.jensenNum, jensenDen := d.jensenDen,
          gapsPos := by subst g; exact d.gapsPos,
          LPos := d.LPos,
          UPos := by subst s; exact d.UPos,
          maximaPos := d.maximaPos,
          jensenDenPos := d.jensenDenPos }

private theorem withSharedLogData_eq {α : Type} (a : Input) (k : SimplexData → α) :
    withSharedLogData a k = k (toSimplexData a) := by
  unfold withSharedLogData
  rw [forceNat_eq, forceNat_eq] <;> rfl

/-- The log cross-product uses only the normalized gaps, y, and U. -/
private def forceLogData {α : Type} (d : SimplexData) (k : SimplexData → α) : α :=
  forceNat d.U fun U hU =>
    forceFn forceNat d.gaps fun gaps hg =>
      forceFn forceNat d.y fun y _ =>
        k { gaps := gaps, y := y, L := d.L, U := U, deviations := d.deviations,
            maxima := d.maxima, jensenNum := d.jensenNum, jensenDen := d.jensenDen,
            gapsPos := hg.symm ▸ d.gapsPos, LPos := d.LPos,
            UPos := hU.symm ▸ d.UPos, maximaPos := d.maximaPos,
            jensenDenPos := d.jensenDenPos }

private theorem forceLogData_eq {α : Type} (d : SimplexData) (k : SimplexData → α) :
    forceLogData d k = k d := by
  unfold forceLogData
  rw [forceNat_eq, forceFn_eq _ forceNat_eq, forceFn_eq _ forceNat_eq]

/-- This is definitionally the source log factor's rational Input. -/
private def factorInput (r : Geometry) (j : Fin 10) : Input where
  gaps := rawGap r.vertices
  p i := rawFactor r.vertices i j
  deviations _ _ := 0
  upper := factorTop r j
  maxima _ := 1
  jensen := 0
  gaps_nonneg := r.gap_nonneg
  gaps_pos := r.gap_sum_pos
  upper_pos := factorTop_pos r j
  p_le_upper i := rawFactor_le_top r i j
  maxima_pos _ := by norm_num
  jensen_nonneg := by norm_num

/-- Evaluate the original log cross-product with shared normalization scales. -/
def checkFactor (r : Geometry) (j : Fin 10) (floor : ℕ) : Bool :=
  forceLogInput (factorInput r j) fun a =>
    withSharedLogData a fun d =>
      forceLogData d fun d' => decide (logFloorCheckData d' floor)

theorem checkFactor_eq_decide (r : Geometry) (j : Fin 10) (floor : ℕ) :
    checkFactor r j floor = decide (logFloorCheck r j floor) := by
  rw [checkFactor, forceLogInput_eq, withSharedLogData_eq, forceLogData_eq]
  rfl

/-- Retain every original log-branch premise and its final Q96 comparison. -/
def checkLogSharedScale (v : RationalVertices) (r : RawRow) : Bool :=
  withRowNumerics v r fun v' r' =>
    letI : Decidable (BasicChecks v' r') := basicDecidable v' r'
    if h : BasicChecks v' r' then
      decide ((∀ j, checkFactor (logGeometry v' r' h) j (logFloors r' j) = true) ∧
        (r'.logSelected : ℚ) / q96 ≤ logPriceQ r'.jensen (logFloors r'))
    else false

theorem checkLogSharedScale_eq (v : RationalVertices) (r : RawRow) :
    checkLogSharedScale v r = checkLog v r := by
  unfold checkLogSharedScale checkLog
  rw [withRowNumerics_eq, withRowNumerics_eq]
  split_ifs <;> simp only [checkFactor_eq_decide, decide_eq_true_eq]

/-- The stored selection comparison and the complete Q6 branch are unchanged. -/
def checkSelectedSharedScale (r : RawRow) : Bool :=
  if r.logSelected ≤ r.mixedRaw then checkQ6 (archiveVertices r) r
  else checkLogSharedScale (archiveVertices r) r

/-- The additive evaluator computes the original selected predicate. -/
theorem checkSelectedSharedScale_eq (r : RawRow) :
    checkSelectedSharedScale r = checkSelected r := by
  simp only [checkSelectedSharedScale, checkSelected, checkLogSharedScale_eq]

theorem checkSelectedSharedScale_sound {r : RawRow}
    (h : checkSelectedSharedScale r = true) : checkSelected r = true :=
  (checkSelectedSharedScale_eq r).symm.trans h

end ImbalancedChen.P2Winner9SharedScaleLogChecker
