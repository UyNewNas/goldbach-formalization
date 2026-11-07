import ImbalancedChen.P5ZU1011OriginalSixteenKnotPayment

/-!
Actual snapped H248 profile for the original sixteen policies. Outside
the paid31-branch/151-knot strip, nearby positive coordinate snapping
preserves the exact serialized scalar atom, hence the literal H248 value.
This includes the whole clamp below two, which is never erased.

A safe snap uses the original lookup when positivity or the distance test
fails. Its range and off-strip agreement are proved for EVERY snap map,
so the arithmetic reserve threshold precedes all moving snap maps and all
moving tuple keep masks. Fine original-cube meshes pass the tests and
therefore use the literal lower-corner lookup throughout each cell.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenSnappedTable

open Set
open Classical
open U11Integral U11H248 U1011OriginalSixteenPolicyBank U1011OriginalSixteenOscillation
open U1011H248Partition U1011OriginalSixteenKnotPayment
open U1011AdaptivePrimeError
open Part5UpperTables Part5OriginalUpsilon5CausalDictionary
open scoped BigOperators

noncomputable section

def gap (p : Policy) (j : Fin 201) (v : LogFour) : ℝ :=
  typedResidual p v-floorGrid j.val*v 3

private theorem tableKnot_surjective (j : Fin 201) (hj : 50≤j.val) :
    ∃ i : Fin 151,tableKnot i=j := by
  let i : Fin 151 := ⟨j.val-50,by have hmax:=j.isLt; omega⟩
  refine ⟨i,?_⟩
  apply Fin.ext
  dsimp [tableKnot,i]
  omega

private theorem same_strict_signs (x y : ℝ) (h : |x-y|<|x|) :
    (x<0 ↔ y<0) ∧ (0<x ↔ 0<y) := by
  have hx0 : x≠0 := by
    intro hx
    rw [hx,abs_zero] at h
    exact (not_lt_of_ge (abs_nonneg _)) h
  rcases lt_or_gt_of_ne hx0 with hx | hx
  · have hy : y<0 := by
      rw [abs_of_neg hx] at h
      have hh := (abs_lt.mp h).1
      linarith
    exact ⟨⟨fun _=>hy,fun _=>hx⟩,⟨by intro h;linarith,by intro h;linarith⟩⟩
  · have hy : 0<y := by
      rw [abs_of_pos hx] at h
      have hh := (abs_lt.mp h).2
      linarith
    exact ⟨⟨by intro h;linarith,by intro h;linarith⟩,⟨fun _=>hy,fun _=>hx⟩⟩

/-- Actual cap/residual oscillation supplies the sign stability; the
hypothesis is coordinate proximity, not a target H-table approximation. -/
theorem gap_signs_stable (p : Policy) (j : Fin 201) (hj : 50≤j.val)
    (v w : LogFour) (delta : ℝ) (hd : 0<delta) (hoff : v∉knotStrip delta)
    (hclose : l1Delta v w≤delta/8) :
    (gap p j v<0 ↔ gap p j w<0) ∧ (0<gap p j v ↔ 0<gap p j w) := by
  obtain ⟨i,hi⟩ := tableKnot_surjective j hj
  have hsep := actual_gap_separated_of_not_strip p v i delta hoff
  have hosc := policyGap_abs_sub_le p i v w
  have hdiff : |policyGap p i v-policyGap p i w|<delta := by nlinarith
  have hsign := same_strict_signs _ _ (hdiff.trans hsep)
  simpa only [policyGap,gap,hi] using hsign

theorem gap_ne_zero_of_not_strip (p : Policy) (j : Fin 201) (hj : 50≤j.val)
    (v : LogFour) (delta : ℝ) (hd : 0≤delta) (hoff : v∉knotStrip delta) :
    gap p j v≠0 := by
  obtain ⟨i,hi⟩ := tableKnot_surjective j hj
  have hsep := actual_gap_separated_of_not_strip p v i delta hoff
  intro hz
  have heq : policyGap p i v=0 := by simpa only [policyGap,gap,hi] using hz
  rw [heq,abs_zero] at hsep
  linarith

/-- The actual table value is unchanged off the paid strip. Open atoms,
clamp atom50, high marked knots and exterior are handled separately. -/
theorem H248_lookup_stable (p : Policy) (v w : LogFour) (delta : ℝ)
    (hd : 0<delta) (hv : 0<v 3) (hw : 0<w 3) (hoff : v∉knotStrip delta)
    (hclose : l1Delta v w≤delta/8) :
    H248 (max 2 (typedResidual p v/v 3))=
      H248 (max 2 (typedResidual p w/w 3)) := by
  obtain ⟨a,ha⟩ := exists_scalarCell (typedResidual p v/v 3)
  have hwa : typedResidual p w/w 3∈scalarCell a := by
    cases a with
    | none =>
      have hquery : 5<typedResidual p v/v 3 := (mem_scalarCell_none_iff _).mp ha
      have hgap : 0<gap p (200 : Fin 201) v := by
        have hmul := (lt_div_iff₀ hv).1 hquery
        norm_num [gap,floorGrid] at *
        linarith
      have hgw := (gap_signs_stable p 200 (by norm_num) v w delta hd hoff hclose).2.mp hgap
      apply (mem_scalarCell_none_iff _).mpr
      apply (lt_div_iff₀ hw).2
      norm_num [gap,floorGrid] at hgw
      linarith
    | some a =>
      cases a with
      | inl i =>
        have hi : 50≤i.val := by
          by_contra hn
          have hindex : i.val+1≤50 := by omega
          have hindexR : (i.val:ℝ)+1≤50 := by exact_mod_cast hindex
          have hg : floorGrid (i.val+1)≤2 := by
            simp only [floorGrid,Nat.cast_add,Nat.cast_one]
            linarith
          have hupper : max 2 (typedResidual p v/v 3)<floorGrid (i.val+1) := ha.2.2
          exact (not_lt_of_ge (hg.trans (le_max_left (2:ℝ) _))) hupper
        obtain ⟨hlo,hhi⟩ := (mem_scalarCell_open_iff i hi _ _ hv).mp ha
        let jl : Fin 201 := ⟨i.val,by omega⟩
        let ju : Fin 201 := ⟨i.val+1,by omega⟩
        have hgl : 0<gap p jl v := by dsimp [gap,jl]; linarith
        have hgu : gap p ju v<0 := by dsimp [gap,ju]; linarith
        have hglw := (gap_signs_stable p jl (by dsimp [jl];omega) v w delta hd hoff hclose).2.mp hgl
        have hguw := (gap_signs_stable p ju (by dsimp [ju];omega) v w delta hd hoff hclose).1.mp hgu
        apply (mem_scalarCell_open_iff i hi _ _ hw).mpr
        dsimp [gap,jl,ju] at hglw hguw
        exact ⟨by linarith,by linarith⟩
      | inr j =>
        by_cases hj : j.val<50
        · have hjR : (j.val:ℝ)<50 := by exact_mod_cast hj
          have hgrid : floorGrid j.val<2 := by dsimp [floorGrid];linarith
          have heq : max 2 (typedResidual p v/v 3)=floorGrid j.val := ha.2
          linarith [le_max_left (2:ℝ) (typedResidual p v/v 3)]
        · by_cases heq : j.val=50
          · have hj50 : j=U1011H248Clamp.clampKnot := Fin.ext heq
            subst j
            have hmul := (mem_scalarCell_clamp_iff _ _ hv).mp ha
            have hgle : gap p U1011H248Clamp.clampKnot v≤0 := by
              norm_num [gap,U1011H248Clamp.clampKnot,floorGrid] at *
              linarith
            have hgn := gap_ne_zero_of_not_strip p U1011H248Clamp.clampKnot
              (by norm_num [U1011H248Clamp.clampKnot]) v delta hd.le hoff
            have hgl : gap p U1011H248Clamp.clampKnot v<0 := lt_of_le_of_ne hgle hgn
            have hgw := (gap_signs_stable p U1011H248Clamp.clampKnot
              (by norm_num [U1011H248Clamp.clampKnot]) v w delta hd hoff hclose).1.mp hgl
            apply (mem_scalarCell_clamp_iff _ _ hw).mpr
            norm_num [gap,U1011H248Clamp.clampKnot,floorGrid] at hgw
            linarith
          · have hjhigh : 50<j.val := by omega
            have hmul := (mem_scalarCell_knot_iff j hjhigh _ _ hv).mp ha
            have hgn := gap_ne_zero_of_not_strip p j hjhigh.le v delta hd.le hoff
            exact (hgn (by dsimp [gap];linarith)).elim
  rw [H248_eq_stateValue ha,H248_eq_stateValue hwa]

/-- A concrete actual lookup profile, with original lookup fallback when
an arbitrary snap map fails positivity or the quantitative distance test. -/
def snappedProfile (delta : ℝ) (snap : LogFour→LogFour) (p : Policy) (v : LogFour) : ℝ :=
  if 0<v 3 ∧ 0<(snap v) 3 ∧ l1Delta v (snap v)≤delta/8 then
    H248 (max 2 (typedResidual p (snap v)/(snap v) 3))
  else H248 (max 2 (typedResidual p v/v 3))

theorem snappedProfile_bounds (delta : ℝ) (snap : LogFour→LogFour) (p : Policy) (v : LogFour) :
    0≤snappedProfile delta snap p v ∧ snappedProfile delta snap p v≤1 := by
  unfold snappedProfile
  split_ifs <;> exact H248_bounds _

theorem snappedProfile_eq_of_not_strip (delta : ℝ) (hd : 0<delta)
    (snap : LogFour→LogFour) (p : Policy) (v : LogFour) (hoff : v∉knotStrip delta) :
    snappedProfile delta snap p v=H248 (max 2 (typedResidual p v/v 3)) := by
  unfold snappedProfile
  split_ifs with h
  · exact (H248_lookup_stable p v (snap v) delta hd h.1 h.2.1 hoff h.2.2).symm
  · rfl

/-- A total actual half-open mesh snap, with exact Ico cell ownership. -/
def meshSnap (lo hi : ℝ) (m : ℕ) (v : LogFour) : LogFour :=
  if hv : v∈logPrimeBox (fun _ : Fin 4=>lo) (fun _=>hi) then
    logPrimeMeshLo lo hi m (Classical.choose (exists_logPrimeMeshCell lo hi m hv))
  else v

theorem meshSnap_eq_of_mem (lo hi : ℝ) (hab : lo<hi) (m : ℕ)
    (j : Fin 4→Fin (m+1)) (v : LogFour) (hv : v∈logPrimeMeshCell lo hi m j) :
    meshSnap lo hi m v=logPrimeMeshLo lo hi m j := by
  have hbox := logPrimeMeshCell_subset_box hab m j hv
  have hsel := Classical.choose_spec (exists_logPrimeMeshCell lo hi m hbox)
  have hsame := logPrimeMeshCell_unique hab.le hsel hv
  simp only [meshSnap,dif_pos hbox,hsame]

/-- Fine original-cube meshes use the literal lower-corner table lookup;
the safe fallback disappears on every real mesh cell, for all16 policies. -/
theorem snappedProfile_original_mesh (delta : ℝ) (m : ℕ)
    (hstep : logPrimeMeshStep (417/5000:ℝ) (59/250:ℝ) m≤delta/32)
    (p : Policy) (j : Fin 4→Fin (m+1)) (v : LogFour)
    (hv : v∈logPrimeMeshCell (417/5000:ℝ) (59/250:ℝ) m j) :
    snappedProfile delta (meshSnap (417/5000:ℝ) (59/250:ℝ) m) p v=
      H248 (max 2 (typedResidual p (logPrimeMeshLo (417/5000:ℝ) (59/250:ℝ) m j)/
        logPrimeMeshLo (417/5000:ℝ) (59/250:ℝ) m j 3)) := by
  have hab : (417/5000:ℝ)<59/250 := by norm_num
  have hlo : 0<logPrimeMeshLo (417/5000:ℝ) (59/250:ℝ) m j 3 :=
    (show (0:ℝ)<417/5000 by norm_num).trans_le (logPrimeMeshLoHi_bounds hab m j 3).1
  have hv3 : 0<v 3 := hlo.trans_le (mem_logPrimeMeshCell.mp hv 3).1
  have hclose : l1Delta v (logPrimeMeshLo (417/5000:ℝ) (59/250:ℝ) m j)≤delta/8 := by
    have h := l1Delta_meshLo_le j hv
    linarith
  unfold snappedProfile
  rw [meshSnap_eq_of_mem _ _ hab m j v hv]
  rw [if_pos ⟨hv3,hlo,hclose⟩]

/-- Concrete snapped-profile jump payment. The scalar agreement premise
from the preceding general reserve is discharged internally. One width
and target threshold precede every moving snap map and moving keep mask. -/
theorem exists_uniform_snapped_profile_reserve (epsilon : ℝ) (he : 0<epsilon) :
    ∃ delta : ℝ,0<delta ∧ ∃ N0 : ℕ,2≤N0 ∧ ∀ N : ℕ,N0≤N →
      ∀ (d : ℝ),0<d → d≤delta → ∀ (snap : LogFour→LogFour)
        (switched : LogFour→ℝ) (mask : Set (ℝ×ℝ)) (keep : (Fin 4→ℕ)→Prop),
        (∀ p∈actualPrimeBoxTuples N (fun _ : Fin 4 => (417/5000:ℝ))
          (fun _ => (59/250:ℝ)),keep p → actualPrimeTupleLog N p∈originalDomain mask) →
        |maskedTestSum N (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ)) keep
            (originalEnvelope switched)-
          maskedTestSum N (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ)) keep
            (replacementEnvelope (snappedProfile d snap) switched)|<epsilon := by
  obtain ⟨delta,hd,N0,hN0,hpay⟩ := exists_uniform_masked_replacement_reserve epsilon he
  refine ⟨delta,hd,N0,hN0,?_⟩
  intro N hN d hdpos hsmall snap switched mask keep hkeep
  exact hpay N hN d hdpos.le hsmall (snappedProfile d snap) switched mask keep
    (snappedProfile_bounds d snap)
    (fun p v hoff=>snappedProfile_eq_of_not_strip d hdpos snap p v hoff) hkeep

end

end ImbalancedChen.P5Z.U1011OriginalSixteenSnappedTable
