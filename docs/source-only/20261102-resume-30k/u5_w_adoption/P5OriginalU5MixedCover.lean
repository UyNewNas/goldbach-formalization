import ImbalancedChen.P5OriginalU5MixedWinner
import ImbalancedChen.ActualSelectedSubproductParameters

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Full L5 mixed-winner source licences, including W/tent ties. The physical
cap is always M-2b with M the proved original maximum. A near-tied W source
is covered by the leading singleton at M-7b/4; a separated W source uses
M-b. Neither cover changes the physical cap or the original winning label.
All selected complements are derived, and both critical upper bounds are
kept at residue exponent 1+3*kappa.

These are original source/parameter and prefix-support licences. Actual
finite endpoint grouping, subsequent adopted rank-four/five history,
same-rho analytic distribution and h248 counts remain separate ports.
-/
namespace ImbalancedChen.P5OriginalU5MixedCover

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P2EnhancedLowerPhysicalNode
open P5OriginalU5MixedWinner

private theorem square_mono {c d T : ℝ} (xs : List ℝ) (hcd : c≤d)
    (hs : SquareGates c T xs) : SquareGates d T xs := by
  induction xs generalizing T with
  | nil => trivial
  | cons x xs ih => exact ⟨hs.1.trans hcd,ih hs.2⟩

def SelectedCover (t u z b kappa M : ℝ) (mask : Finset (Fin 5))
    (theta delta auxiliary : ℝ) : Prop :=
  0<delta ∧ (1/2:ℝ)<theta ∧ theta≤cap ∧
    theta-2*delta=auxiliary ∧ M-2*b<auxiliary ∧ auxiliary<M ∧
    theta+delta ≤ actualSelectedSubproductV (1+3*kappa)
      (selectedWord (prefixSlots mask t u z)).sum ∧
    2*theta-1 ≤ (selectedWord (prefixSlots mask t u z)).sum ∧
    (selectedWord (prefixSlots mask t u z)).sum ≤
      actualSelectedSubproductUpper (1+3*kappa) theta ∧
    SquareGates auxiliary 0 [t,u,z] ∧
    SquareGates auxiliary (selectedWord (prefixSlots mask t u z)).sum
      (remainingWord (prefixSlots mask t u z))

/-- The empty W mask is not made into a selected critical product. Its
separate initialization and first-overflow inequalities retain c, the
original W ceiling (a for a root source, z for a fresh source). -/
def WCover (t u z b kappa M c : ℝ) : Prop :=
  0≤c ∧ c≤a ∧ z≤c ∧ M=B c ∧ w t u c=B c ∧
    (1/2:ℝ)<M-b/2 ∧ M-b/2≤cap ∧
    t≤2*(M-b/2)-1 ∧
    2*u≤1-(M-b/2)-2*(b/4) ∧
    (1/3:ℝ)≤1-(M-b/2)-2*(b/4) ∧
    c+(2*(M-b/2)-1)≤actualSelectedSubproductUpper (1+3*kappa) (M-b/2) ∧
    (M-b/2)-2*(b/4)=M-b ∧
    M-2*b<M-b ∧ M-b<M ∧
    SquareGates (M-b) 0 [t,u,z] ∧
    SquareGates (M-b) (selectedWord (prefixSlots ∅ t u z)).sum
      (remainingWord (prefixSlots ∅ t u z))

theorem selected_sum (t u z : ℝ) (s : Source) :
    (selectedWord (prefixSlots (sourceMask s) t u z)).sum =
      selectedExponent t u z s := by
  cases s <;> norm_num [prefixSlots,sourceMask,selectedWord,selectedExponent] <;> ring

private theorem original_bounds {t u z : ℝ} (hd : Domain t u z) :
    A t≤original t u z ∧ original t u z≤cap ∧ (1/2+a/2:ℝ)≤original t u z := by
  have ho := domain_ordered hd
  have hv := v_le_original ho
  rw [v_eq_A ho.2.2.2] at hv
  refine ⟨hv,original_le_cap ho,?_⟩
  have ht : a≤t := hd.1.trans hd.2.1
  dsimp [A] at hv
  linarith

private theorem selected_cover_of_margin {t u z b kappa M theta delta auxiliary e : ℝ}
    (hd : Domain t u z) (hb : b≤1/1000) (hM : A t≤M) (mask : Finset (Fin 5))
    (hdelt : 0<delta) (htheta : (1/2:ℝ)<theta) (htop : theta≤cap)
    (haux : theta-2*delta=auxiliary) (hphys : M-2*b<auxiliary) (hauxM : auxiliary<M)
    (he : 0≤e) (hk : kappa≤e/4) (hdelta : delta≤e/8)
    (hsource : theta+e/4≤v (selectedWord (prefixSlots mask t u z)).sum) :
    SelectedCover t u z b kappa M mask theta delta auxiliary := by
  have hm := actualSelectedSubproductV_residue_margin he hk hsource
  have hs : theta+delta≤actualSelectedSubproductV (1+3*kappa)
      (selectedWord (prefixSlots mask t u z)).sum := by linarith
  have hc := (actualSelectedSubproduct_critical_iff (1+3*kappa) theta
    (selectedWord (prefixSlots mask t u z)).sum).mp (by linarith :
      theta≤actualSelectedSubproductV (1+3*kappa)
        (selectedWord (prefixSlots mask t u z)).sum)
  have hg := all_masks_full_and_complement hd hb hM mask
  have hcover : M-2*b-1/32≤auxiliary := by linarith
  exact ⟨hdelt,htheta,htop,haux,hphys,hauxM,hs,hc.1,hc.2,
    square_mono _ hcover hg.1,square_mono _ hcover hg.2⟩

theorem tent_winner_cover {t u z b kappa : ℝ} (hd : Domain t u z)
    (hb : 0<b) (hbhi : b≤1/1000) (hk : kappa≤b/8)
    (htent : ¬isW (winner t u z)) :
    SelectedCover t u z b kappa (original t u z) (sourceMask (winner t u z))
      (original t u z-b/2) (b/4) (original t u z-b) := by
  obtain ⟨hbase,htop,hfloor⟩ := original_bounds hd
  have hv : v (selectedWord (prefixSlots (sourceMask (winner t u z)) t u z)).sum =
      original t u z := by
    rw [selected_sum,←tent_source_value htent,winner_eq_original hd]
  apply selected_cover_of_margin (e:=2*b) hd hbhi hbase _
  · positivity
  · dsimp [a,Part5OriginalUpsilon5CausalDictionary.a] at hfloor; linarith
  · linarith
  · ring
  · linarith
  · linarith
  · positivity
  · linarith
  · linarith
  · rw [hv]; linarith

/-- The manuscript's near-W singleton cover has a strict reserve, at the
same physical cap. It applies also to a true W/tent tie; no tie set is
discarded and the winning source label is not changed. -/
theorem W_near_singleton_cover {t u z b kappa : ℝ} (hd : Domain t u z)
    (hb : 0<b) (hbhi : b≤1/1000) (hk : kappa≤b/8)
    (hnear : original t u z-2*b+b/2≤A t) :
    SelectedCover t u z b kappa (original t u z) {0}
      (original t u z-13*b/8) (b/16) (original t u z-7*b/4) := by
  obtain ⟨hbase,htop,hfloor⟩ := original_bounds hd
  have hs : (selectedWord (prefixSlots {0} t u z)).sum=t := by
    norm_num [prefixSlots,selectedWord]
  have hv : v t=A t := v_eq_A (domain_ordered hd).2.2.2
  apply selected_cover_of_margin (e:=b/2) hd hbhi hbase _
  · positivity
  · dsimp [a,Part5OriginalUpsilon5CausalDictionary.a] at hfloor; linarith
  · linarith
  · ring
  · linarith
  · linarith
  · positivity
  · linarith
  · linarith
  · rw [hs,hv]; linarith

/-- Separated W branch: initialization, the actual ceiling and BOTH
critical upper constraints follow from the full winner and the primitive
complementary near/far test. No `Geometry` premise is supplied by a caller. -/
theorem W_far_cover {t u z b kappa : ℝ} (hd : Domain t u z)
    (hb : 0<b) (hbhi : b≤1/1000) (hk : kappa≤b/8)
    (hw : isW (winner t u z))
    (hfar : A t<original t u z-2*b+b/2) :
    WCover t u z b kappa (original t u z) (sourceCeiling z (winner t u z)) := by
  obtain ⟨hc0,hca,hzc,hvalue,hgate⟩ := W_winner_original_gate hd hw
  have hM : original t u z=B (sourceCeiling z (winner t u z)) :=
    (winner_eq_original hd).symm.trans hvalue
  obtain ⟨hbase,htop,hfloor⟩ := original_bounds hd
  have hu : u≤h := hd.2.1.trans hd.2.2.1
  have hg := all_masks_full_and_complement hd hbhi hbase (∅:Finset (Fin 5))
  have hcover : original t u z-2*b-1/32≤original t u z-b := by linarith
  refine ⟨hc0,hca,hzc,hM,hgate,?_,?_,?_,?_,?_,?_,by ring,by linarith,by linarith,
    square_mono _ hcover hg.1,square_mono _ hcover hg.2⟩
  · dsimp [a,Part5OriginalUpsilon5CausalDictionary.a] at hfloor; linarith
  · linarith
  · dsimp [A] at hfar; linarith
  · dsimp [h,Part5OriginalUpsilon5CausalDictionary.h,cap] at hu htop; linarith
  · dsimp [cap] at htop; linarith
  · rw [hM]
    unfold actualSelectedSubproductUpper
    apply le_min <;>
      dsimp [B,cap,a,Part5OriginalUpsilon5CausalDictionary.a] at * <;> linarith

def Licensed (t u z b kappa : ℝ) : Prop :=
    (¬isW (winner t u z) ∧
      SelectedCover t u z b kappa (original t u z) (sourceMask (winner t u z))
        (original t u z-b/2) (b/4) (original t u z-b)) ∨
    (isW (winner t u z) ∧ original t u z-2*b+b/2≤A t ∧
      SelectedCover t u z b kappa (original t u z) {0}
        (original t u z-13*b/8) (b/16) (original t u z-7*b/4)) ∨
    (isW (winner t u z) ∧ A t<original t u z-2*b+b/2 ∧
      WCover t u z b kappa (original t u z) (sourceCeiling z (winner t u z)))

/-- No successful winner, W gate, full-square predicate, selected-square
predicate, or critical interval is an input. The first disjunct retains a
non-W winner's actual mask. Only the near-W analytic cover uses {0}. -/
theorem full_original_winner_cover {t u z b kappa : ℝ} (hd : Domain t u z)
    (hb : 0<b) (hbhi : b≤1/1000) (hk : kappa≤b/8) : Licensed t u z b kappa := by
  unfold Licensed
  by_cases hw : isW (winner t u z)
  · by_cases hn : original t u z-2*b+b/2≤A t
    · exact Or.inr (Or.inl ⟨hw,hn,W_near_singleton_cover hd hb hbhi hk hn⟩)
    · exact Or.inr (Or.inr ⟨hw,lt_of_not_ge hn,
        W_far_cover hd hb hbhi hk hw (lt_of_not_ge hn)⟩)
  · exact Or.inl ⟨hw,tent_winner_cover hd hb hbhi hk hw⟩

/-- All later unselected slots require only their literal full-prefix
squares. The old selected mask and every old complement test survive.
This does not assert that an unconstructed adopted continuation is legal. -/
theorem selected_complement_suffix (cap : ℝ) (slots : List Slot) (xs : List ℝ)
    (hselected : SquareGates cap (selectedWord slots).sum (remainingWord slots))
    (hfullSuffix : SquareGates cap (slots.map Slot.exponent).sum xs) :
    SquareGates cap (selectedWord (slots++xs.map unselected)).sum
      (remainingWord (slots++xs.map unselected)) := by
  have hwords : selectedWord (xs.map unselected)=[] ∧
      remainingWord (xs.map unselected)=xs := by
    induction xs with
    | nil => exact ⟨rfl,rfl⟩
    | cons x xs ih => simpa [selectedWord,remainingWord,unselected] using ih
  rw [selectedWord_append,remainingWord_append,hwords.1,hwords.2,List.append_nil,
    squareGates_append_iff,selected_remaining_sum]
  exact ⟨hselected,hfullSuffix⟩

end
end ImbalancedChen.P5OriginalU5MixedCover
