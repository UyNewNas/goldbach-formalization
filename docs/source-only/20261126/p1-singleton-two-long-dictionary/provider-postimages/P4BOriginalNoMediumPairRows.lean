import ImbalancedChen.P1OriginalSingletonTwoLongFiniteGeometry
import ImbalancedChen.P4BOriginalHighRankLocalLevel
import ImbalancedChen.Part3TwoLongRetainedRowReindex

/-! SOURCE ONLY / UNCOMPILED. Actual ordered two-mother rows.
Dead rows are removed at their integer source, not by asserting that
their Fourier amplitude vanishes. Long slots are positions, not values.
The short scale is the product of the remaining block LOWER endpoints. -/
namespace ImbalancedChen.P4BOriginalNoMediumPairRows
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos owns_bounds)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle mem_rectangle)
open P5Z.ActualHBPostModulusLogCutoff (hbSlots completeProduct)
open P5Z.ActualRoughHeathBrownWords (Role)
open P5Z.ActualHBMediumBranchPartition
open P5Z.ExactOriginalSmoothDyadicPartition (R R_pos beforeHBCutoff)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P4BUpperPairOrderedRowGeometry
open P4BUpperPairOrderedRowModes (rowAtom)
open P4BOriginalHighRankMotherScale (completeScale live_geometry)
open Part3.TwoLongActualHBShortMass (ShortPositions shortScale)
open P4BOuterRampRoughness (baseline)

theorem firstMedium_none_append {a d : ℕ} (A B : ℝ)
    (bs : Fin a→Block) (cs : Fin d→Block) :
    firstMedium A B (List.ofFn bs++List.ofFn cs)=none ↔
      firstMedium A B (List.ofFn (Fin.append bs cs))=none := by
  rw [firstMedium_none,firstMedium_none]
  constructor
  · intro h block hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.append_left] using h (bs i)
        (List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨i,rfl⟩)))
    · simpa only [Fin.append_right] using h (cs i)
        (List.mem_append.mpr (Or.inr (List.mem_ofFn.mpr ⟨i,rfl⟩)))
  · intro h block hb
    rcases List.mem_append.mp hb with hb|hb
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
      exact h _ (List.mem_ofFn.mpr ⟨Fin.castAdd d i,Fin.append_left bs cs i⟩)
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
      exact h _ (List.mem_ofFn.mpr ⟨Fin.natAdd a i,Fin.append_right bs cs i⟩)

/-- The native type-I selector on the two actual Row records is exactly
the Fin.append block-only test. Factors, frequencies and rho play no role. -/
theorem typeI_pair_selector {a d : ℕ} (A B : ℝ) (j l : ℕ)
    (bs : Fin a→Block) (cs : Fin d→Block) (u : Fin a→ℕ) (v : Fin d→ℕ)
    (F : List P5Z.PerGroupIntegerHBAtlasPushforward.Row→ℂ) :
    P5Z.PerGroupIntegerHBAtlasPushforward.typeIValue A B F
      [{order:=j,blocks:=List.ofFn bs,factors:=List.ofFn u},
       {order:=l,blocks:=List.ofFn cs,factors:=List.ofFn v}] =
      if firstMedium A B (List.ofFn (Fin.append bs cs))=none then
        F [{order:=j,blocks:=List.ofFn bs,factors:=List.ofFn u},
           {order:=l,blocks:=List.ofFn cs,factors:=List.ofFn v}] else 0 := by
  unfold P5Z.PerGroupIntegerHBAtlasPushforward.typeIValue
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change (if firstMedium A B (List.ofFn bs++List.ofFn cs)=none then _ else 0)=_
  by_cases h : firstMedium A B (List.ofFn (Fin.append bs cs))=none
  · rw [if_pos h,if_pos ((firstMedium_none_append A B bs cs).mpr h)]
  · rw [if_neg h,if_neg (fun H => h ((firstMedium_none_append A B bs cs).mp H))]

def noMedium {t : ℕ} (zeta : ℝ) (cj ck : ℕ) (bs : Fin t → Block) : Prop :=
  firstMedium (originalLower (R cj*R ck) zeta)
    (originalUpper (R cj*R ck) zeta) (List.ofFn bs) = none

theorem noMedium_eq_original {t : ℕ} (zeta : ℝ) (cj ck : ℕ) (bs : Fin t→Block) :
    noMedium zeta cj ck bs ↔
      firstMedium (P5Z.OriginalPrimeAtlasReserveBranches.originalMediumLow zeta [cj,ck])
        (P5Z.OriginalPrimeAtlasReserveBranches.originalMediumHigh zeta [cj,ck])
        (List.ofFn bs)=none := by
  simp [noMedium,originalLower,originalUpper,
    P5Z.OriginalPrimeAtlasReserveBranches.originalMediumLow,
    P5Z.OriginalPrimeAtlasReserveBranches.originalMediumHigh,
    P5Z.ExactOriginalSmoothDyadicPartition.scales]

theorem native_selector {j l cj ck : ℕ} (zeta : ℝ) (bs cs : List Block)
    (hbs : bs∈P5Z.ActualHBDyadicOccurrenceFamily.blockWords
      (P5Z.PerGroupIntegerHBAtlasPushforward.hbCap cj) (2*(j+1)))
    (hcs : cs∈P5Z.ActualHBDyadicOccurrenceFamily.blockWords
      (P5Z.PerGroupIntegerHBAtlasPushforward.hbCap ck) (2*(l+1))) :
    noMedium zeta cj ck
      (Fin.append (P5Z.OrderedFactorTupleRectangleReindex.blockVector (2*(j+1)) bs)
        (P5Z.OrderedFactorTupleRectangleReindex.blockVector (2*(l+1)) cs)) ↔
      firstMedium (P5Z.OriginalPrimeAtlasReserveBranches.originalMediumLow zeta [cj,ck])
        (P5Z.OriginalPrimeAtlasReserveBranches.originalMediumHigh zeta [cj,ck]) (bs++cs)=none := by
  rw [noMedium_eq_original,←firstMedium_none_append]
  rw [P5Z.OrderedFactorTupleRectangleReindex.ofFn_blockVector
    (P5Z.ActualHBDyadicOccurrenceFamily.blockWords_spec _ _ _ hbs).1,
    P5Z.OrderedFactorTupleRectangleReindex.ofFn_blockVector
    (P5Z.ActualHBDyadicOccurrenceFamily.blockWords_spec _ _ _ hcs).1]

/-- A fixed block-only choice. Neither the integer source point nor rho
occurs in its definition. Each live no-medium mother has a long slot. -/
def chooseLong {t : ℕ} (ht : 0<t) (B : ℝ) (bs : Fin t→Block) : Fin t :=
  if h : ∃ i : Fin t,B<(lower (bs i):ℝ) then Classical.choose h else ⟨0,ht⟩

theorem chooseLong_long {t : ℕ} (ht : 0<t) (B : ℝ) (bs : Fin t→Block)
    (h : ∃ i : Fin t,B<(lower (bs i):ℝ)) :
    B<(lower (bs (chooseLong ht B bs)):ℝ) := by
  simp only [chooseLong,dif_pos h]
  exact Classical.choose_spec h

def live {u v : ℕ} (b kap s : ℝ) (N : ℕ) (kap0 : ℝ) (cj ck : ℕ)
    (bs : Fin (u+v) → Block) (Z : ℝ) (ys : Fin (u+v) → ℝ)
    (rs : Fin (u+v) → Role) : Prop :=
  ∃ y ∈ rectangle bs,
    hbSlots Z ys rs y * (integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y : ℂ) ≠ 0

theorem dead_row_zero {u v : ℕ} (b kap s : ℝ) (N : ℕ) (kap0 : ℝ) (cj ck : ℕ)
    (bs : Fin (u+v) → Block) (Z : ℝ) (ys : Fin (u+v) → ℝ)
    (rs : Fin (u+v) → Role) (Q : Finset ℕ) (rho : ℕ → ℂ)
    (hdead : ¬live b kap s N kap0 cj ck bs Z ys rs) :
    rowAtom b kap s N kap0 cj ck bs Z ys rs Q rho = 0 := by
  unfold rowAtom PrimeProducts.MellinInsertion20261028.exactDiscrepancy
    PrimeProducts.MellinInsertion20261028.functional
  apply Finset.sum_eq_zero
  intro y hy
  have hz : hbSlots Z ys rs y *
      (integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y : ℂ) = 0 := by
    by_contra hn
    exact hdead ⟨y,hy,hn⟩
  simp [hz]

theorem row_eq_live_test {u v : ℕ} (b kap s : ℝ) (N : ℕ) (kap0 : ℝ) (cj ck : ℕ)
    (bs : Fin (u+v) → Block) (Z : ℝ) (ys : Fin (u+v) → ℝ)
    (rs : Fin (u+v) → Role) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    rowAtom b kap s N kap0 cj ck bs Z ys rs Q rho =
      if live b kap s N kap0 cj ck bs Z ys rs then
        rowAtom b kap s N kap0 cj ck bs Z ys rs Q rho else 0 := by
  by_cases h : live b kap s N kap0 cj ck bs Z ys rs
  · rw [if_pos h]
  · rw [if_neg h]
    exact dead_row_zero _ _ _ _ _ _ _ _ _ _ _ _ _ h

/-- Actual source support gives both original prime-product lower
windows and the shared upper product window, before any mode estimate. -/
theorem profile_data {u v N : ℕ} {b kap s kap0 : ℝ}
    (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96)
    (cj ck : ℕ) (y : Fin (u+v) → ℕ)
    (hw : integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y ≠ 0) :
    2≤N ∧ (N:ℝ)^(19/96:ℝ)<(completeProduct (leftPart y):ℝ) ∧
      (N:ℝ)^(19/96:ℝ)<(completeProduct (rightPart y):ℝ) ∧
      (completeProduct y:ℝ)<4*(R cj*R ck) := by
  let p : Fin 2 → ℝ := fun j => (P5Z.ActualAllRankOccurrenceFourierBridge.integerGroupProduct
    (pairOwner u v) y j : ℝ)
  have hnorm : P4BArbitraryWidthUpperPairHBNormalization.normalizedProfile b kap s N p ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).1
  have hG : 2*s≤baseline b kap-1*(19/96:ℝ) := by simpa using hg
  obtain ⟨hN,hpos,hprime,_⟩ := P4BArbitraryWidthUpperPairHBNormalization.normalized_support
    hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) hs hG hnorm
  have hpsi := (mul_ne_zero_iff.mp hw).2
  have h0 := P4BOriginalRankTwoChartScales.psi_window (R_pos cj)
    (Finset.prod_ne_zero_iff.mp hpsi 0 (Finset.mem_univ _))
  have h1 := P4BOriginalRankTwoChartScales.psi_window (R_pos ck)
    (Finset.prod_ne_zero_iff.mp hpsi 1 (Finset.mem_univ _))
  have hleft : (N:ℝ)^(19/96:ℝ)<(completeProduct (leftPart y):ℝ) := by
    simpa [p,pair_group_zero] using hprime 0
  have hright : (N:ℝ)^(19/96:ℝ)<(completeProduct (rightPart y):ℝ) := by
    simpa [p,pair_group_one] using hprime 1
  have h0' : (completeProduct (leftPart y):ℝ)<2*R cj := by simpa [p] using h0.2
  have h1' : (completeProduct (rightPart y):ℝ)<2*R ck := by simpa [p] using h1.2
  have hp0 : 0<(completeProduct (leftPart y):ℝ) :=
    (Real.rpow_nonneg (Nat.cast_nonneg N) (19/96:ℝ)).trans_lt hleft
  have hprod1 := mul_lt_mul_of_pos_left h1' hp0
  have hprod2 := mul_lt_mul_of_pos_right h0' (by positivity : 0<2*R ck)
  refine ⟨hN,hleft,hright,?_⟩
  rw [completeProduct_parts,Nat.cast_mul]
  nlinarith only [hprod1,hprod2]

/-- The finite, block-only selection. The two explicit power inequalities
are supplied uniformly from the original source by the next module.
No Assigned, medium licence, or arithmetic cancellation premise occurs. -/
theorem select_actual_pair {j l N : ℕ} (hj : j∈Finset.range 3) (hl : l∈Finset.range 3)
    {b kap s kap0 zeta : ℝ} (hb : 0<b) (hs : 0<s)
    (hg : 2*s≤baseline b kap-19/96) (hz : 0<zeta)
    (cj ck : ℕ) (bs : Fin (2*(j+1)) → Block) (cs : Fin (2*(l+1)) → Block)
    (y : Fin (2*(j+1)+2*(l+1)) → ℕ)
    (hy : y∈rectangle (Fin.append bs cs))
    (hw : integerProfile (a:=2*(j+1)) (d:=2*(l+1)) b kap s N kap0 cj ck y≠0)
    (hnone : noMedium zeta cj ck (Fin.append bs cs))
    (hshort : 64*(R cj*R ck)^(18*zeta)<(N:ℝ)^(19/96:ℝ))
    (hthree : 4<(R cj*R ck)^(3*zeta/4)) :
    ∃ i1 : Fin (2*(j+1)), ∃ i2 : Fin (2*(l+1)),
      i1=chooseLong (by omega) ((R cj*R ck)^(1/3+zeta/4:ℝ)) bs ∧
      i2=chooseLong (by omega) ((R cj*R ck)^(1/3+zeta/4:ℝ)) cs ∧
      let i := Fin.castAdd (2*(l+1)) i1
      let k := Fin.natAdd (2*(j+1)) i2
      let blocks := Fin.append bs cs
      let X := R cj*R ck
      i≠k ∧ X^(1/3+zeta/4:ℝ)<(lower (blocks i):ℝ) ∧
      X^(1/3+zeta/4:ℝ)<(lower (blocks k):ℝ) ∧
      Fintype.card (ShortPositions i k)≤10 ∧
      (∀ a : ShortPositions i k,(lower (blocks a.val):ℝ)<X^(3*zeta)) ∧
      (shortScale (fun a : ShortPositions i k => blocks a.val):ℝ)≤X^(30*zeta) := by
  let X := R cj*R ck
  let A := X^(3*zeta)
  let B := X^(1/3+zeta/4:ℝ)
  let blocks := Fin.append bs cs
  have hX : 1≤X := by
    have h1 : (1:ℝ)≤R cj := one_le_pow₀ (by norm_num)
    have h2 : (1:ℝ)≤R ck := one_le_pow₀ (by norm_num)
    dsimp [X]
    nlinarith
  have hXp : 0<X := mul_pos (R_pos cj) (R_pos ck)
  have hA : 1≤A := Real.one_le_rpow hX (by dsimp [A]; linarith)
  have hB : 1≤B := Real.one_le_rpow hX (by linarith)
  have hnone' : firstMedium A B (List.ofFn blocks)=none := hnone
  have hnona (a) : ¬Medium A B (blocks a) :=
    firstMedium_none.mp hnone' _ (List.mem_ofFn.mpr ⟨a,rfl⟩)
  obtain ⟨_,hp1,hp2,hprod⟩ := profile_data hb hs hg cj ck y hw
  have hA6 : A^6=X^(18*zeta) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hXp.le]; congr 1; ring
  have hex1 := group_has_long (by have := Finset.mem_range.mp hj; omega) hA bs (leftPart y)
    (fun a => by simpa [leftPart,blocks,blockScales] using (rectangle_bounds (Fin.append bs cs) hy (Fin.castAdd _ a)).2.2)
    (fun a => by simpa [blocks] using hnona (Fin.castAdd (2*(l+1)) a))
    (by rw [hA6]; exact hshort.trans hp1)
  have hex2 := group_has_long (by have := Finset.mem_range.mp hl; omega) hA cs (rightPart y)
    (fun a => by simpa [rightPart,blocks,blockScales] using (rectangle_bounds (Fin.append bs cs) hy (Fin.natAdd _ a)).2.2)
    (fun a => by simpa [blocks] using hnona (Fin.natAdd (2*(j+1)) a))
    (by rw [hA6]; exact hshort.trans hp2)
  let i1 := chooseLong (by omega) B bs
  let i2 := chooseLong (by omega) B cs
  have hi1 := chooseLong_long (by omega) B bs hex1
  have hi2 := chooseLong_long (by omega) B cs hex2
  let i := Fin.castAdd (2*(l+1)) i1
  let k := Fin.natAdd (2*(j+1)) i2
  have hik : i≠k := by intro he; have H := congrArg Fin.val he; dsimp [i,k] at H; omega
  have hi : i∈longPositions B blocks := by simp [longPositions,blocks,i,hi1]
  have hk : k∈longPositions B blocks := by simp [longPositions,blocks,k,hi2]
  have hraw : rawProduct (List.ofFn blocks)≤(completeProduct y:ℝ) := by
    have H : (List.map lower (List.ofFn blocks)).prod≤completeProduct y := by
      simpa [completeProduct,List.map_ofFn,List.prod_ofFn] using
        Finset.prod_le_prod' (fun a _ => (owns_bounds ((mem_rectangle _ _).mp hy a)).1)
    change (((List.map lower (List.ofFn blocks)).prod:ℕ):ℝ)≤(completeProduct y:ℝ)
    exact_mod_cast H
  have hB3 : B^3=X*X^(3*zeta/4) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hXp.le]
    rw [show (1/3+zeta/4:ℝ)*3=1+3*zeta/4 by ring,Real.rpow_add hXp,Real.rpow_one]
  have hcount : (longPositions B blocks).card≤2 := by
    rw [long_card_eq_length]
    apply atMostTwoLong hB
    rw [hB3]
    exact (hraw.trans_lt hprod).trans (by nlinarith only [mul_lt_mul_of_pos_left hthree hXp])
  have hrest (a : ShortPositions i k) : (lower (blocks a.val):ℝ)<A := by
    have hnlong : ¬B<(lower (blocks a.val):ℝ) := by
      intro ha
      have hsub : ({i,k,a.val}:Finset _)⊆longPositions B blocks := by
        intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        rcases hv with rfl|rfl|rfl
        · exact hi
        · exact hk
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
      have H := Finset.card_le_card hsub
      have h3 : 3≤(longPositions B blocks).card := by
        simpa [hik,a.property.1,a.property.2,a.property.1.symm,a.property.2.symm] using H
      omega
    by_contra! hge
    exact hnona a.val ⟨hge,le_of_not_gt hnlong⟩
  have hcard : Fintype.card (ShortPositions i k)≤10 := by
    have H := short_card i k hik
    have hj' := Finset.mem_range.mp hj
    have hl' := Finset.mem_range.mp hl
    omega
  refine ⟨i1,i2,rfl,rfl,hik,by simpa [blocks,i] using hi1,by simpa [blocks,k] using hi2,hcard,hrest,?_⟩
  calc
    _ = ∏ a : ShortPositions i k,(lower (blocks a.val):ℝ) := by simp [shortScale]
    _ ≤ ∏ _a : ShortPositions i k,A := Finset.prod_le_prod
      (fun _ _ => Nat.cast_nonneg _) (fun a _ => (hrest a).le)
    _ = A^Fintype.card (ShortPositions i k) := by simp
    _ ≤ A^10 := pow_le_pow_right₀ hA hcard
    _ = X^(30*zeta) := by rw [←Real.rpow_natCast,←Real.rpow_mul hXp.le]; congr 1; ring

/-- The genuine live tuple excludes a truncated Mobius long slot.
The argument uses the original per-mother cutoff, not a shared replacement. -/
theorem selected_long_role {j l : ℕ} (cj ck : ℕ) (Z B : ℝ)
    (bs : Fin (2*(j+1))→Block) (cs : Fin (2*(l+1))→Block)
    (y : Fin (2*(j+1)+2*(l+1))→ℕ) (hy : y∈rectangle (Fin.append bs cs))
    (hslots : hbSlots Z (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
      (Fin.append (rowRoles j) (rowRoles l)) y≠0)
    (hcut : hbCutoff cj≤B ∧ hbCutoff ck≤B)
    (i : Fin (2*(j+1)+2*(l+1))) (hi : B<(lower (Fin.append bs cs i):ℝ)) :
    Fin.append (rowRoles j) (rowRoles l) i=.one ∨
      Fin.append (rowRoles j) (rowRoles l) i=.logarithm := by
  have hc : Fin.append (fun _ : Fin (2*(j+1)) => hbCutoff cj)
      (fun _ : Fin (2*(l+1)) => hbCutoff ck) i≤B := by
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i
    · simpa only [Fin.append_left] using hcut.1
    · simpa only [Fin.append_right] using hcut.2
  cases hr : Fin.append (rowRoles j) (rowRoles l) i with
  | mobius =>
      have hm := pair_mobius_cutoff Z cj ck j l y hslots i hr
      have hlower := (rectangle_bounds (Fin.append bs cs) hy i).2.1
      dsimp only [blockScales] at hlower
      linarith
  | one => exact Or.inl rfl
  | logarithm => exact Or.inr rfl

end
end ImbalancedChen.P4BOriginalNoMediumPairRows
