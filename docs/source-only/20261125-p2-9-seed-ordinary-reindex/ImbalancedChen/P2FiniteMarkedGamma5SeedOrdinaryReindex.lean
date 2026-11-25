import ImbalancedChen.P2FiniteMarkedGamma5SeedCellFibre

namespace ImbalancedChen.P2FiniteMarkedGamma5SeedOrdinaryReindex
noncomputable section
open Finset Real
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open Part5OriginalH430PhysicalRoots (Root sourceRoot)
open Part5OriginalH430FrozenRootRefinement (rootCode RootCode frozenLeafCutoffFloor)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430SameQHistoryCells (cellQ)
open Part5OriginalH430NativeQueryPaths (NativeSlot)
open P2FiniteMarkedGamma5SeedAtlasFinitePP (Entry oldRank tailRank rank Tuple)
open P2FiniteMarkedGamma5SeedCellFibre (exactCell sum_fibre)
open P2FiniteMarkedGamma5NativeSeedSum (Index fixedWeight primeTuples coordinateOld)
open P2FiniteMarkedGamma5SeedOrdinaryPrice (seedMass completeProfile)
open P2FiniteMarkedGamma5RealSelectedPrefix (selected)
open P2FiniteMarkedGamma5ActualRadialAggregate
  (tuplePrefix tuplePrefix_length Split admissibleSplit boundedProfileWeight boundedProfileSlice)
open P2FiniteMarkedGamma5ActualRank (frozenSourceRankBound)
open P2FiniteMarkedGamma5ActualRootCells (originalRootCellBand_Q mem_originalRootCellBand)
open P2FiniteMarkedGamma5EulerWordBudget (finPhysicalProfile)
open P2FiniteMarkedGamma5IntegerSupport (finPhysicalProfile_nonzero_support)
open P2FiniteMarkedGamma5RadialProfileCollar (radialWidth radialWidth_pos exp_radialWidth_lt_two)
open P2FiniteMarkedGamma5RadialNaturalMass (tupleValues)
open P2FiniteMarkedGamma5OrderedOldSlots (coordinateOld_length)
open scoped Classical BigOperators

private abbrev K := frozenSourceRankBound
private abbrev R := Fin (K+1)
private abbrev axis (i : Index 430) := Nat.card (NativeSlot i.val.1)
private abbrev X (N : ℕ) (i : Index 430) := NativeSlot i.val.1 → Fin (N+1)
private def codeOf {N : ℕ} (n : ℕ) (t : ℝ) {i : Index 430} (x : X N i) : RootCode n :=
  rootCode n (sourceRoot .U4 t (physicalPrime N (x (.inl ())).val)).physical.total
private def active {N : ℕ} (n : ℕ) (t : ℝ) (i : Index 430) (x : X N i) : Prop :=
  (fun z => physicalPrime N (x z).val) ∈ selected n .U4 t i.val.1 i.val.2
private def originalWord {N : ℕ} (n : ℕ) (t : ℝ) (i : Index 430) (x : X N i) :=
  coordinateOld n .U4 t ⟨i,x⟩

def profile {N n : ℕ} (h : ℝ) (v : Entry n) (u : Tuple N v) : ℝ :=
  finPhysicalProfile (log (cellQ N n v.val.2.1)) (N:ℝ) (radialWidth h)
    ((N:ℝ)^frozenLeafCutoffFloor) (fun j => ((u j).val:ℝ))

def literalMass (N n : ℕ) (t h : ℝ) : ℝ :=
  ∑ v : Entry n, fixedWeight v.val.1 *
    ∑ u ∈ Part3.labelledPrimeTuples (rank v) (2*N),
      if exactCell v .U4 t u then profile h v u else 0

private theorem entry_fubini {N n : ℕ} (t h : ℝ) (v : Entry n)
    (hN : 0<N) (hp : 0<h) (h8 : h≤1/8) :
    (∑ u ∈ Part3.labelledPrimeTuples (rank v) (2*N),
      if exactCell v .U4 t u then profile h v u else 0) =
    ∑ x ∈ primeTuples N .U4 v.val.1,
      if codeOf n t x = v.val.2.1 ∧ active n t v.val.1 x then
        boundedProfileSlice N (oldRank v) (tailRank v)
          (log (cellQ N n v.val.2.1)) h (originalWord n t v.val.1 x) else 0 := by
  let S := Part3.labelledPrimeTuples (rank v) (2*N)
  let B := primeTuples N .U4 v.val.1
  let E (x : X N v.val.1) := codeOf n t x = v.val.2.1 ∧ active n t v.val.1 x
  let M (x : X N v.val.1) (u : Tuple N v) :=
    originalWord n t v.val.1 x = tuplePrefix (k:=oldRank v) (r:=tailRank v) (tupleValues u)
  calc
    _ = ∑ u ∈ S, ∑ x ∈ B, if E x ∧ M x u then profile h v u else 0 := by
      apply sum_congr rfl
      intro u hu
      by_cases hz : profile h v u = 0
      · simp [hz]
      · have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
        have hcap := (finPhysicalProfile_nonzero_support
          (rpow_pos_of_pos hNr frozenLeafCutoffFloor) hNr (radialWidth_pos hp)
          (show finPhysicalProfile (log (cellQ N n v.val.2.1)) (N:ℝ) (radialWidth h)
            ((N:ℝ)^frozenLeafCutoffFloor) (fun j => ((u j).val:ℝ)) ≠ 0 from hz)).2
        have hm : (∏ j,(u j).val) ≤ 2*N := by
          have H := (hcap.trans (mul_lt_mul_of_pos_right (exp_radialWidth_lt_two hp h8) hNr)).le
          exact_mod_cast H
        simpa only [E,M,codeOf,active,originalWord, and_assoc] using
          (sum_fibre v .U4 t u (mem_filter.mp hu).2 hm (profile h v u)).symm
    _ = ∑ x ∈ B, ∑ u ∈ S, if E x ∧ M x u then profile h v u else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro x _
      by_cases he : E x
      · simpa only [show codeOf n t x = v.val.2.1 ∧ active n t v.val.1 x from he,
          if_true,he,true_and,boundedProfileSlice,boundedProfileWeight,M,profile,S]
      · simp only [show ¬ (codeOf n t x = v.val.2.1 ∧ active n t v.val.1 x) from he,
          if_false,he,false_and,sum_const_zero]

private theorem wrong_rank (N k r : ℕ) (L h : ℝ) (w : List ℕ) (hm : w.length ≠ k) :
    boundedProfileSlice N k r L h w = 0 := by
  apply sum_eq_zero
  intro u _
  apply if_neg
  intro hw
  exact hm ((congrArg List.length hw).trans (tuplePrefix_length _))

private theorem collapse_split {N : ℕ} (n : ℕ) (t h : ℝ) (i : Index 430)
    (x : X N i) (L : ℝ) :
    (∑ s : Split, if admissibleSplit s then
      boundedProfileSlice N s.1.val s.2.val L h (originalWord n t i x) else 0) =
    ∑ r : R, if axis i+2+r.val ≤ K then
      boundedProfileSlice N (axis i) r.val L h (originalWord n t i x) else 0 := by
  rw [Fintype.sum_prod_type,sum_comm]
  apply sum_congr rfl
  intro r _
  have hlen := coordinateOld_length n .U4 t i x
  by_cases ha : axis i+2+r.val ≤ K
  · let j : R := ⟨axis i,by omega⟩
    rw [if_pos ha]
    calc
      _ = (if admissibleSplit (j,r) then boundedProfileSlice N j.val r.val L h
            (originalWord n t i x) else 0) := by
        apply sum_eq_single j
        · intro b _ hb
          have H : (originalWord n t i x).length ≠ b.val := by
            intro eq
            apply hb
            exact Fin.ext (eq.symm.trans hlen)
          simp [wrong_rank N b.val r.val L h _ H]
        · simp
      _ = _ := by simp [admissibleSplit,j,ha]
  · rw [if_neg ha]
    apply sum_eq_zero
    intro b _
    by_cases hb : b.val = axis i
    · simp [admissibleSplit,hb,ha]
    · have H : (originalWord n t i x).length ≠ b.val := fun eq => hb (eq.symm.trans hlen)
      simp [wrong_rank N b.val r.val L h _ H]

private def term {N : ℕ} (n : ℕ) (t h : ℝ) (i : Index 430)
    (c : RootCode n) (r : R) (x : X N i) : ℝ :=
  if codeOf n t x = c ∧ active n t i x then
    if axis i+2+r.val ≤ K then fixedWeight i *
      boundedProfileSlice N (axis i) r.val (log (cellQ N n c)) h (originalWord n t i x)
    else 0
  else 0

private theorem expand_entries {N n : ℕ} (t h : ℝ) (hN : 0<N) (hp : 0<h) (h8 : h≤1/8) :
    literalMass N n t h =
      ∑ i : Index 430, ∑ c : RootCode n, ∑ r : R, ∑ x ∈ primeTuples N .U4 i,
        term n t h i c r x := by
  let F (w : Index 430 × RootCode n × R) := ∑ x ∈ primeTuples N .U4 w.1,
    term n t h w.1 w.2.1 w.2.2 x
  have H : (∑ w, F w) = ∑ i : Index 430, ∑ c : RootCode n, ∑ r : R,
      ∑ x ∈ primeTuples N .U4 i, term n t h i c r x := by
    simp only [F,Fintype.sum_prod_type]
  rw [← H]
  let good (w : Index 430 × RootCode n × R) := axis w.1+2+w.2.2.val ≤ K
  have filterF : (∑ w ∈ univ.filter good, F w) = ∑ w, F w := by
    rw [sum_filter]
    apply sum_congr rfl
    intro w _
    by_cases hg : good w
    · simp only [if_pos hg]
    · have hh : ¬ axis w.1+2+w.2.2.val ≤ K := hg
      simp [F,term,hh,hg]
  have subtypeF : (∑ v : Entry n, F v.val) = ∑ w ∈ univ.filter good, F w := by
    apply sum_bij (fun (v : Entry n) _ => v.val)
    · intro v _
      exact mem_filter.mpr ⟨mem_univ _,v.property⟩
    · intro v _ v' _ he
      exact Subtype.ext he
    · intro w hw
      exact ⟨⟨w,(mem_filter.mp hw).2⟩,mem_univ _,rfl⟩
    · intro _ _
      rfl
  rw [← filterF,← subtypeF]
  unfold literalMass
  apply sum_congr (Finset.ext (fun _ => by simp))
  intro v _
  rw [entry_fubini t h v hN hp h8,mul_sum]
  apply sum_congr rfl
  intro x _
  have hg : axis v.val.1 + 2 + v.val.2.2.val ≤ K := v.property
  by_cases he : codeOf n t x = v.val.2.1 ∧ active n t v.val.1 x <;>
    simp [F,term,hg,he,oldRank,tailRank,axis]

private theorem finish_word {N n : ℕ} (t h : ℝ) (i : Index 430) (x : X N i)
    (hx : x ∈ primeTuples N .U4 i) :
    (∑ c : RootCode n, ∑ r : R, term n t h i c r x) =
    if active n t i x then fixedWeight i *
      completeProfile N n t h (x (.inl ())).val (originalWord n t i x) else 0 := by
  by_cases hs : active n t i x
  · rw [if_pos hs]
    have hq := originalRootCellBand_Q (root:=.U4) (t:=t) (n:=n) (N:=N) (mem_originalRootCellBand.mpr
      ⟨(mem_filter.mp hx).2.1,(rfl : rootCode n
        (sourceRoot .U4 t (physicalPrime N (x (.inl ())).val)).physical.total = codeOf n t x)⟩)
    calc
      _ = ∑ r : R, term n t h i (codeOf n t x) r x := by
        apply sum_eq_single (codeOf n t x)
        · intro c _ hc
          simp [term,Ne.symm hc]
        · simp
      _ = _ := by
        unfold completeProfile
        rw [hq,collapse_split n t h i x,mul_sum]
        apply sum_congr rfl
        intro r _
        by_cases ha : axis i+2+r.val ≤ K <;> simp [term,hs,ha]
  · simp [term,hs]

/-- The entire fixed Entry sum on its exact arithmetic carrier is the
literal original U4 seed profile. The equality imposes no target
coprimality on either fresh prime or on any tail coordinate. -/
theorem literalMass_eq_seedMass {N : ℕ} (n : ℕ) (t h : ℝ)
    (hN : 0<N) (hp : 0<h) (h8 : h≤1/8) :
    literalMass N n t h = seedMass N n .U4 t (completeProfile N n t h) := by
  rw [expand_entries t h hN hp h8]
  unfold seedMass
  apply sum_congr rfl
  intro i _
  calc
    _ = ∑ c : RootCode n, ∑ x ∈ primeTuples N .U4 i, ∑ r : R, term n t h i c r x :=
      sum_congr rfl (fun _ _ => sum_comm)
    _ = ∑ x ∈ primeTuples N .U4 i, ∑ c : RootCode n, ∑ r : R, term n t h i c r x := sum_comm
    _ = _ := sum_congr rfl (fun x hx => finish_word t h i x hx)

end
end ImbalancedChen.P2FiniteMarkedGamma5SeedOrdinaryReindex
