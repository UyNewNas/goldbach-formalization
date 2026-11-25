import ImbalancedChen.P2FiniteMarkedGamma5TestedSeedAtom
import ImbalancedChen.Part5OriginalH430SeedPurifiedPrimeFibres

namespace ImbalancedChen.P2FiniteMarkedGamma5TestedSeedMass
noncomputable section
open Finset Real LiLiuPrereqBuchstab
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open P2EnhancedBadGamma5ArithmeticGeometry (badLabels)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open Part5OriginalH430FrozenRootRefinement (frozenLeafCutoffFloor frozenLeafCutoffFloor_pos)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430NativeQueryPaths (NativeSlot)
open Part5OriginalH430SeedPurifiedPrimeFibres (badFibre fibre)
open P2FiniteMarkedGamma5RealSelectedPrefix (selected)
open P2FiniteMarkedGamma5NativeSeedSum (Index coordinateOld primeTuples fixedWeight)
open P2FiniteMarkedGamma5SeedOrdinaryPrice (seedMass)
open P2FiniteMarkedGamma5SeedAtlasFinitePP (Entry oldRank tailRank rank Tuple weight mark_nonneg)
open P2FiniteMarkedGamma5SeedCellReadout (planAt acceptAt)
open P2FiniteMarkedGamma5AllRankEulerBudget (scaleThreshold)
open P2FiniteMarkedGamma5SharpTupleCount (tupleFresh tupleTail)
open P2FiniteMarkedGamma5ActualRadialAggregate (tuplePrefix)
open P2FiniteMarkedGamma5RadialNaturalMass (tupleValues)
open P2FiniteMarkedGamma5OrderedOldSlots (oldSlotEquiv coordinateOld_eq_ofFn)
open scoped Classical BigOperators

private abbrev I := Index 430
private abbrev X (N : ℕ) (i : I) := NativeSlot i.val.1 → Fin (N+1)
private abbrev Source (N : ℕ) := (i : I) × (x : X N i) × (qs : List ℕ) × ℕ
private abbrev Target (N n : ℕ) := (v : Entry n) × Tuple N v
private abbrev word {N : ℕ} (n : ℕ) (t : ℝ) (i : I) (x : X N i) :=
  coordinateOld n .U4 t ⟨i,x⟩
private abbrev Qx {N : ℕ} (n : ℕ) (t : ℝ) {i : I} (x : X N i) :=
  rootQ N n .U4 t (x (.inl ())).val
private abbrev sel {N : ℕ} (n : ℕ) (t : ℝ) (i : I) (x : X N i) : Prop :=
  (fun z => physicalPrime N (x z).val) ∈ selected n .U4 t i.val.1 i.val.2
private abbrev tested (N M : ℕ) : Prop := M<N ∧ (N-M).Prime
private def cofs (N n : ℕ) (t : ℝ) (i : I) (x : X N i) (qs : List ℕ) :=
  let d := (word n t i x).prod
  (roughNumbers ((N:ℝ)/(d*qs.prod:ℕ)) (cutoff (Qx n t x) d (227/50))).filter
    (fun m => tested N (d*qs.prod*m))
private def sources (N n : ℕ) (t : ℝ) : Finset (Source N) :=
  univ.sigma fun i => ((primeTuples N .U4 i).filter (sel n t i)).sigma fun x =>
    (badLabels N (Qx n t x) (word n t i x).prod).sigma (cofs N n t i x)
private def targets (N n : ℕ) : Finset (Target N n) :=
  univ.sigma fun v => (Part3.labelledPrimeTuples (rank v) (2*N)).filter
    (fun u => tested N (Part3.labelledProduct u))

private theorem source_sum (N n : ℕ) (t : ℝ) :
    seedMass N n .U4 t (fun p w => badFibre true N (rootQ N n .U4 t p) w.prod) =
      ∑ a ∈ sources N n t,fixedWeight a.1 := by
  unfold sources seedMass
  rw [sum_sigma]
  apply sum_congr rfl
  intro i _
  rw [sum_sigma,sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases hx : sel n t i x
  · simp only [show (fun z => physicalPrime N (x z).val) ∈
        selected n .U4 t i.val.1 i.val.2 from hx,if_pos hx,if_true]
    unfold badFibre
    rw [sum_sigma,mul_sum]
    apply sum_congr rfl
    intro qs _
    unfold fibre p5z_labelledPrimeMass cofs
    simp only [if_true,sum_filter,mul_sum]
    apply sum_congr rfl
    intro m _
    split_ifs <;> simp_all [tested]
  · simp only [show ¬ (fun z => physicalPrime N (x z).val) ∈
        selected n .U4 t i.val.1 i.val.2 from hx,if_neg hx,if_false]

private theorem target_sum (N n : ℕ) (W : (v : Entry n) → Tuple N v → ℝ) :
    (∑ b ∈ targets N n,fixedWeight b.1.val.1*W b.1 b.2) =
      ∑ v : Entry n, fixedWeight v.val.1 *
        p5z_labelledPrimeMass (Part3.labelledPrimeTuples (rank v) (2*N))
          Part3.labelledProduct (W v) N := by
  unfold targets
  rw [sum_sigma]
  apply sum_congr rfl
  intro v _
  rw [sum_filter,p5z_labelledPrimeMass,mul_sum]
  apply sum_congr rfl
  intro u _
  by_cases h : tested N (Part3.labelledProduct u) <;> simp_all [tested]

private abbrev keyS {N : ℕ} (n : ℕ) (t : ℝ) (a : Source N) :=
  (a.1,word n t a.1 a.2.1,a.2.2.1,a.2.2.2)
private abbrev keyT {N n : ℕ} (b : Target N n) :=
  (b.1.val.1,tuplePrefix (k:=oldRank b.1) (r:=tailRank b.1) (tupleValues b.2),
    [tupleFresh (k:=oldRank b.1) (r:=tailRank b.1) (tupleValues b.2) 0,
     tupleFresh (k:=oldRank b.1) (r:=tailRank b.1) (tupleValues b.2) 1],
    (List.ofFn (tupleTail (k:=oldRank b.1) (r:=tailRank b.1) (tupleValues b.2))).prod)

private theorem keyS_inj (N n : ℕ) (t : ℝ) : Function.Injective (keyS (N:=N) n t) := by
  rintro ⟨i,x,q,m⟩ ⟨i',x',q',m'⟩ h
  obtain ⟨hi,hw,hq,hm⟩ : i=i' ∧ word n t i x=word n t i' x' ∧ q=q' ∧ m=m' := by
    simpa only [keyS,Prod.mk.injEq] using h
  subst i'; subst q'; subst m'
  have hx : x=x' := by
    rw [show word n t i x=coordinateOld n .U4 t ⟨i,x⟩ from rfl,
      coordinateOld_eq_ofFn,show word n t i x'=coordinateOld n .U4 t ⟨i,x'⟩ from rfl,
      coordinateOld_eq_ofFn] at hw
    have H := List.ofFn_injective hw
    funext z
    apply Fin.ext
    simpa only [Equiv.apply_symm_apply] using congrFun H ((oldSlotEquiv i.val.1).symm z)
  subst x'
  rfl

/-- Positive majorization on the same fallback Entry and the same full tuple
family as ordinary_bounded and the selected ordinary comparison. This is
the original Gamma5 badFibre true component of the purified receiver. -/
theorem tested_seed_le {N : ℕ} (n : ℕ) (t width : ℝ) (hN : 2≤N)
    (ht : 0≤t) (ht' : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hw : 0<width) (hw1 : width≤1) (hscale : scaleThreshold frozenLeafCutoffFloor≤(N:ℝ))
    (mesh : I → ℕ) :
    seedMass N n .U4 t (fun p w => badFibre true N (rootQ N n .U4 t p) w.prod) ≤
      ∑ v : Entry n, fixedWeight v.val.1 *
        p5z_labelledPrimeMass (Part3.labelledPrimeTuples (rank v) (2*N))
          Part3.labelledProduct
          (weight v (planAt mesh v) width frozenLeafCutoffFloor_pos hw hw1
            (acceptAt .U4 t mesh v) N) N := by
  let W := fun v : Entry n =>
    weight v (planAt mesh v) width frozenLeafCutoffFloor_pos hw hw1 (acceptAt .U4 t mesh v) N
  change seedMass N n .U4 t _ ≤ ∑ v : Entry n, fixedWeight v.val.1 *
    p5z_labelledPrimeMass (Part3.labelledPrimeTuples (rank v) (2*N)) Part3.labelledProduct (W v) N
  rw [source_sum,← target_sum N n W]
  let S := sources N n t
  let T := targets N n
  have lift (a : S) : ∃ b ∈ T, keyT b=keyS n t a.val ∧ 1≤W b.1 b.2 := by
    rcases a with ⟨⟨i,x,qs,m⟩,ha⟩
    obtain ⟨_,ha₁⟩ := mem_sigma.mp ha
    obtain ⟨hx,har⟩ := mem_sigma.mp ha₁
    obtain ⟨hq,hm⟩ := mem_sigma.mp har
    obtain ⟨hrough,htest⟩ := mem_filter.mp hm
    obtain ⟨hp,hsel⟩ := mem_filter.mp hx
    obtain ⟨v,u,hi,hu,_,hpre,hfresh,htail,hM,hW⟩ :=
      P2FiniteMarkedGamma5TestedSeedAtom.original_atom hN t width ht ht' hn hw hw1 hscale
        mesh i x hp hsel qs m hq hrough
    refine ⟨⟨v,u⟩,mem_sigma.mpr ⟨mem_univ _,mem_filter.mpr ⟨hu,?_⟩⟩,?_,hW⟩
    · simpa only [hM] using htest
    · have hm0 := (mem_roughNumbers.mp hrough).1
      simp only [keyT,keyS,hi,hpre,hfresh,htail,Nat.prod_primeFactorsList hm0.ne']
  choose f hf hk hwgt using lift
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply keyS_inj N n t
    exact (hk a).symm.trans ((congrArg keyT he).trans (hk b))
  let G := fun b : Target N n => fixedWeight b.1.val.1 * W b.1 b.2
  have hG (b : Target N n) : 0≤G b := by
    apply mul_nonneg (mark_nonneg _)
    unfold W weight
    apply P2FiniteMarkedGamma5AtlasFamily.atlasFamily_nonneg
  calc
    _ = ∑ a ∈ S.attach, fixedWeight a.val.1 := by simp [S]
    _ ≤ ∑ a ∈ S.attach, G (f a) := by
      apply sum_le_sum
      intro a _
      have hi := congrArg Prod.fst (hk a)
      change (f a).1.val.1=a.val.1 at hi
      change _ ≤ fixedWeight (f a).1.val.1 * W (f a).1 (f a).2
      rw [hi]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hwgt a) (mark_nonneg a.val.1)
    _ = ∑ b ∈ S.attach.image f, G b := (sum_image (fun _ _ _ _ h => hinj h)).symm
    _ ≤ ∑ b ∈ T, G b := sum_le_sum_of_subset_of_nonneg
      (fun b hb => by obtain ⟨a,_,rfl⟩ := mem_image.mp hb; exact hf a) (fun b _ _ => hG b)

end
end ImbalancedChen.P2FiniteMarkedGamma5TestedSeedMass
