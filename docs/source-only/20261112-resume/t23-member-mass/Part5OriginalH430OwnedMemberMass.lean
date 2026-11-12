import ImbalancedChen.Part5OriginalH430OwnedRootCounts
import ImbalancedChen.Part5OriginalH430SelectedBankCarrierSupply
import ImbalancedChen.Part5OriginalH430RealizedBuchstabSupply

/-! Source candidate.  One actual RootKey, all geometric integer Members
over its original prime fibre, and one choice of row per parent.  An inactive
lower Buchstab transition has no coefficient payment; its parent's weight
is still present. No sum of alternative actions or comparison of counts. -/
namespace ImbalancedChen.Part5OriginalH430OwnedMemberMass
noncomputable section
open Set
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers
open P2EnhancedLowerPrimeChildGeometry P2OriginalChildPhysicalNormalization
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430SameQHistoryCells
open Part5OriginalH430OwnedRootCounts Part5OriginalH430IntegerItineraries
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430LiteralAbsoluteBudget Part5OriginalH430LiteralBankBudget
open Part5OriginalH430ArithmeticAtomRows Part5OriginalH430BuchstabPhysicalBudget
open Part5OriginalBuchstabImmutable430Budget Part5OriginalBuchstabActualRowLimits
open Part5OriginalH430SelectedBankCarrierSupply
open P5OriginalActionMassBound

def ownedMembers (N n m mesh : ℕ) (k : Root) (tau : ℝ) (c : RootKey n m) :
    Finset (Label N mesh) :=
  (catalog N n mesh tau).filter
    (fun h => h.2.1 = k ∧ h.2.2.1.val ∈ rootFibre N n m k tau c)

theorem mem_ownedMembers {N n m mesh : ℕ} {k : Root} {tau : ℝ}
    {c : RootKey n m} {h : Label N mesh} :
    h ∈ ownedMembers N n m mesh k tau c ↔
      Valid n tau h ∧ h.2.1 = k ∧ h.2.2.1.val ∈ rootFibre N n m k tau c := by
  simp only [ownedMembers, Finset.mem_filter, mem_catalog]

private theorem step_le {p : PhysicalNode} {s : StepShape} {z : Point}
    (hz : LocalDomain p s z) : residual (perform p s z) ≤ residual p := by
  cases s with
  | retain => exact le_rfl
  | transport i => exact le_rfl
  | w1Fixed i j => exact le_rfl
  | w2Fixed i b => exact le_rfl
  | buchstabUpper | w1Singleton _ _ | w2Singleton _ _ =>
    dsimp only [perform]
    rw [residual_appendOne]
    linarith only [hz.2.1.1]
  | buchstabLower =>
    dsimp only [perform]
    rw [residual_appendOne]
    linarith only [hz.2.2.1.1]
  | w2Pair _ _ =>
    dsimp only [perform]
    rw [residual_appendPair]
    linarith only [hz.2.1.1, hz.2.1.2.1]

theorem member_residual_le_root {lo hi : ℝ} {mesh depth : ℕ} {p : TypedNode}
    {code : Program mesh depth} {z : Coordinates depth} (hz : Member lo hi depth p code z) :
    residual (realize depth p code z).physical ≤ residual p.physical := by
  induction depth generalizing p with
  | zero => exact le_rfl
  | succ depth ih =>
    exact (ih hz.2.2.2).trans (step_le hz.2.2.1)

abbrev Lkey {N n m mesh : ℕ} (c : RootKey n m) (h : Label N mesh) : ℝ :=
  physicalLevel N (cellQ N n c.1) (labelWord h)

/-- The same original owner gives Q at every full Member. No parent
direction guard, owner/compactness hypothesis, or winning-source test. -/
theorem owned_support {N n m mesh : ℕ} {k : Root} {tau : ℝ} {c : RootKey n m}
    {h : Label N mesh} (hN : 2 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1 / ((n:ℝ)+1) ≤ 11/384) (hh : h ∈ ownedMembers N n m mesh k tau c) :
    let p := (labelNode n tau h).physical
    let Q := cellQ N n c.1
    parentWindow N Q (labelWord h) p.ceiling ∧ residual p = Lkey c h ∧
      Lkey c h ∈ Icc frozenResidualFloor (1/2 : ℝ) ∧ p.argument ∈ Icc (1:ℝ) 6 ∧
      2 ≤ P2OriginalChildPhysicalNormalization.alpha
        (Real.log (labelPrefix h : ℝ)/Real.log (N:ℝ)) (Lkey c h) ∧
      Q = (labelPrefix h : ℝ)*(N:ℝ)^(Lkey c h) := by
  obtain ⟨v, hk, hf⟩ := mem_ownedMembers.mp hh
  subst k
  have hQ := (original_fibre_geometry hN ht ht' hn hf).1
  have hs := history_support (by omega : 1 < N) ht ht' hn
    (show h.1.val ≤ 440 by omega) v.1 v.2.1 v.2.2.1 v.2.2.2.2
  dsimp only at hs ⊢
  have hu := (member_residual_le_root v.2.2.2.2).trans
    (frozenRoot_residual_bounds ht ht' v.2.1 hn).2
  unfold Lkey
  rw [hQ]
  exact ⟨hs.1,hs.2.1,⟨hs.2.2.1,hs.2.1 ▸ hu⟩,hs.2.2.2⟩

/-- Sum type selects one candidate, with its original polarity on a
Buchstab step; a bank row here is its arithmetic carrier, not its base. -/
abbrev NextRow := Original106Action ⊕ Unit

def rowError {N n m mesh : ℕ} (tau : ℝ) (c : RootKey n m) (g : Fin 430)
    (h : Label N mesh) : NextRow → ℝ
  | .inl a => pointError N (cellQ N n c.1) (Lkey c h) (labelPrefix h) g a
  | .inr _ =>
    let p := labelNode n tau h
    if directionGuard p.upper p.physical then
      strictAbsoluteError p.upper N (cellQ N n c.1) p.physical.ceiling
        (labelWord h) p.physical (precedingH g) (precedingh g)
    else 0

theorem rowError_nonneg {N n m mesh : ℕ} (tau : ℝ) (c : RootKey n m) (g : Fin 430)
    (h : Label N mesh) (a : NextRow) : 0 ≤ rowError tau c g h a := by
  cases a with
  | inl a => exact pointError_nonneg _ _ _ _ _ _
  | inr u =>
    dsimp only [rowError]
    split_ifs
    · exact strictAbsoluteError_nonneg _ _ _ _ _ _ _ _
    · exact le_rfl

def ownedError {N n m mesh : ℕ} (k : Root) (tau : ℝ) (c : RootKey n m)
    (g : Label N mesh → Fin 430) (next : Label N mesh → NextRow)
    (mark : Label N mesh → ℝ) : ℝ :=
  ∑ h ∈ ownedMembers N n m mesh k tau c, mark h * rowError tau c (g h) h (next h)

def ownedTheta {N n m mesh : ℕ} (k : Root) (tau : ℝ) (c : RootKey n m)
    (mark : Label N mesh → ℝ) : ℝ :=
  parentTheta N (cellQ N n c.1) (ownedMembers N n m mesh k tau c) labelPrefix mark

/-- Absolute coefficient errors before summation over parent labels and
old-array atoms.  Marks may select a stratum at the *parent*; no assertion
here filters new child terms inside a signed arithmetic row. -/
theorem uniform_owned_member_rows {eps : ℝ} (he : 0 < eps) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n m mesh : ℕ, ∀ k : Root, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1 / ((n:ℝ)+1) ≤ 11/384 → ∀ c : RootKey n m,
      ∀ g : Label N mesh → Fin 430, ∀ next : Label N mesh → NextRow,
      ∀ mark : Label N mesh → ℝ, (∀ h ∈ ownedMembers N n m mesh k tau c, 0 ≤ mark h) →
      ownedError k tau c g next mark ≤ eps * ownedTheta k tau c mark ∧
      (ownedTheta k tau c mark = 0 → ownedError k tau c g next mark = 0) := by
  let hi : ℝ := max frozenResidualFloor (1/2)
  have hf := Part5OriginalH430FrozenIntegerSupport.frozenResidualFloor_pos
  obtain ⟨Tb,hb⟩ := immutable430_literal_absoluteCoefficientError hf
    (le_max_left frozenResidualFloor (1/2:ℝ)) he
  obtain ⟨Tu,hu⟩ := immutable430_uniform_buchstab_rows hf he
  refine ⟨max 4 (max Tb Tu), ?_⟩
  intro N hN n m mesh k tau ht ht' hn c g next mark hm
  let S := ownedMembers N n m mesh k tau c
  let Q := cellQ N n c.1
  have hp (h : Label N mesh) (hh : h ∈ S) :
      rowError tau c (g h) h (next h) ≤ eps * thetaAtom N Q (labelPrefix h) := by
    have s := owned_support (by omega : 2 ≤ N) ht ht' hn hh
    dsimp only at s
    have htheta := P2OriginalPositiveSameQMassLift.thetaAtom_nonneg
      (by omega : 4 ≤ N) s.1.2.1 (parentWindow_logs s.1).2.1
    cases ha : next h with
    | inl a =>
      have hsL : Lkey c h ∈ Icc frozenResidualFloor hi :=
        ⟨s.2.2.1.1,s.2.2.1.2.trans (le_max_right _ _)⟩
      have b := hb N (by omega) (g h) Q ({()} : Finset Unit)
        (fun _ => Lkey c h) (fun _ => labelPrefix h) (fun _ => (1:ℝ))
        (fun _ _ => hsL) (fun _ _ => s.1.2.1) (fun _ _ => s.2.2.2.2.2)
        (fun _ _ => zero_le_one) (fun _ _ => s.2.2.2.2.1) a
      simpa only [rowError, pointError, absoluteCoefficientError, parentRow, parentTheta,
        Finset.sum_singleton, one_mul] using b
    | inr u =>
      dsimp only [rowError]
      split_ifs with hg
      · let p := labelNode n tau h
        have b := hu N (by omega) Q ({()} : Finset Unit) (fun _ => labelWord h)
          (fun _ => p.physical) (fun _ => p.physical.ceiling) (fun _ => (1:ℝ))
          (fun _ => p.upper) (fun _ => g h) (fun _ _ => s.1) (fun _ _ => s.2.1)
          (fun _ _ => rfl) (fun _ _ => s.2.2.2.1.1) (fun _ _ => hg)
          (fun _ _ => zero_le_one) (fun _ _ => s.2.2.1.1)
        simpa only [parentTheta, Finset.sum_singleton, one_mul] using b
      · exact mul_nonneg he.le htheta
  have herr : ownedError k tau c g next mark ≤ eps * ownedTheta k tau c mark := by
    unfold ownedError ownedTheta parentTheta
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun h hh => (mul_le_mul_of_nonneg_left (hp h hh) (hm h hh)).trans_eq
      (by ring))
  refine ⟨herr,fun hz => le_antisymm (by simpa only [hz,mul_zero] using herr) ?_⟩
  exact Finset.sum_nonneg (fun h hh => mul_nonneg (hm h hh) (rowError_nonneg _ _ _ _ _))

/-- Finite outer sum over the two original labels and *all* original
root keys; the Q is still computed separately inside each key. -/
theorem uniform_outer_owned_error {eps : ℝ} (he : 0 < eps) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n m mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ g : Label N mesh → Fin 430, ∀ next : Label N mesh → NextRow,
      ∀ mark : Label N mesh → ℝ, (∀ h, 0 ≤ mark h) →
      (∑ k : Root, ∑ c : RootKey n m, ownedError k tau c g next mark) ≤
        eps * ∑ k : Root, ∑ c : RootKey n m, ownedTheta k tau c mark := by
  obtain ⟨T,hT⟩ := uniform_owned_member_rows he
  refine ⟨T,?_⟩
  intro N hN n m mesh tau ht ht' hn g next mark hm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun c _ =>
    (hT N hN n m mesh k tau ht ht' hn c g next mark (fun h _ => hm h)).1)

end
end ImbalancedChen.Part5OriginalH430OwnedMemberMass
