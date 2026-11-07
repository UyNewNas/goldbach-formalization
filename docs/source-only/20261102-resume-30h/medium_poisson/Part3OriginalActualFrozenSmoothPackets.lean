import ImbalancedChen.Part3OriginalActualPolarizedProductCaller

/-!
Source only; uncompiled; zero formal credit.
Freeze the two independent original st=d labels before interpreting a
polarized upper-product source as a sum of diagonal coefficient packets.
No coefficient depends on the opposite rough variable, q or h. The
remaining arithmetic/product gates stay in the finite source carrier.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumDoubleLambdaColorWindows20261028
open ImbalancedChen.Part3.OriginalActualProductBoundDifferences20261028
open ImbalancedChen.Part3.OriginalActualThreePairPolarization20261102
open ImbalancedChen.Part3.OriginalActualPolarizedProductCaller20261102
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028

namespace ImbalancedChen.Part3.OriginalActualFrozenSmoothPackets20261102

attribute [local instance] Classical.propDecidable

def smoothTag (p : Factor) : ℕ × ℕ := (p.s, p.t)

/-- Actual finite labels, shared across all rough products, q,n,h. -/
def smoothLabels (atom : MediumAtom) (z y : ℝ) (k : Key) (small : ℕ) :
    Finset (ℕ × ℕ) :=
  (choicesWithoutProductWindow atom z y k small).image smoothTag

theorem mem_smoothLabels_original_data {atom : MediumAtom} {z y : ℝ}
    {k : Key} {small : ℕ} {st : ℕ × ℕ}
    (h : st ∈ smoothLabels atom z y k small) :
    st.1 * st.2 = small ∧ (st.1 : ℝ) ≤ y ∧ (st.2 : ℝ) ≤ y := by
  rcases Finset.mem_image.mp h with ⟨p, hp, rfl⟩
  rcases (Finset.mem_filter.mp hp).2 with ⟨hst, h2, h3, hsy, hty⟩
  exact ⟨hst, hsy, hty⟩

private theorem fibre_tag_mem {atom : MediumAtom} {z y : ℝ} {k : Key}
    {small w : ℕ} {p : Factor}
    (hp : p ∈ productFibre atom z y k small w) :
    smoothTag p ∈ smoothLabels atom z y k small := by
  exact Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩

private theorem sum_by_labels {ι ν : Type*} [DecidableEq ν]
    (S : Finset ι) (L : Finset ν) (tag : ι → ν)
    (htag : ∀ i ∈ S, tag i ∈ L) (f : ι → ℂ) :
    (∑ i ∈ S, f i) = ∑ a ∈ L, ∑ i ∈ S.filter (fun i => tag i = a), f i := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [htag i hi]

private theorem sum_two_labels {ι ν : Type*} (S : Finset ι) (L : Finset ν)
    (P : ι → ν → ν → ℂ) :
    (∑ i ∈ S, ∑ a ∈ L, ∑ b ∈ L, P i a b) =
      ∑ a ∈ L, ∑ b ∈ L, ∑ i ∈ S, P i a b := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]

def frozenDiagonal (atom : MediumAtom) (st st' : ℕ × ℕ)
    (t : Index) (p p' : Factor) (e f g : Fin 4) : ℂ :=
  diagonalProduct (gamma2Slot atom st.1) (gamma2Slot atom st'.1)
    (gamma3Slot atom st.2) (gamma3Slot atom st'.2)
    (alphaSlot atom) (alphaSlot atom)
    p.u p'.u p.v p'.v t.n1 t.n2 e f g

theorem frozenDiagonal_norm_le_one {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (st st' : ℕ × ℕ)
    (t : Index) (p p' : Factor) (e f g : Fin 4) :
    ‖frozenDiagonal atom st st' t p p' e f g‖ ≤ 1 := by
  obtain ⟨h2, h3, hn⟩ := actual_slots_one_bounded hA
  exact diagonalProduct_norm_le_one _ _ _ _ _ _
    (h2 st.1) (h2 st'.1) (h3 st.2) (h3 st'.2) hn hn _ _ _ _ _ _ e f g

def smoothFibre (atom : MediumAtom) (z y : ℝ) (k : Key) (small w : ℕ)
    (st : ℕ × ℕ) : Finset Factor :=
  (productFibre atom z y k small w).filter (fun p => smoothTag p = st)

def frozenUpperPacket (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4) : ℂ :=
  ∑ t ∈ B.carrier.filter R.contains,
    if t.w1 ≤ Br ∧ t.w2 ≤ Bs then
      ∑ p ∈ smoothFibre atom z y k small t.w1 st,
        ∑ p' ∈ smoothFibre atom z y k small t.w2 st',
          frozenDiagonal atom st st' t p p' e f g * physicalKernel B t
    else 0

/-- All smooth pairs are retained independently. This is a disjoint
partition of the previous actual source, not a chosen family equality. -/
theorem actualUpperPacket_eq_frozen (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (e f g : Fin 4) :
    actualUpperPacket B atom z y k small R Br Bs e f g =
      ∑ st ∈ smoothLabels atom z y k small,
        ∑ st' ∈ smoothLabels atom z y k small,
          frozenUpperPacket B atom z y k small R Br Bs st st' e f g := by
  unfold actualUpperPacket frozenUpperPacket
  rw [← sum_two_labels]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h : t.w1 ≤ Br ∧ t.w2 ≤ Bs
  · simp only [if_pos h]
    rw [sum_by_labels (productFibre atom z y k small t.w1)
      (smoothLabels atom z y k small) smoothTag (fun p hp => fibre_tag_mem hp)]
    apply Finset.sum_congr rfl
    intro st hst
    have hsplit :
        (∑ p ∈ (productFibre atom z y k small t.w1).filter (fun p => smoothTag p = st),
          ∑ p' ∈ productFibre atom z y k small t.w2,
            actualDiagonal atom t p p' e f g * physicalKernel B t) =
        ∑ p ∈ (productFibre atom z y k small t.w1).filter (fun p => smoothTag p = st),
          ∑ st' ∈ smoothLabels atom z y k small,
            ∑ p' ∈ (productFibre atom z y k small t.w2).filter (fun p' => smoothTag p' = st'),
              actualDiagonal atom t p p' e f g * physicalKernel B t := by
      apply Finset.sum_congr rfl
      intro p hp
      exact sum_by_labels _ _ smoothTag (fun p' hp' => fibre_tag_mem hp') _
    rw [hsplit, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro st' hst'
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro p' hp'
    have hpTag := (Finset.mem_filter.mp hp).2
    have hpTag' := (Finset.mem_filter.mp hp').2
    have hs : p.s = st.1 := congrArg Prod.fst hpTag
    have ht : p.t = st.2 := congrArg Prod.snd hpTag
    have hs' : p'.s = st'.1 := congrArg Prod.fst hpTag'
    have ht' : p'.t = st'.2 := congrArg Prod.snd hpTag'
    simp only [actualDiagonal, frozenDiagonal, hs, ht, hs', ht']
  · simp only [if_neg h, Finset.sum_const_zero]

/-- Each actual upper source reaches fixed-coefficient diagonal packets.
The two independent st=d sums and all 64 unit-mass weights are explicit. -/
theorem actualUpperRectangle_eq_frozen_packets (B : FixedBlock) (atom : MediumAtom)
    (hAtom : B.atom = atom) (z y : ℝ) (k : Key) (small : ℕ)
    (R : Rectangle) (Br Bs : ℕ) :
    actualUpperRectangle B atom z y k small R Br Bs =
      ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4, packetWeight e f g *
        (∑ st ∈ smoothLabels atom z y k small,
          ∑ st' ∈ smoothLabels atom z y k small,
            frozenUpperPacket B atom z y k small R Br Bs st st' e f g) := by
  rw [actualUpperRectangle_eq_packets B atom hAtom]
  simp_rw [actualUpperPacket_eq_frozen]

def frozenKernelMass (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ) : ℝ :=
  ∑ t ∈ B.carrier.filter R.contains,
    if t.w1 ≤ Br ∧ t.w2 ≤ Bs then
      ((smoothFibre atom z y k small t.w1 st).card : ℝ) *
        ((smoothFibre atom z y k small t.w2 st').card : ℝ) * ‖physicalKernel B t‖
    else 0

theorem frozenUpperPacket_norm_le {b : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (atom : MediumAtom) (hA : MediumAdmissible b σ κ c0 atom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4) :
    ‖frozenUpperPacket B atom z y k small R Br Bs st st' e f g‖ ≤
      frozenKernelMass B atom z y k small R Br Bs st st' := by
  unfold frozenUpperPacket frozenKernelMass
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro t ht
  by_cases h : t.w1 ≤ Br ∧ t.w2 ≤ Bs
  · rw [if_pos h, if_pos h]
    exact norm_double_sum_le_card_mul _ _ _ _
      (fun p hp p' hp' => frozenDiagonal_norm_le_one hA st st' t p p' e f g)
  · simp only [if_neg h, norm_zero, le_refl]

end ImbalancedChen.Part3.OriginalActualFrozenSmoothPackets20261102
