import ImbalancedChen.Part3OriginalActualThreePairPolarization

/-!
Source only; uncompiled; zero formal credit.
Actual independent st=d choices, original individual gamma windows,
both product upper cutoffs, and the original physical denominator feed
the normalized non-Hermitian polarization. The carrier and first phase
are never transposed. All h signs, H<1 cases and clean gates remain in
the existing FixedBlock carrier. No spectral cancellation is asserted.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumDoubleLambdaColorWindows20261028
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalActualLambdaPairExpansion20261028
open ImbalancedChen.Part3.OriginalActualProductBoundDifferences20261028
open ImbalancedChen.Part3.OriginalActualThreePairPolarization20261102
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas

namespace ImbalancedChen.Part3.OriginalActualPolarizedProductCaller20261102

attribute [local instance] Classical.propDecidable

/-- These masks make the original one-bounded hypotheses global, without
assuming anything about gamma or alpha outside their original support. -/
def gamma2Slot (atom : MediumAtom) (s u : ℕ) : ℂ :=
  if u * s ∈ factorCarrier atom.Q2 then atom.gamma2 (u * s) else 0

def gamma3Slot (atom : MediumAtom) (t v : ℕ) : ℂ :=
  if v * t ∈ factorCarrier atom.Q3 then atom.gamma3 (v * t) else 0

def alphaSlot (atom : MediumAtom) (n : ℕ) : ℂ :=
  if n ∈ atom.alphaCarrier then atom.alpha n else 0

theorem actual_slots_one_bounded {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) :
    (∀ s u, ‖gamma2Slot atom s u‖ ≤ 1) ∧
    (∀ t v, ‖gamma3Slot atom t v‖ ≤ 1) ∧
    (∀ n, ‖alphaSlot atom n‖ ≤ 1) := by
  rcases hA with ⟨hU, hV, hQ1, hQ2, hQ3, hx, haLo, haHi,
    h1, h2, h3, h4, hα, hαrough, hβ, hγ1, hγ2, hγ3⟩
  constructor
  · intro s u
    by_cases h : u * s ∈ factorCarrier atom.Q2
    · simpa only [gamma2Slot, if_pos h] using (hγ2 _ h).1
    · simp only [gamma2Slot, if_neg h, norm_zero, zero_le_one]
  constructor
  · intro t v
    by_cases h : v * t ∈ factorCarrier atom.Q3
    · simpa only [gamma3Slot, if_pos h] using (hγ3 _ h).1
    · simp only [gamma3Slot, if_neg h, norm_zero, zero_le_one]
  · intro n
    by_cases h : n ∈ atom.alphaCarrier
    · simpa only [alphaSlot, if_pos h] using hα n h
    · simp only [alphaSlot, if_neg h, norm_zero, zero_le_one]

theorem carrier_n_support (B : FixedBlock) {t : Index} (ht : t ∈ B.carrier) :
    t.n1 ∈ B.atom.alphaCarrier ∧ t.n2 ∈ B.atom.alphaCarrier := by
  have ht' := (Finset.mem_filter.mp ht).1
  rcases Finset.mem_biUnion.mp ht' with ⟨q, hq, ht'⟩
  rcases Finset.mem_biUnion.mp ht' with ⟨w1, hw1, ht'⟩
  rcases Finset.mem_biUnion.mp ht' with ⟨w2, hw2, ht'⟩
  rcases Finset.mem_biUnion.mp ht' with ⟨n1, hn1, ht'⟩
  rcases Finset.mem_biUnion.mp ht' with ⟨n2, hn2, ht'⟩
  rcases Finset.mem_image.mp ht' with ⟨h, hh, rfl⟩
  exact ⟨hn1, hn2⟩

def productFibre (atom : MediumAtom) (z y : ℝ) (k : Key) (small w : ℕ) :
    Finset Factor :=
  (choicesWithoutProductWindow atom z y k small).filter (fun p => p.u * p.v = w)

/-- The two smooth pairs remain independent. Once p.s,p.t,p'.s,p'.t
are fixed, each polarized gamma is a function of its own rough variable
only, and the same function occurs on the left and right. -/
def actualDiagonal (atom : MediumAtom) (t : Index) (p p' : Factor)
    (e f g : Fin 4) : ℂ :=
  diagonalProduct (gamma2Slot atom p.s) (gamma2Slot atom p'.s)
    (gamma3Slot atom p.t) (gamma3Slot atom p'.t)
    (alphaSlot atom) (alphaSlot atom)
    p.u p'.u p.v p'.v t.n1 t.n2 e f g

theorem actualDiagonal_norm_le_one {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom)
    (t : Index) (p p' : Factor) (e f g : Fin 4) :
    ‖actualDiagonal atom t p p' e f g‖ ≤ 1 := by
  obtain ⟨h2, h3, hn⟩ := actual_slots_one_bounded hA
  exact diagonalProduct_norm_le_one _ _ _ _ _ _
    (h2 p.s) (h2 p'.s) (h3 p.t) (h3 p'.t) hn hn _ _ _ _ _ _ e f g

theorem actual_choice_three_pairs (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (t : Index) (p p' : Factor)
    (hp : p ∈ choicesWithoutProductWindow atom z y k small)
    (hp' : p' ∈ choicesWithoutProductWindow atom z y k small)
    (hn1 : t.n1 ∈ atom.alphaCarrier) (hn2 : t.n2 ∈ atom.alphaCarrier) (Z : ℂ) :
    (choiceCoefficient atom z k small p * star (choiceCoefficient atom z k small p') *
      atom.alpha t.n1 * star (atom.alpha t.n2)) * Z =
      ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4,
        packetWeight e f g * (actualDiagonal atom t p p' e f g * Z) := by
  rcases (Finset.mem_filter.mp hp).2 with ⟨hst, h2, h3, hsy, hty⟩
  rcases (Finset.mem_filter.mp hp').2 with ⟨hst', h2', h3', hsy', hty'⟩
  have h := three_pairs (gamma2Slot atom p.s) (gamma2Slot atom p'.s)
    (gamma3Slot atom p.t) (gamma3Slot atom p'.t)
    (alphaSlot atom) (alphaSlot atom)
    p.u p'.u p.v p'.v t.n1 t.n2 Z
  change _ = ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4,
    packetWeight e f g * (actualDiagonal atom t p p' e f g * Z) at h
  rw [gamma2Slot, if_pos h2, gamma2Slot, if_pos h2',
    gamma3Slot, if_pos h3, gamma3Slot, if_pos h3',
    alphaSlot, if_pos hn1, alphaSlot, if_pos hn2] at h
  rw [← h]
  simp only [choiceCoefficient_eq_gamma, star_mul]
  ring

/-- Bare physical kernel, with the original q*w1*w2 denominator.
The full retained weight is handled before this caller by five Abel. -/
def physicalKernel (B : FixedBlock) (t : Index) : ℂ :=
  B.firstPhase t / ((t.q * t.w1 * t.w2 : ℕ) : ℂ)

theorem norm_physicalKernel (B : FixedBlock) (t : Index) :
    ‖physicalKernel B t‖ = 1 / ((t.q * t.w1 * t.w2 : ℕ) : ℝ) := by
  have hphase : ‖B.firstPhase t‖ = 1 := by
    simp [FixedBlock.firstPhase, Complex.norm_exp, Complex.mul_re]
  simp only [physicalKernel, norm_div, hphase]
  simp

def actualUpperRectangle (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) : ℂ :=
  ∑ t ∈ B.carrier.filter R.contains,
    productUpperPayload atom z y k small t.w1 t.w2 Br Bs
      (atom.alpha t.n1 * star (atom.alpha t.n2) * physicalKernel B t)

def actualUpperPacket (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (e f g : Fin 4) : ℂ :=
  ∑ t ∈ B.carrier.filter R.contains,
    if t.w1 ≤ Br ∧ t.w2 ≤ Bs then
      ∑ p ∈ productFibre atom z y k small t.w1,
        ∑ p' ∈ productFibre atom z y k small t.w2,
          actualDiagonal atom t p p' e f g * physicalKernel B t
    else 0

/-- Explicit counting-scale norm, not a spectral-return or log-saving
bound. It retains all actual factor fibres and the physical kernel. -/
def upperKernelMass (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) : ℝ :=
  ∑ t ∈ B.carrier.filter R.contains,
    if t.w1 ≤ Br ∧ t.w2 ≤ Bs then
      ((productFibre atom z y k small t.w1).card : ℝ) *
        ((productFibre atom z y k small t.w2).card : ℝ) * ‖physicalKernel B t‖
    else 0

/-- The mass has exactly the original reciprocal denominator; there
is no extra d, M, Q or retained-phase charge in the polarization. -/
theorem upperKernelMass_eq_original_scale (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) :
    upperKernelMass B atom z y k small R Br Bs =
      ∑ t ∈ B.carrier.filter R.contains,
        if t.w1 ≤ Br ∧ t.w2 ≤ Bs then
          ((productFibre atom z y k small t.w1).card : ℝ) *
            ((productFibre atom z y k small t.w2).card : ℝ) /
              ((t.q * t.w1 * t.w2 : ℕ) : ℝ)
        else 0 := by
  simp only [upperKernelMass, norm_physicalKernel, div_eq_mul_inv, one_mul]

private theorem sum_three_comm {ι : Type*} (S : Finset ι)
    (P : ι → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    (∑ i ∈ S, ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4, P i e f g) =
      ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4, ∑ i ∈ S, P i e f g := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  rw [Finset.sum_comm]

/-- Each of the four signed upper-cutoff terms has its actual 64
diagonal source sums, with all scalar/coprimality/phase gates fixed. -/
theorem actualUpperRectangle_eq_packets (B : FixedBlock)
    (atom : MediumAtom) (hAtom : B.atom = atom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) :
    actualUpperRectangle B atom z y k small R Br Bs =
      ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4,
        packetWeight e f g * actualUpperPacket B atom z y k small R Br Bs e f g := by
  unfold actualUpperRectangle actualUpperPacket
  simp_rw [Finset.mul_sum]
  rw [← sum_three_comm]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨hn1, hn2⟩ := carrier_n_support B (Finset.mem_filter.mp ht).1
  rw [hAtom] at hn1 hn2
  by_cases hr : t.w1 ≤ Br
  · by_cases hs : t.w2 ≤ Bs
    · simp only [productUpperPayload, if_pos hr, if_pos hs, hr, hs, and_self,
        if_true, mul_one]
      change productUnrestrictedLambda atom z y k small t.w1 *
          star (productUnrestrictedLambda atom z y k small t.w2) * _ = _
      unfold productUnrestrictedLambda
      rw [star_sum, Finset.sum_mul_sum]
      simp only [Finset.sum_mul]
      change (∑ p ∈ productFibre atom z y k small t.w1,
        ∑ p' ∈ productFibre atom z y k small t.w2, _) = _
      conv_lhs =>
        arg 2
        ext p
        arg 2
        ext p'
        rw [show choiceCoefficient atom z k small p * star (choiceCoefficient atom z k small p') *
            (atom.alpha t.n1 * star (atom.alpha t.n2) * physicalKernel B t) =
          (choiceCoefficient atom z k small p * star (choiceCoefficient atom z k small p') *
            atom.alpha t.n1 * star (atom.alpha t.n2)) * physicalKernel B t by ring]
      have hrow : (∑ p ∈ productFibre atom z y k small t.w1,
          ∑ p' ∈ productFibre atom z y k small t.w2,
            (choiceCoefficient atom z k small p * star (choiceCoefficient atom z k small p') *
              atom.alpha t.n1 * star (atom.alpha t.n2)) * physicalKernel B t) =
          ∑ p ∈ productFibre atom z y k small t.w1,
            ∑ p' ∈ productFibre atom z y k small t.w2,
              ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4,
                packetWeight e f g * (actualDiagonal atom t p p' e f g * physicalKernel B t) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro p' hp'
        exact actual_choice_three_pairs atom z y k small t p p'
          (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp').1 hn1 hn2 _
      rw [hrow]
      conv_lhs =>
        arg 2
        ext p
        rw [sum_three_comm]
      rw [sum_three_comm]
      simp only [Finset.mul_sum]
    · simp [productUpperPayload, hs, hr]
  · simp [productUpperPayload, hr]

theorem actualUpperPacket_norm_le {b : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (atom : MediumAtom) (hA : MediumAdmissible b σ κ c0 atom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (e f g : Fin 4) :
    ‖actualUpperPacket B atom z y k small R Br Bs e f g‖ ≤
      upperKernelMass B atom z y k small R Br Bs := by
  unfold actualUpperPacket upperKernelMass
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro t ht
  by_cases h : t.w1 ≤ Br ∧ t.w2 ≤ Bs
  · rw [if_pos h, if_pos h]
    exact norm_double_sum_le_card_mul _ _ _ _
      (fun p hp p' hp' => actualDiagonal_norm_le_one hA t p p' e f g)
  · simp only [if_neg h, norm_zero, le_refl]

/-- Quantitative cost 64 in the unchanged original scale. The remaining
task is cancellation inside these actual diagonal sums, not an extra
coefficient/smooth-window/polarization payment hidden in a premise. -/
theorem actualUpperRectangle_norm_le {b : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (atom : MediumAtom) (hAtom : B.atom = atom)
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (Br Bs : ℕ) :
    ‖actualUpperRectangle B atom z y k small R Br Bs‖ ≤
      64 * upperKernelMass B atom z y k small R Br Bs := by
  rw [actualUpperRectangle_eq_packets B atom hAtom]
  calc
    _ ≤ ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4,
        upperKernelMass B atom z y k small R Br Bs := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e he
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro f hf
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro g hg
      rw [norm_mul, norm_packetWeight, one_mul]
      exact actualUpperPacket_norm_le B atom hA z y k small R Br Bs e f g
    _ = _ := by simp <;> ring

/-- Original caller, not a model lambda or a SourceBind assumption.
All four upper/lower combinations occur with their original signs. -/
theorem actual_rectangleSum_eq_four_upper {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (R : Rectangle) :
    let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
    B.rectangleSum R =
      actualUpperRectangle B atom z y k small R (upperProductBound k) (upperProductBound k) -
      actualUpperRectangle B atom z y k small R (lowerProductBound k) (upperProductBound k) -
      actualUpperRectangle B atom z y k small R (upperProductBound k) (lowerProductBound k) +
      actualUpperRectangle B atom z y k small R (lowerProductBound k) (lowerProductBound k) := by
  dsimp only
  let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
  change B.rectangleSum R = _
  unfold FixedBlock.rectangleSum actualUpperRectangle
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have h := actual_lambda_pair_upper_bound_difference atom z y k small t.w1 t.w2
    (atom.alpha t.n1 * star (atom.alpha t.n2) * physicalKernel B t)
  rw [← h]
  unfold FixedBlock.coeff physicalKernel
  simp only [poissonAtlasBlock_lambda, poissonAtlasBlock_atom, Complex.star_def]
  ring

/-- Direct quantitative consumer at the independently defined original
rectangleSum. The factor 64 is the polarization cost for each of the
four signed upper-cutoff sources, and each source keeps its own count.
This absolute count envelope is explicitly not the bare spectral bound. -/
theorem actual_rectangleSum_norm_le_four_kernelMass {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (R : Rectangle) :
    let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
    ‖B.rectangleSum R‖ ≤ 64 *
      (upperKernelMass B atom z y k small R (upperProductBound k) (upperProductBound k) +
       upperKernelMass B atom z y k small R (lowerProductBound k) (upperProductBound k) +
       upperKernelMass B atom z y k small R (upperProductBound k) (lowerProductBound k) +
       upperKernelMass B atom z y k small R (lowerProductBound k) (lowerProductBound k)) := by
  dsimp only
  let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
  let U := upperProductBound k
  let L := lowerProductBound k
  have hUU := actualUpperRectangle_norm_le B atom rfl hA z y k small R U U
  have hLU := actualUpperRectangle_norm_le B atom rfl hA z y k small R L U
  have hUL := actualUpperRectangle_norm_le B atom rfl hA z y k small R U L
  have hLL := actualUpperRectangle_norm_le B atom rfl hA z y k small R L L
  have hsource := actual_rectangleSum_eq_four_upper atom z y k hA Csep j small hd negative R
  change B.rectangleSum R = _ at hsource
  change ‖B.rectangleSum R‖ ≤ _
  rw [hsource]
  have htri :
      ‖actualUpperRectangle B atom z y k small R U U -
        actualUpperRectangle B atom z y k small R L U -
        actualUpperRectangle B atom z y k small R U L +
        actualUpperRectangle B atom z y k small R L L‖ ≤
      ‖actualUpperRectangle B atom z y k small R U U‖ +
        ‖actualUpperRectangle B atom z y k small R L U‖ +
        ‖actualUpperRectangle B atom z y k small R U L‖ +
        ‖actualUpperRectangle B atom z y k small R L L‖ := by
    exact (norm_add_le _ _).trans
      (add_le_add_right ((norm_sub_le _ _).trans
        (add_le_add_right (norm_sub_le _ _) _)) _)
  nlinarith

end ImbalancedChen.Part3.OriginalActualPolarizedProductCaller20261102
