import ImbalancedChen.Part5OriginalH430W1StrictRows
import ImbalancedChen.Part5OriginalH430SelectedBankCarrierSupply

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Transfer the existing selected W1 half-open arithmetic supplier to the
production STRICT d*N-fresh singleChildren. Pay the endpoint once at the
same Q, with half of the error allowance; use the other half for the
existing bank arithmetic-to-ideal error. Positivity implies that deleting
the endpoint cannot increase row mass, so the original budget 12 is kept.
Full selected-count assignment, bank candidate/base soundness and the
441-level geometric realization are NOT supplied by this local transfer.
-/
namespace ImbalancedChen.Part5OriginalH430SelectedStrictW1Supply

noncomputable section
open Set Classical
open scoped BigOperators
open P5OriginalActionMassBound
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430SameQHistoryCells
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ImmutableBankProfiles Part5OriginalH430LiteralBankBudget
open Part5OriginalH430BankSlotTargets Part5OriginalH430SelectedBankGeometry
open Part5OriginalH430SelectedBankCarrierSupply
open Part5OriginalH430W1StrictRows

abbrev w1Family (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (i : Fin 7) (j : Fin 10) :=
  bankFamily N n mesh tau c g (slotOfAction (.inl (i,j)))

abbrev w1Theta (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (i : Fin 7) (j : Fin 10) :=
  bankTheta N n mesh tau c g sigma (slotOfAction (.inl (i,j)))

def strictPointError (N : ℕ) (Q chi : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) (g : Fin 430) : ℝ :=
  ∑ b : RowAtom,
    |strictRow N Q chi old i j b-thetaAtom N Q (parentProduct old)*idealRow (.inl (i,j)) b| *
      |oldAtomValue (precedingH g) (precedingh g) b|

theorem strictPointError_nonneg (N : ℕ) (Q chi : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) (g : Fin 430) : 0 ≤ strictPointError N Q chi old i j g :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Triangle inequality at EACH atom; cancellation is never used. -/
theorem strictPointError_le (N : ℕ) (Q chi : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) (g : Fin 430) :
    strictPointError N Q chi old i j g ≤
      rowGap N Q chi old i j (precedingH g) (precedingh g) +
      pointError N Q (physicalLevel N Q old) (parentProduct old) g (.inl (i,j)) := by
  unfold strictPointError rowGap pointError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _
  have h := abs_sub_le (strictRow N Q chi old i j b)
    (arithmeticRow N Q (physicalLevel N Q old) (parentProduct old) (.inl (i,j)) b)
    (thetaAtom N Q (parentProduct old)*idealRow (.inl (i,j)) b)
  rw [abs_sub_comm (strictRow N Q chi old i j b)
    (arithmeticRow N Q (physicalLevel N Q old) (parentProduct old) (.inl (i,j)) b)] at h
  simpa only [add_mul] using
    mul_le_mul_of_nonneg_right h (abs_nonneg (oldAtomValue (precedingH g) (precedingh g) b))

def w1StrictError (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (i : Fin 7) (j : Fin 10) : ℝ :=
  ∑ h ∈ w1Family N n mesh tau c g i j, sigma h *
    strictPointError N (cellQ N n c) (labelNode n tau h).physical.ceiling (labelWord h) i j (g h)

def w1StrictRow (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (i : Fin 7) (j : Fin 10)
    (b : RowAtom) : ℝ :=
  ∑ h ∈ w1Family N n mesh tau c g i j, sigma h *
    strictRow N (cellQ N n c) (labelNode n tau h).physical.ceiling (labelWord h) i j b

/-- Every formerly explicit W1 ceiling premise is deduced from its actual
selected slot. The catalog's source-binding limitations are unchanged. -/
theorem uniform_selected_strictW1 {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ c : RootCode n, ∀ g : Label N mesh → Fin 430,
      ∀ sigma : Label N mesh → ℝ, ∀ i : Fin 7, ∀ j : Fin 10,
      (∀ h ∈ w1Family N n mesh tau c g i j, 0 ≤ sigma h) →
      w1StrictError N n mesh tau c g sigma i j ≤ epsilon*w1Theta N n mesh tau c g sigma i j ∧
      (∀ b, 0 ≤ w1StrictRow N n mesh tau c g sigma i j b) ∧
      (∑ b : RowAtom, w1StrictRow N n mesh tau c g sigma i j b) ≤
        12*w1Theta N n mesh tau c g sigma i j ∧
      (w1Theta N n mesh tau c g sigma i j = 0 →
        w1StrictError N n mesh tau c g sigma i j = 0 ∧
        ∀ b, w1StrictRow N n mesh tau c g sigma i j b = 0) := by
  obtain ⟨Tr,hTr⟩ := uniform_selected_bank_carriers (by positivity : (0:ℝ) < epsilon/2)
  obtain ⟨Te,hTe⟩ := uniform_rowGap frozenResidualFloor_pos (by positivity : (0:ℝ) < epsilon/2)
  refine ⟨max 4 (max Tr Te),?_⟩
  intro N hN n mesh tau ht ht' hn c g sigma i j hsigma
  let S := w1Family N n mesh tau c g i j
  let Q := cellQ N n c
  let k := slotOfAction (.inl (i,j))
  have hN4 : 4 ≤ N := by omega
  have hN1 : 1 < N := by omega
  have hf (h : Label N mesh) (hh : h ∈ S) :=
    cell_history_support hN1 ht ht' hn (mem_bankFamily.mp hh).1
  have hceil (h : Label N mesh) (hh : h ∈ S) :
      physicalLevel N Q (labelWord h)/W1Target i ≤ (labelNode n tau h).physical.ceiling := by
    have hh' := (selected_parent_tests hN1 ht ht' hn hh).2.2
    simpa only [action_slot,actionTarget,(hf h hh).2.1] using hh'
  have hraw := hTr N (by omega) n mesh tau ht ht' hn c g sigma k hsigma
  have hgap (h : Label N mesh) (hh : h ∈ S) :
      rowGap N Q (labelNode n tau h).physical.ceiling (labelWord h) i j
        (precedingH (g h)) (precedingh (g h)) ≤ (epsilon/2)*thetaAtom N Q (labelPrefix h) :=
    (hTe N (by omega)).2 Q _ (labelWord h) i j (hf h hh).1 (hf h hh).2.2.1 (hceil h hh) (g h)
  have hgapSum : (∑ h ∈ S, sigma h * rowGap N Q (labelNode n tau h).physical.ceiling
      (labelWord h) i j (precedingH (g h)) (precedingh (g h))) ≤
      (epsilon/2)*w1Theta N n mesh tau c g sigma i j := by
    calc
      _ ≤ ∑ h ∈ S, sigma h*((epsilon/2)*thetaAtom N Q (labelPrefix h)) :=
        Finset.sum_le_sum (fun h hh => mul_le_mul_of_nonneg_left (hgap h hh) (hsigma h hh))
      _ = _ := by
        change _ = (epsilon/2)*parentTheta N Q S labelPrefix sigma
        rw [parentTheta,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        ring
  have herr : w1StrictError N n mesh tau c g sigma i j ≤
      epsilon*w1Theta N n mesh tau c g sigma i j := by
    have hcmp : w1StrictError N n mesh tau c g sigma i j ≤
        (∑ h ∈ S, sigma h * rowGap N Q (labelNode n tau h).physical.ceiling
          (labelWord h) i j (precedingH (g h)) (precedingh (g h))) +
        bankError N n mesh tau c g sigma k := by
      change (∑ h ∈ S, _) ≤ _ + ∑ h ∈ S, _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro h hh
      have hp := mul_le_mul_of_nonneg_left
        (strictPointError_le N Q (labelNode n tau h).physical.ceiling (labelWord h) i j (g h))
        (hsigma h hh)
      simpa only [k,action_slot,mul_add,labelResidual,labelPrefix] using hp
    have hr := hraw.1
    change bankError N n mesh tau c g sigma k ≤ (epsilon/2)*w1Theta N n mesh tau c g sigma i j at hr
    linarith
  have hrow (b : RowAtom) :
      0 ≤ w1StrictRow N n mesh tau c g sigma i j b ∧
      w1StrictRow N n mesh tau c g sigma i j b ≤ bankRow N n mesh tau c g sigma k b := by
    have hb (h : Label N mesh) (hh : h ∈ S) :=
      strictRow_bounds hN4 (hf h hh).1 (labelResidual n c h) i j (hceil h hh) b
    constructor
    · exact Finset.sum_nonneg (fun h hh => mul_nonneg (hsigma h hh) (hb h hh).1)
    · change (∑ h ∈ S, _) ≤ ∑ h ∈ S, _
      apply Finset.sum_le_sum
      intro h hh
      simpa only [k,action_slot,labelPrefix] using
        mul_le_mul_of_nonneg_left (hb h hh).2 (hsigma h hh)
  have hmass : (∑ b : RowAtom, w1StrictRow N n mesh tau c g sigma i j b) ≤
      12*w1Theta N n mesh tau c g sigma i j :=
    (Finset.sum_le_sum (fun b _ => (hrow b).2)).trans hraw.2.2.2.1
  refine ⟨herr,fun b => (hrow b).1,hmass,?_⟩
  intro hz
  constructor
  · apply le_antisymm (by simpa only [hz,mul_zero] using herr)
    exact Finset.sum_nonneg (fun h hh => mul_nonneg (hsigma h hh) (strictPointError_nonneg _ _ _ _ _ _ _))
  · intro b
    have hb : w1StrictRow N n mesh tau c g sigma i j b ≤
        ∑ a : RowAtom, w1StrictRow N n mesh tau c g sigma i j a :=
      Finset.single_le_sum (fun a _ => (hrow a).1) (Finset.mem_univ b)
    apply le_antisymm ((hb.trans hmass).trans_eq (by rw [hz,mul_zero])) (hrow b).1

/-- A signed old-table application is bounded AFTER the absolute coefficient
estimate, so it cannot exploit cancellation between histories or atoms. -/
theorem strict_profile_error_le (N : ℕ) (Q chi : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) (g : Fin 430) :
    |(∑ b : RowAtom, strictRow N Q chi old i j b*oldAtomValue (precedingH g) (precedingh g) b) -
      thetaAtom N Q (parentProduct old)*idealProfile (precedingH g) (precedingh g) (.inl (i,j))| ≤
      strictPointError N Q chi old i j g := by
  rw [← Part5OriginalH430LiteralBankBudget.idealRow_value,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_assoc,← sub_mul,abs_mul]

def w1AppliedError (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (i : Fin 7) (j : Fin 10) : ℝ :=
  ∑ h ∈ w1Family N n mesh tau c g i j, sigma h *
    |(∑ b : RowAtom, strictRow N (cellQ N n c) (labelNode n tau h).physical.ceiling
        (labelWord h) i j b*oldAtomValue (precedingH (g h)) (precedingh (g h)) b) -
      thetaAtom N (cellQ N n c) (labelPrefix h)*
        idealProfile (precedingH (g h)) (precedingh (g h)) (.inl (i,j))|

theorem w1AppliedError_le {N n mesh : ℕ} (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (i : Fin 7) (j : Fin 10)
    (hs : ∀ h ∈ w1Family N n mesh tau c g i j, 0 ≤ sigma h) :
    w1AppliedError N n mesh tau c g sigma i j ≤ w1StrictError N n mesh tau c g sigma i j := by
  apply Finset.sum_le_sum
  intro h hh
  exact mul_le_mul_of_nonneg_left (strict_profile_error_le _ _ _ _ _ _ _) (hs h hh)

theorem uniform_selected_strictW1_applied {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ c : RootCode n, ∀ g : Label N mesh → Fin 430,
      ∀ sigma : Label N mesh → ℝ, ∀ i : Fin 7, ∀ j : Fin 10,
      (∀ h ∈ w1Family N n mesh tau c g i j, 0 ≤ sigma h) →
      w1AppliedError N n mesh tau c g sigma i j ≤ epsilon*w1Theta N n mesh tau c g sigma i j := by
  obtain ⟨T,hT⟩ := uniform_selected_strictW1 he
  refine ⟨T,?_⟩
  intro N hN n mesh tau ht ht' hn c g sigma i j hs
  exact (w1AppliedError_le tau c g sigma i j hs).trans
    (hT N hN n mesh tau ht ht' hn c g sigma i j hs).1

/-- Finite outer aggregation: each root cell keeps its OWN Q. The right
side includes only selected W1 slots, not all bank alternatives. -/
theorem uniform_selected_outer_strictW1 {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ g : Label N mesh → Fin 430, ∀ sigma : Label N mesh → ℝ,
      (∀ h ∈ readyCatalog N n mesh tau, 0 ≤ sigma h) →
      (∑ c : RootCode n, ∑ ij : Fin 7 × Fin 10,
        w1StrictError N n mesh tau c g sigma ij.1 ij.2) ≤
      epsilon*(∑ c : RootCode n, ∑ ij : Fin 7 × Fin 10,
        w1Theta N n mesh tau c g sigma ij.1 ij.2) := by
  obtain ⟨T,hT⟩ := uniform_selected_strictW1 he
  refine ⟨T,?_⟩
  intro N hN n mesh tau ht ht' hn g sigma hsigma
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ij _
  exact (hT N hN n mesh tau ht ht' hn c g sigma ij.1 ij.2
    (fun h hh => hsigma h (Finset.mem_filter.mp (mem_bankFamily.mp hh).1).1)).1

end
end ImbalancedChen.Part5OriginalH430SelectedStrictW1Supply
