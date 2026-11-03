import ImbalancedChen.Part5OriginalH430SelectedBankGeometry
import ImbalancedChen.Part5OriginalH430LiteralAbsoluteBudget
import ImbalancedChen.Part5OriginalBuchstabActualRowLimits

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Instantiate the existing genuine 106-bank arithmetic coefficients on
selected original frozen-root Member families. Absolute values are taken
at EACH PARENT and EACH ATOM before summation. Equal products keep their
history labels. The W2 arithmetic carrier retains original N-window repeats;
it is not identified with the strict fresh children of the geometry file.
The numerical candidate/base/quadrature licence is not asserted here.
-/
namespace ImbalancedChen.Part5OriginalH430SelectedBankCarrierSupply

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430SameQHistoryCells Part5OriginalBuchstabActualRowLimits
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ImmutableBankProfiles Part5OriginalH430LiteralBankBudget
open Part5OriginalH430LiteralAbsoluteBudget
open Part5OriginalH430BankSlotTargets Part5OriginalH430SelectedBankGeometry

def pointError (N : ℕ) (Q L : ℝ) (d : ℕ) (g : Fin 430) (a : Original106Action) : ℝ :=
  ∑ b : RowAtom, |arithmeticRow N Q L d a b - thetaAtom N Q d*idealRow a b| *
    |oldAtomValue (precedingH g) (precedingh g) b|

theorem pointError_nonneg (N : ℕ) (Q L : ℝ) (d : ℕ) (g : Fin 430)
    (a : Original106Action) : 0 ≤ pointError N Q L d g a :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- The signed applied-profile estimate is a CONSEQUENCE of absolute
coefficient control, never the justification for that stronger control. -/
theorem point_profile_error_le (N : ℕ) (Q L : ℝ) (d : ℕ) (g : Fin 430)
    (a : Original106Action) :
    |arithmeticProfile N Q L d (precedingH g) (precedingh g) a -
      thetaAtom N Q d*idealProfile (precedingH g) (precedingh g) a| ≤
      pointError N Q L d g a := by
  rw [← arithmeticRow_value, ← Part5OriginalH430LiteralBankBudget.idealRow_value,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro b _
  have he : arithmeticRow N Q L d a b*oldAtomValue (precedingH g) (precedingh g) b -
      thetaAtom N Q d*(idealRow a b*oldAtomValue (precedingH g) (precedingh g) b) =
      (arithmeticRow N Q L d a b-thetaAtom N Q d*idealRow a b)*
        oldAtomValue (precedingH g) (precedingh g) b := by ring
  rw [he, abs_mul]

abbrev labelPrefix {N mesh : ℕ} (h : Label N mesh) : ℕ := parentProduct (labelWord h)
def labelResidual {N mesh : ℕ} (n : ℕ) (c : RootCode n) (h : Label N mesh) : ℝ :=
  physicalLevel N (cellQ N n c) (labelWord h)

def bankTheta (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (k : Fin 106) : ℝ :=
  parentTheta N (cellQ N n c) (bankFamily N n mesh tau c g k) labelPrefix sigma

def bankError (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (k : Fin 106) : ℝ :=
  ∑ h ∈ bankFamily N n mesh tau c g k, sigma h *
    pointError N (cellQ N n c) (labelResidual n c h) (labelPrefix h) (g h) (actionOfSlot k)

def bankRow (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (k : Fin 106) (b : RowAtom) : ℝ :=
  parentRow N (cellQ N n c) (bankFamily N n mesh tau c g k)
    (labelResidual n c) labelPrefix sigma (fun _ => actionOfSlot k) b

def bankAppliedError (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (k : Fin 106) : ℝ :=
  ∑ h ∈ bankFamily N n mesh tau c g k, sigma h *
    |arithmeticProfile N (cellQ N n c) (labelResidual n c h) (labelPrefix h)
      (precedingH (g h)) (precedingh (g h)) (actionOfSlot k) -
      thetaAtom N (cellQ N n c) (labelPrefix h)*
        idealProfile (precedingH (g h)) (precedingh (g h)) (actionOfSlot k)|

theorem bankAppliedError_le {N n mesh : ℕ} (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (k : Fin 106)
    (hs : ∀ h ∈ bankFamily N n mesh tau c g k, 0 ≤ sigma h) :
    bankAppliedError N n mesh tau c g sigma k ≤ bankError N n mesh tau c g sigma k := by
  apply Finset.sum_le_sum
  intro h hh
  exact mul_le_mul_of_nonneg_left (point_profile_error_le _ _ _ _ _ _) (hs h hh)

/-- No unknown residual floor, common Q or arbitrary physical action is
an input here. The only scalar-generation assignments still explicit are
g; deriving them from the FULL original count source remains separate. -/
theorem uniform_selected_bank_carriers {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ c : RootCode n, ∀ g : Label N mesh → Fin 430,
      ∀ sigma : Label N mesh → ℝ, ∀ k : Fin 106,
      (∀ h ∈ bankFamily N n mesh tau c g k, 0 ≤ sigma h) →
      bankError N n mesh tau c g sigma k ≤ epsilon*bankTheta N n mesh tau c g sigma k ∧
      bankAppliedError N n mesh tau c g sigma k ≤ epsilon*bankTheta N n mesh tau c g sigma k ∧
      (∀ b, 0 ≤ bankRow N n mesh tau c g sigma k b) ∧
      (∑ b : RowAtom, bankRow N n mesh tau c g sigma k b) ≤
        12*bankTheta N n mesh tau c g sigma k ∧
      (bankTheta N n mesh tau c g sigma k = 0 →
        bankError N n mesh tau c g sigma k = 0 ∧
        ∀ b, bankRow N n mesh tau c g sigma k b = 0) := by
  let Lmax := max frozenResidualFloor 1
  obtain ⟨Te,hTe⟩ := immutable430_literal_absoluteCoefficientError (Lmax := Lmax)
    frozenResidualFloor_pos (le_max_left _ _) he
  obtain ⟨Tm,hTm⟩ := all106_normalized_parent_rows
    frozenResidualFloor_pos (show frozenResidualFloor ≤ Lmax from le_max_left _ _)
  refine ⟨max 4 (max Te Tm), ?_⟩
  intro N hN n mesh tau ht ht' hn c g sigma k hsigma
  let S := bankFamily N n mesh tau c g k
  let Q := cellQ N n c
  let L := labelResidual n c
  let d : Label N mesh → ℕ := labelPrefix
  let a : Label N mesh → Original106Action := fun _ => actionOfSlot k
  have hN4 : 4 ≤ N := by omega
  have hN1 : 1 < N := by omega
  have hf (h : Label N mesh) (hh : h ∈ S) :=
    cell_history_support hN1 ht ht' hn (mem_bankFamily.mp hh).1
  have hL (h : Label N mesh) (hh : h ∈ S) : L h ∈ Icc frozenResidualFloor Lmax :=
    ⟨(hf h hh).2.2.1, (parent_level_le_one (hf h hh).1).trans (le_max_right _ _)⟩
  have hd (h : Label N mesh) (hh : h ∈ S) : 0 < d h := (hf h hh).1.2.1
  have hQ (h : Label N mesh) (hh : h ∈ S) : Q = (d h:ℝ)*(N:ℝ)^(L h) :=
    (hf h hh).2.2.2.2.2
  have hA (h : Label N mesh) (hh : h ∈ S) :
      2 ≤ P2OriginalChildPhysicalNormalization.alpha
        (Real.log (d h:ℝ)/Real.log (N:ℝ)) (L h) := (hf h hh).2.2.2.2.1
  have hR (h : Label N mesh) (hh : h ∈ S) : 1 < Q/(d h:ℝ) :=
    sameQ_residual_gt_one hN1 (hd h hh) (frozenResidualFloor_pos.trans_le (hL h hh).1) (hQ h hh)
  have htheta : 0 ≤ parentTheta N Q S d sigma :=
    parentTheta_nonneg hN4 Q S d sigma hd hsigma hR
  have herrPoint (h : Label N mesh) (hh : h ∈ S) :
      pointError N Q (L h) (d h) (g h) (actionOfSlot k) ≤ epsilon*thetaAtom N Q (d h) := by
    have hx := hTe N (by omega) (g h) Q ({()} : Finset Unit)
      (fun _ => L h) (fun _ => d h) (fun _ => (1:ℝ))
      (fun _ _ => hL h hh) (fun _ _ => hd h hh) (fun _ _ => hQ h hh)
      (fun _ _ => zero_le_one) (fun _ _ => hA h hh) (actionOfSlot k)
    simpa only [absoluteCoefficientError, parentRow, parentTheta,
      Finset.sum_singleton, one_mul, pointError] using hx
  have herr : bankError N n mesh tau c g sigma k ≤
      epsilon*bankTheta N n mesh tau c g sigma k := by
    change (∑ h ∈ S, sigma h*pointError N Q (L h) (d h) (g h) (actionOfSlot k)) ≤
      epsilon*parentTheta N Q S d sigma
    calc
      _ ≤ ∑ h ∈ S, sigma h*(epsilon*thetaAtom N Q (d h)) :=
        Finset.sum_le_sum (fun h hh => mul_le_mul_of_nonneg_left (herrPoint h hh) (hsigma h hh))
      _ = _ := by simp only [parentTheta, Finset.mul_sum]; apply Finset.sum_congr rfl; intro h _; ring
  have hm := hTm N (by omega) Q S L d sigma a hL hd hQ hsigma hA
  have hrow (b : RowAtom) : parentRow N Q S L d sigma a b =
      normalizedParentRow N Q S L d sigma a b * parentTheta N Q S d sigma := by
    by_cases hz : parentTheta N Q S d sigma = 0
    · rw [hm.2.2 hz b, hz, mul_zero]
    · exact (div_mul_cancel₀ _ hz).symm
  have hnonneg (b : RowAtom) : 0 ≤ bankRow N n mesh tau c g sigma k b := by
    change 0 ≤ parentRow N Q S L d sigma a b
    rw [hrow]
    exact mul_nonneg (hm.1 b) htheta
  have hmass : (∑ b : RowAtom, bankRow N n mesh tau c g sigma k b) ≤
      12*bankTheta N n mesh tau c g sigma k := by
    change (∑ b : RowAtom, parentRow N Q S L d sigma a b) ≤ 12*parentTheta N Q S d sigma
    simp_rw [hrow]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hm.2.1 htheta
  refine ⟨herr, (bankAppliedError_le tau c g sigma k hsigma).trans herr, hnonneg, hmass, ?_⟩
  intro hz
  refine ⟨?_, hm.2.2 hz⟩
  apply le_antisymm (by simpa only [hz,mul_zero] using herr)
  exact Finset.sum_nonneg (fun h hh => mul_nonneg (hsigma h hh) (pointError_nonneg _ _ _ _ _ _))

/-- Each cell keeps its original Q. Alternatives partition by their
unique selected slot; equal-product histories remain distinct. -/
def totalBankTheta (N n mesh : ℕ) (tau : ℝ)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) : ℝ :=
  ∑ c : RootCode n, parentTheta N (cellQ N n c) (bankUnion N n mesh tau c g) labelPrefix sigma

theorem sum_bankTheta (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) :
    (∑ k : Fin 106, bankTheta N n mesh tau c g sigma k) =
      parentTheta N (cellQ N n c) (bankUnion N n mesh tau c g) labelPrefix sigma := by
  unfold bankTheta parentTheta
  exact sum_bankFamily N n mesh tau c g _

theorem uniform_selected_outer_bank_error {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ g : Label N mesh → Fin 430, ∀ sigma : Label N mesh → ℝ,
      (∀ h ∈ readyCatalog N n mesh tau, 0 ≤ sigma h) →
      (∑ c : RootCode n, ∑ k : Fin 106, bankError N n mesh tau c g sigma k) ≤
        epsilon*totalBankTheta N n mesh tau g sigma := by
  obtain ⟨T,hT⟩ := uniform_selected_bank_carriers he
  refine ⟨T, ?_⟩
  intro N hN n mesh tau ht ht' hn g sigma hsigma
  have hs (c : RootCode n) (k : Fin 106) (h : Label N mesh)
      (hh : h ∈ bankFamily N n mesh tau c g k) : 0 ≤ sigma h :=
    hsigma h (Finset.mem_filter.mp (mem_bankFamily.mp hh).1).1
  calc
    _ ≤ ∑ c : RootCode n, ∑ k : Fin 106, epsilon*bankTheta N n mesh tau c g sigma k := by
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro k _
      exact (hT N hN n mesh tau ht ht' hn c g sigma k (hs c k)).1
    _ = _ := by
      simp_rw [← Finset.mul_sum, sum_bankTheta]
      rfl

end
end ImbalancedChen.Part5OriginalH430SelectedBankCarrierSupply
