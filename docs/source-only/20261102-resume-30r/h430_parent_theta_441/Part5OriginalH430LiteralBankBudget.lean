import ImbalancedChen.Part5OriginalH430ArithmeticAtomRows
import ImbalancedChen.RenewalFiniteErrorPropagationP5

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The ideal coefficients below are the literal normalized-coordinate
singleton/pair integrals, with all old-table pullback atoms. They are not
free fields. They are not D13's full-Member physical-native x integrals.
The final theorem identifies production localBudget for these actual
arithmetic bank rows, retaining the entire separate base discrepancy.
It proves an identity, not an estimate on that discrepancy or the
coefficientwise absolute error. No full immutable441 hlocal is claimed.
-/

namespace ImbalancedChen.Part5OriginalH430LiteralBankBudget

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open P2OriginalBankThetaMassLimits P2OriginalHalfOpenProfileCarrier
open P2OriginalOldProfilePrimeLimits P2OriginalPhysicalOldProfileMass
open P2OriginalBankOldProfilePassage
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows

def singletonIntegralAtom (lo hi s0 : ℝ) (b : FloorAtom) : ℝ :=
  ∫ u in Ioo lo hi ∩ tablePullback true (singletonProfile s0) b, singletonKernel u

def pairIntegralAtom (p : W2Parameters) (k : Fin 4) (b : FloorAtom) : ℝ :=
  ∫ x in W2PairDomain p k ∩ tablePullback false (pairProfile p k) b, pairKernel x

def idealRow : Original106Action → RowAtom → ℝ
  | .inl (i,j), .inl b => pointAtom 1 false (W1Anchor j) b
  | .inl (i,j), .inr b =>
      singletonIntegralAtom (1/W1Anchor j) (1/W1Target i) (W1Anchor j) b/2
  | .inr j, .inl b =>
      (4*pointAtom 1 false (originalW2At j).s0 b +
        pointAtom 1 false (originalW2At j).phi1 b +
        ∑ k : Fin 4, pairIntegralAtom (originalW2At j) k b)/5
  | .inr j, .inr b =>
      (∑ k : Fin 3, singletonIntegralAtom (a0 (originalW2At j))
        (singletonTop (originalW2At j) k) (originalW2At j).s0 b)/5

theorem singletonIntegralAtom_value {lo hi : ℝ}
    (hsub : Ioo lo hi ⊆ singletonAmbient) (s0 : ℝ) (nums : Fin 200 → ℤ) :
    (∑ b : FloorAtom, singletonIntegralAtom lo hi s0 b*floorAtomValue nums b) =
      singleOldIntegral lo hi s0 nums := by
  have hk : IntegrableOn singletonKernel (Ioo lo hi) :=
    (singletonKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  have h := weightedTable_integral_atom_sum true nums (measurable_singletonProfile s0)
    measurableSet_Ioo hk
  calc
    _ = ∫ u in Ioo lo hi,
        weightedTable true nums (singletonProfile s0) singletonKernel u := by
      simpa only [singletonIntegralAtom, mul_comm] using h.symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      rw [weightedTable, singletonKernel_eq_raw (hsub hu)]
      dsimp [singletonProfile]
      ring

theorem pairIntegralAtom_value {p : W2Parameters} (hp : W2Geometry p)
    (k : Fin 4) (nums : Fin 200 → ℤ) :
    (∑ b : FloorAtom, pairIntegralAtom p k b*floorAtomValue nums b) =
      pairOldIntegral p k nums := by
  have hD := measurableSet_W2PairDomain p k
  have hk : IntegrableOn pairKernel (W2PairDomain p k) :=
    (pairKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      (W2PairDomain_subset hp k)
  have h := weightedTable_integral_atom_sum false nums (measurable_pairProfile p k) hD hk
  calc
    _ = ∫ x in W2PairDomain p k, weightedTable false nums (pairProfile p k) pairKernel x := by
      simpa only [pairIntegralAtom, mul_comm] using h.symm
    _ = _ := by
      apply setIntegral_congr_fun hD
      intro x hx
      rw [weightedTable, pairKernel_eq_raw
        (W2PairDomain_geometry hp k hx).1 (W2PairDomain_geometry hp k hx).2]
      ring

theorem idealRow_value (oldH oldh : Fin 200 → ℤ) (a : Original106Action) :
    (∑ b : RowAtom, idealRow a b*oldAtomValue oldH oldh b) = idealProfile oldH oldh a := by
  rcases a with ⟨i,j⟩ | j
  · simp only [Fintype.sum_sum_type, idealRow, oldAtomValue, idealProfile]
    simp_rw [div_mul_eq_mul_div]
    rw [Finset.sum_div, pointAtom_value,
      singletonIntegralAtom_value (W1Domain_subset i j)]
    simp only [one_mul, W1OldIntegral]
  · have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
    have hp : (∑ b : FloorAtom,
        (∑ k : Fin 4, pairIntegralAtom (originalW2At j) k b)*floorAtomValue oldH b) =
        ∑ k : Fin 4, pairOldIntegral (originalW2At j) k oldH := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [pairIntegralAtom_value hg]
    have hs : (∑ b : FloorAtom,
        (∑ k : Fin 3, singletonIntegralAtom (a0 (originalW2At j))
          (singletonTop (originalW2At j) k) (originalW2At j).s0 b)*floorAtomValue oldh b) =
        ∑ k : Fin 3, singleOldIntegral (a0 (originalW2At j))
          (singletonTop (originalW2At j) k) (originalW2At j).s0 oldh := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply singletonIntegralAtom_value
      have he : Ioo (a0 (originalW2At j)) (singletonTop (originalW2At j) k) =
          W2SingletonDomain (originalW2At j) k := by fin_cases k <;> rfl
      rw [he]
      exact W2SingletonDomain_subset hg k
    simp only [Fintype.sum_sum_type, idealRow, oldAtomValue, idealProfile]
    simp_rw [div_mul_eq_mul_div]
    rw [Finset.sum_div, Finset.sum_div]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [pointAtom_value, pointAtom_value, hp, hs]
    unfold W2OldIntegral
    ring

/-- Actual absolute discrepancy of each complete arithmetic coefficient
against its parent-Theta multiple of the normalized-coordinate ideal integral. -/
def absoluteCoefficientError {ι : Type*} (N : ℕ) (Q : ℝ) (S : Finset ι)
    (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ)
    (oldH oldh : Fin 200 → ℤ) (a : Original106Action) : ℝ :=
  ∑ b : RowAtom,
    |parentRow N Q S L d sigma (fun _ => a) b - parentTheta N Q S d sigma*idealRow a b| *
      |oldAtomValue oldH oldh b|

/-- Exact production localBudget identity for all 106 bank rows. The
base difference remains literally present; neither switched costs nor
old analytic licences have been replaced by a zero base. Theta=0 is
handled by the preceding file's absolute row-vanishing statement. -/
theorem literal_localBudget_identity {ι : Type*} (N : ℕ) (Q : ℝ) (S : Finset ι)
    (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ)
    (oldH oldh : Fin 200 → ℤ) (baseA baseB : Original106Action → ℝ)
    (a : Original106Action) (htheta : 0 < parentTheta N Q S d sigma) :
    P5RenewalFiniteError.localBudget (fun _ : Original106Action => (Finset.univ : Finset RowAtom))
      (fun _ b => b) baseA baseB
      (fun a b => normalizedParentRow N Q S L d sigma (fun _ => a) b)
      idealRow (oldAtomValue oldH oldh) a =
        |baseA a-baseB a| +
          absoluteCoefficientError N Q S L d sigma oldH oldh a / parentTheta N Q S d sigma := by
  unfold P5RenewalFiniteError.localBudget
  apply congrArg (fun x : ℝ => |baseA a-baseB a|+x)
  rw [absoluteCoefficientError, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  have heq : normalizedParentRow N Q S L d sigma (fun _ => a) b - idealRow a b =
      (parentRow N Q S L d sigma (fun _ => a) b -
        parentTheta N Q S d sigma*idealRow a b) / parentTheta N Q S d sigma := by
    unfold normalizedParentRow
    field_simp [htheta.ne']
    ring
  rw [heq, abs_div, abs_of_pos htheta]
  ring

end
end ImbalancedChen.Part5OriginalH430LiteralBankBudget
