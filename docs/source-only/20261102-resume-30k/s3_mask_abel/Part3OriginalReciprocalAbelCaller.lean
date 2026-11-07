import ImbalancedChen.Part3OriginalReciprocalProductAbel

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Attach the proved product/reciprocal Abel cost to J's ORIGINAL positive
Cauchy and actual rectangleSum. All 64 ordered labels, the independent
smooth-label sums and the four signed product branches are retained.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalActualProductBoundDifferences20261028
open ImbalancedChen.Part3.OriginalActualThreePairPolarization20261102
open ImbalancedChen.Part3.OriginalActualPolarizedProductCaller20261102
open ImbalancedChen.Part3.OriginalActualFrozenSmoothPackets20261102
open ImbalancedChen.Part3.OriginalFrozenReciprocalCauchy20261102
open ImbalancedChen.Part3.OriginalFrozenCauchyCaller20261102
open ImbalancedChen.Part3.OriginalReciprocalMaskSeparation20261102
open ImbalancedChen.Part3.OriginalReciprocalProductAbel20261102
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas

namespace ImbalancedChen.Part3.OriginalReciprocalAbelCaller20261102

attribute [local instance] Classical.propDecidable

/-- The exact original profile before reciprocal weighting has squared
coefficient norm at most S. No SW is reapplied after polarization. -/
theorem original_common_coefficient_energy {b : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible b sigma kappa c0 atom)
    (z : ℝ) (k : Key) (small : ℕ) (st st' : ℕ × ℕ) (e : Fin 4) :
    (∑ i ∈ range (2 ^ k.u),
      ‖if 2 ^ k.u + i ∈ commonS atom z k small st then
        lambdaS atom st st' e (2 ^ k.u + i) else 0‖ ^ 2) ≤ (2 ^ k.u : ℕ) := by
  calc
    _ ≤ ∑ _i ∈ range (2 ^ k.u), (1 : ℝ) := by
      apply sum_le_sum
      intro i hi
      by_cases hs : 2 ^ k.u + i ∈ commonS atom z k small st
      · rw [if_pos hs]
        have hh := OriginalFrozenReciprocalMask20261102.lambdaS_norm_le_one
          hA st st' e (2 ^ k.u + i)
        nlinarith [norm_nonneg (lambdaS atom st st' e (2 ^ k.u + i))]
      · simp only [if_neg hs, norm_zero, zero_pow (by omega : 2 ≠ 0)]
        norm_num
    _ = _ := by simp

def abelCauchyCharge (B : FixedBlock) (atom : MediumAtom) (z y : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ)
    (e f g : Fin 4) : ℝ :=
  Real.sqrt
    ((∑ o ∈ (sourceCarrier B atom z y k small R Br Bs st st').image (outer B),
      ‖outerCoefficient atom st st' e f g o‖ ^ 2) *
     ∑ o ∈ (sourceCarrier B atom z y k small R Br Bs st st').image (outer B),
       (2 * rowEnvelope B atom z k small R st st' e o / (2 ^ k.u : ℕ)) ^ 2)

/-- This consumes J's independently defined frozen packet. The exact
original outer coefficient energy is retained; no P-normalization or
spectral bound is assumed for the new unweighted prefix energies. -/
theorem frozenUpperPacket_norm_le_abelCauchyCharge (B : FixedBlock)
    (atom : MediumAtom) (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle)
    (Br Bs : ℕ) (st st' : ℕ × ℕ) (e f g : Fin 4) :
    ‖frozenUpperPacket B atom z y k small R Br Bs st st' e f g‖ ≤
      abelCauchyCharge B atom z y k small R Br Bs st st' e f g := by
  apply Real.le_sqrt_of_sq_le
  apply (frozenUpperPacket_positive_Cauchy B atom z y k small R Br Bs st st' e f g).trans
  apply mul_le_mul_of_nonneg_left
  · apply sum_le_sum
    intro o ho
    have hb := original_row_norm_le_product_Abel B atom z y k small R Br Bs st st' e o
    have hrow := norm_nonneg (row B atom z y k small R Br Bs st st' e o)
    exact pow_le_pow_left₀ hrow hb 2
  · exact sum_nonneg (fun o ho => sq_nonneg _)

def upperAbelCharge (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) : ℝ :=
  ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4,
    ∑ st ∈ smoothLabels atom z y k small,
      ∑ st' ∈ smoothLabels atom z y k small,
        abelCauchyCharge B atom z y k small R Br Bs st st' e f g

theorem actualUpperRectangle_norm_le_upperAbelCharge (B : FixedBlock)
    (atom : MediumAtom) (hAtom : B.atom = atom) (z y : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (Br Bs : ℕ) :
    ‖actualUpperRectangle B atom z y k small R Br Bs‖ ≤
      upperAbelCharge B atom z y k small R Br Bs := by
  rw [actualUpperRectangle_eq_frozen_packets B atom hAtom]
  unfold upperAbelCharge
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro e he
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro f hf
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro g hg
  rw [norm_mul, norm_packetWeight, one_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro st hst
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro st' hst'
  exact frozenUpperPacket_norm_le_abelCauchyCharge B atom z y k small R Br Bs st st' e f g

def upperSeparatedSource (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) : ℂ :=
  ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4, packetWeight e f g *
    (∑ st ∈ smoothLabels atom z y k small,
      ∑ st' ∈ smoothLabels atom z y k small,
        ∑ o ∈ (sourceCarrier B atom z y k small R Br Bs st st').image (outer B),
          outerCoefficient atom st st' e f g o *
            (if outerGate B atom z y k small R Bs st st' o then
              upperWeightedRow B atom z k small R st st' e o (productHi B R Br) -
              upperWeightedRow B atom z k small R st st' e o
                (min (productHi B R Br) (productLo B R - 1)) else 0))

theorem actualUpperRectangle_eq_upperSeparatedSource (B : FixedBlock)
    (atom : MediumAtom) (hAtom : B.atom = atom) (z y : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (Br Bs : ℕ) :
    actualUpperRectangle B atom z y k small R Br Bs =
      upperSeparatedSource B atom z y k small R Br Bs := by
  rw [actualUpperRectangle_eq_frozen_packets B atom hAtom]
  simp_rw [frozenUpperPacket_eq_rows, original_row_eq_separated,
    separatedRow_eq_two_upperWeighted]
  rfl

/-- The original four signs remain literal before any norm is taken. -/
theorem actual_rectangleSum_eq_four_separated_sources
    {b : ℕ} {sigma kappa c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b sigma kappa c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (R : Rectangle) :
    let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
    B.rectangleSum R =
      upperSeparatedSource B atom z y k small R (upperProductBound k) (upperProductBound k) -
      upperSeparatedSource B atom z y k small R (lowerProductBound k) (upperProductBound k) -
      upperSeparatedSource B atom z y k small R (upperProductBound k) (lowerProductBound k) +
      upperSeparatedSource B atom z y k small R (lowerProductBound k) (lowerProductBound k) := by
  dsimp only
  rw [actual_rectangleSum_eq_four_upper atom z y k hA Csep j small hd negative R]
  simp_rw [actualUpperRectangle_eq_upperSeparatedSource _ atom rfl]

theorem actual_rectangleSum_norm_le_four_Abel_charges
    {b : ℕ} {sigma kappa c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b sigma kappa c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (R : Rectangle) :
    let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
    ‖B.rectangleSum R‖ ≤
      upperAbelCharge B atom z y k small R (upperProductBound k) (upperProductBound k) +
      upperAbelCharge B atom z y k small R (lowerProductBound k) (upperProductBound k) +
      upperAbelCharge B atom z y k small R (upperProductBound k) (lowerProductBound k) +
      upperAbelCharge B atom z y k small R (lowerProductBound k) (lowerProductBound k) := by
  dsimp only
  let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
  let U := upperProductBound k
  let L := lowerProductBound k
  have hUU := actualUpperRectangle_norm_le_upperAbelCharge B atom rfl z y k small R U U
  have hLU := actualUpperRectangle_norm_le_upperAbelCharge B atom rfl z y k small R L U
  have hUL := actualUpperRectangle_norm_le_upperAbelCharge B atom rfl z y k small R U L
  have hLL := actualUpperRectangle_norm_le_upperAbelCharge B atom rfl z y k small R L L
  have he := actual_rectangleSum_eq_four_upper atom z y k hA Csep j small hd negative R
  change B.rectangleSum R = _ at he
  change ‖B.rectangleSum R‖ ≤ _
  rw [he]
  have ht :
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
  linarith

end ImbalancedChen.Part3.OriginalReciprocalAbelCaller20261102
