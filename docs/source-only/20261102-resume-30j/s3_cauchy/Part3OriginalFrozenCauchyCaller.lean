import ImbalancedChen.Part3OriginalFrozenReciprocalMask

/-!
Source only, uncompiled, zero formal credit.
Actual poissonAtlasBlock.rectangleSum consumer of the new source map.
The 64 ordered polarization terms, both independent st=d sums and
all four signed product-window branches remain literal. No Eq16 saving,
six-piece completion or original outside-weight payment is asserted.
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
open ImbalancedChen.Part3.OriginalActualFrozenSmoothPackets20261102
open ImbalancedChen.Part3.OriginalFrozenReciprocalCauchy20261102
open ImbalancedChen.Part3.OriginalFrozenReciprocalMask20261102
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas

namespace ImbalancedChen.Part3.OriginalFrozenCauchyCaller20261102

def upperRowSource (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) : ℂ :=
  ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4, packetWeight e f g *
    (∑ st ∈ smoothLabels atom z y k small,
      ∑ st' ∈ smoothLabels atom z y k small,
        ∑ o ∈ (sourceCarrier B atom z y k small R Br Bs st st').image (outer B),
          outerCoefficient atom st st' e f g o *
            (∑ u ∈ innerImage B atom z y k small R Br Bs st st' o,
              innerAtom B atom st st' e o u))

theorem actualUpperRectangle_eq_upperRowSource (B : FixedBlock)
    (atom : MediumAtom) (hAtom : B.atom = atom) (z y : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (Br Bs : ℕ) :
    actualUpperRectangle B atom z y k small R Br Bs =
      upperRowSource B atom z y k small R Br Bs := by
  rw [actualUpperRectangle_eq_frozen_packets B atom hAtom]
  simp_rw [frozenUpperPacket_eq_rows, row_eq_inner_image]
  rfl

/-- The first direct original consumer. This is an identity with the
independently defined actual rectangleSum, not a SourceBind hypothesis. -/
theorem actual_rectangleSum_eq_four_reciprocal_sources
    {b : ℕ} {sigma kappa c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b sigma kappa c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (R : Rectangle) :
    let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
    B.rectangleSum R =
      upperRowSource B atom z y k small R (upperProductBound k) (upperProductBound k) -
      upperRowSource B atom z y k small R (lowerProductBound k) (upperProductBound k) -
      upperRowSource B atom z y k small R (upperProductBound k) (lowerProductBound k) +
      upperRowSource B atom z y k small R (lowerProductBound k) (lowerProductBound k) := by
  dsimp only
  rw [actual_rectangleSum_eq_four_upper atom z y k hA Csep j small hd negative R]
  simp_rw [actualUpperRectangle_eq_upperRowSource _ atom rfl]

def cauchyCharge (B : FixedBlock) (atom : MediumAtom) (z y : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ)
    (e f g : Fin 4) : ℝ :=
  Real.sqrt
    ((∑ o ∈ (sourceCarrier B atom z y k small R Br Bs st st').image (outer B),
      ‖outerCoefficient atom st st' e f g o‖^2) *
      ∑ o ∈ (sourceCarrier B atom z y k small R Br Bs st st').image (outer B),
        ‖row B atom z y k small R Br Bs st st' e o‖^2)

theorem frozenUpperPacket_norm_le_cauchyCharge (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4) :
    ‖frozenUpperPacket B atom z y k small R Br Bs st st' e f g‖ ≤
      cauchyCharge B atom z y k small R Br Bs st st' e f g :=
  Real.le_sqrt_of_sq_le
    (frozenUpperPacket_positive_Cauchy B atom z y k small R Br Bs st st' e f g)

def upperCauchyCharge (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) : ℝ :=
  ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4,
    ∑ st ∈ smoothLabels atom z y k small,
      ∑ st' ∈ smoothLabels atom z y k small,
        cauchyCharge B atom z y k small R Br Bs st st' e f g

/-- Quantitative first-Cauchy return on the real 64-term source. There
is no hidden cost 64 beyond the explicitly summed unit-mass weights. -/
theorem actualUpperRectangle_norm_le_upperCauchyCharge (B : FixedBlock)
    (atom : MediumAtom) (hAtom : B.atom = atom) (z y : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (Br Bs : ℕ) :
    ‖actualUpperRectangle B atom z y k small R Br Bs‖ ≤
      upperCauchyCharge B atom z y k small R Br Bs := by
  rw [actualUpperRectangle_eq_frozen_packets B atom hAtom]
  unfold upperCauchyCharge
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
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro st hst
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro st' hst'
  exact frozenUpperPacket_norm_le_cauchyCharge B atom z y k small R Br Bs st st' e f g

/-- Original caller with the four product-upper charges. The signs
are retained in the preceding exact theorem before taking norms. -/
theorem actual_rectangleSum_norm_le_four_cauchy_charges
    {b : ℕ} {sigma kappa c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b sigma kappa c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (R : Rectangle) :
    let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
    ‖B.rectangleSum R‖ ≤
      upperCauchyCharge B atom z y k small R (upperProductBound k) (upperProductBound k) +
      upperCauchyCharge B atom z y k small R (lowerProductBound k) (upperProductBound k) +
      upperCauchyCharge B atom z y k small R (upperProductBound k) (lowerProductBound k) +
      upperCauchyCharge B atom z y k small R (lowerProductBound k) (lowerProductBound k) := by
  dsimp only
  let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
  let U := upperProductBound k
  let L := lowerProductBound k
  have hUU := actualUpperRectangle_norm_le_upperCauchyCharge B atom rfl z y k small R U U
  have hLU := actualUpperRectangle_norm_le_upperCauchyCharge B atom rfl z y k small R L U
  have hUL := actualUpperRectangle_norm_le_upperCauchyCharge B atom rfl z y k small R U L
  have hLL := actualUpperRectangle_norm_le_upperCauchyCharge B atom rfl z y k small R L L
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
  linarith

end ImbalancedChen.Part3.OriginalFrozenCauchyCaller20261102
