import ImbalancedChen.Part3OriginalLiteralS1AtlasIdentification
import ImbalancedChen.Part3MediumPrimitivePsiSource
import ImbalancedChen.Part3MediumLiteralS3Stages
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Keep the actual (q,a)=1 gate retained by the primitive preliminary source.
The filtered remainder is bounded by the positive full divisor kernel,
not by the norm of a potentially cancelling unfiltered remainder.
-/

namespace ImbalancedChen.Part3.OriginalPrimitiveS1Atlas
noncomputable section
open Classical Finset
open scoped BigOperators
open MediumPrimitivePsiSource20261028 MediumActualPsiPreliminaryDispersion20261028
open MediumActualPreliminaryCauchy20261028 MediumGlobalDyadicOwnership20261028
open OriginalLiteralS1CountDictionary OriginalLiteralS1AtlasIdentification
open OriginalSamePsiS1OwnedAtlas OriginalOwnedS1BlockBudget
open OriginalSamePsiS1Remainder OriginalPaperPsiCoprimeCount
open OriginalMediumPhysicalE3Block OriginalMediumS1CommonMCount
open OriginalMediumS1WeightedRemainder OriginalGevreyPoissonPacket20261028

/-- The independently constructed primitive carrier and original mean
row, before any atlas expression is introduced. -/
def primitiveSourceS1 (atom : MediumAtom) (z y : ℝ) (k : Key) : ℝ :=
  ∑ t ∈ primitiveSmoothOuter atom k, jointPsi atom t *
    ‖principalRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2

theorem primitiveSmoothOuter_eq_product (atom : MediumAtom) (k : Key) :
    primitiveSmoothOuter atom k =
      ((paperPsiNaturalCarrier atom.Q1).filter
        (fun q => q.Coprime atom.residue.natAbs)) ×ˢ
      (dyadicWindow k.d ×ˢ paperPsiNaturalCarrier atom.V) := by
  ext t
  simp only [primitiveSmoothOuter, smoothOuterCarrier, mem_filter, mem_product]
  tauto

theorem primitiveSourceS1_cast_eq_native (atom : MediumAtom) (z y : ℝ) (k : Key) :
    (primitiveSourceS1 atom z y k : ℂ) =
      ∑ q ∈ (paperPsiNaturalCarrier atom.Q1).filter
          (fun q => q.Coprime atom.residue.natAbs),
        ∑ d ∈ dyadicWindow k.d, (paperQWeight atom q : ℂ) *
          ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
            nativePurePair atom z y k q d r s := by
  calc
    _ = ∑ q ∈ (paperPsiNaturalCarrier atom.Q1).filter
          (fun q => q.Coprime atom.residue.natAbs),
        ∑ d ∈ dyadicWindow k.d, (paperQWeight atom q : ℂ) *
          ∑ m ∈ paperPsiNaturalCarrier atom.V, (paperWeight atom.V m : ℂ) *
            principalRow atom z y k q d m * star (principalRow atom z y k q d m) := by
      unfold primitiveSourceS1
      rw [primitiveSmoothOuter_eq_product]
      simp only [jointPsi, sum_product, Complex.ofReal_sum, Complex.ofReal_mul,
        Complex.ofReal_pow, mul_sum]
      apply sum_congr rfl
      intro q hq
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro m hm
      rw [(Complex.mul_conj' (principalRow atom z y k q d m)).symm]
      change (paperQWeight atom q : ℂ) * (paperWeight atom.V m : ℂ) *
        (principalRow atom z y k q d m * star (principalRow atom z y k q d m)) = _
      ring
    _ = _ := by simp_rw [sum_shared_m_principal_square]

def primitiveAtlasPure {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) : ℂ :=
  ∑ j : Fin 3, ∑ d ∈ (activeD atom k).attach,
    let B := atlasBlock atom z y k hA j d.val d.property
    ∑ q ∈ B.qCarrier.filter (fun q => q.Coprime atom.residue.natAbs),
      ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
        actualQWeight B q * paperS1PurePair B (paperPsiNaturalCarrier atom.V) atom.V q r s

def primitiveAtlasMain {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) : ℂ :=
  ∑ j : Fin 3, ∑ d ∈ (activeD atom k).attach,
    let B := atlasBlock atom z y k hA j d.val d.property
    ∑ q ∈ B.qCarrier.filter (fun q => q.Coprime atom.residue.natAbs),
      ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
        actualQWeight B q * paperS1PrincipalPair B atom.V q r s

def paperRemainderOn (B : FixedBlock) (Q : Finset ℕ) (S : Finset ℕ) (M : ℝ) : ℂ :=
  ∑ q ∈ Q, ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
    actualQWeight B q * paperS1RemainderPair B S M q r s

def primitiveAtlasRemainder {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) : ℂ :=
  ∑ j : Fin 3, ∑ d ∈ (activeD atom k).attach,
    let B := atlasBlock atom z y k hA j d.val d.property
    paperRemainderOn B (B.qCarrier.filter (fun q => q.Coprime atom.residue.natAbs))
      (paperPsiNaturalCarrier atom.V) atom.V

theorem sum_qPieces_filtered {Q : ℝ} (hQ : 1 ≤ Q)
    (a : ℕ) (f : ℕ → ℂ) :
    (∑ j : Fin 3, ∑ q ∈ (qPiece Q j).filter (fun q => q.Coprime a), f q) =
      ∑ q ∈ (paperPsiNaturalCarrier Q).filter (fun q => q.Coprime a), f q := by
  simp only [sum_filter]
  exact sum_qPieces hQ (fun q => if q.Coprime a then f q else 0)

theorem primitiveSourceS1_eq_owned_atlas {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) :
    (primitiveSourceS1 atom z y k : ℂ) = primitiveAtlasPure atom z y k hA := by
  rw [primitiveSourceS1_cast_eq_native]
  have hatlas : primitiveAtlasPure atom z y k hA =
      ∑ q ∈ (paperPsiNaturalCarrier atom.Q1).filter
          (fun q => q.Coprime atom.residue.natAbs),
        ∑ d ∈ activeD atom k, (paperQWeight atom q : ℂ) *
          ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
            nativePurePair atom z y k q d r s := by
    unfold primitiveAtlasPure
    simp only [paperS1PurePair_atlas_eq_native, actualQWeight_atlas_eq_paper,
      atlasBlock_qCarrier, atlasBlock_wCarrier]
    simp only [← mul_sum]
    simp_rw [sum_roughClosed_native_pairs]
    calc
      _ = ∑ j : Fin 3, ∑ q ∈ (qPiece atom.Q1 j).filter
          (fun q => q.Coprime atom.residue.natAbs),
          ∑ d ∈ (activeD atom k).attach, (paperQWeight atom q : ℂ) *
            ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
              nativePurePair atom z y k q d.val r s := by
        apply sum_congr rfl
        intro j hj
        exact sum_comm
      _ = _ := by
        simp only [sum_attach]
        exact sum_qPieces_filtered hA.2.2.1 atom.residue.natAbs _
  rw [hatlas]
  apply sum_congr rfl
  intro q hq
  exact sum_native_pairs_d_eq_active atom z y k hA q

theorem primitiveSourceS1_eq_main_add_remainder {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) :
    (primitiveSourceS1 atom z y k : ℂ) =
      primitiveAtlasMain atom z y k hA + primitiveAtlasRemainder atom z y k hA := by
  rw [primitiveSourceS1_eq_owned_atlas]
  unfold primitiveAtlasPure primitiveAtlasMain primitiveAtlasRemainder paperRemainderOn
  simp_rw [paperS1PurePair_eq_principal_add_remainder, mul_add, sum_add_distrib]

/-- Reuse the uniform common-m theorem on a genuine singleton q block;
the analytic cutoff and all coefficients remain unchanged. -/
def singletonQBlock (B : FixedBlock) (q : ℕ) (hq : q ∈ B.qCarrier) : FixedBlock :=
  { B with qLo := q, qHi := q,
    qLo_block := B.qLo_block.trans (by exact_mod_cast (mem_Icc.mp hq).1),
    qHi_block := (show (q : ℝ) ≤ B.qHi by exact_mod_cast (mem_Icc.mp hq).2).trans B.qHi_block }

theorem paperRemainderOn_subset_uniform_kernel :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : FixedBlock) (Q S : Finset ℕ) (M : ℝ),
      Q ⊆ B.qCarrier → 0 < M → (∀ m, paperWeight M m ≠ 0 → m ∈ S) →
      ‖paperRemainderOn B Q S M‖ ≤ C * S1DivisorKernel B := by
  obtain ⟨C, hC, hbound⟩ := paperS1ActualRemainder_le_uniform_divisor_kernel
  refine ⟨C, hC, ?_⟩
  intro B Q S M hQ hM hS
  have hrow (q : ℕ) (hq : q ∈ Q) :
      ‖∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
        actualQWeight B q * paperS1RemainderPair B S M q r s‖ ≤
      C * ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier, divisorKernelTerm B q r s := by
    have h := hbound (singletonQBlock B q (hQ hq)) M hM S hS
    simpa [paperS1ActualRemainder, S1DivisorKernel, singletonQBlock,
      FixedBlock.qCarrier, divisorKernelTerm] using h
  unfold paperRemainderOn
  calc
    _ ≤ ∑ q ∈ Q, ‖∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
        actualQWeight B q * paperS1RemainderPair B S M q r s‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, C * ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
        divisorKernelTerm B q r s := sum_le_sum hrow
    _ ≤ ∑ q ∈ B.qCarrier, C * ∑ r ∈ B.wCarrier, ∑ s ∈ B.wCarrier,
        divisorKernelTerm B q r s :=
      sum_le_sum_of_subset_of_nonneg hQ (fun q _ _ => by
        apply mul_nonneg hC.le
        exact sum_nonneg (fun r _ => sum_nonneg (fun s _ => by
          dsimp [divisorKernelTerm]
          positivity)))
    _ = _ := by rw [← mul_sum]; rfl

/-- Primitive S1 uses its own q filter throughout. Only the positive
kernel is enlarged, so no cancellation-sensitive comparison is made. -/
theorem primitiveSourceS1_sub_main_le_log_over_Y :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℕ) (σ κ c0 : ℝ)
      (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom),
      0 ≤ σ → k ∈ keyBank atom z y →
      ‖(primitiveSourceS1 atom z y k : ℂ) - primitiveAtlasMain atom z y k hA‖ ≤
        C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 38 / keyY atom k := by
  obtain ⟨C, hC, hbound⟩ := paperRemainderOn_subset_uniform_kernel
  have hbase : 0 < (6 + Real.log (256 : ℝ)) ^ 38 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 256)
    positivity
  refine ⟨96 * C * (6 + Real.log (256 : ℝ)) ^ 38, by positivity, ?_⟩
  intro b σ κ c0 atom z y k hA hσ hk
  have hV : 0 < atom.V := lt_of_lt_of_le zero_lt_one hA.2.1
  rw [primitiveSourceS1_eq_main_add_remainder, add_sub_cancel_left]
  have hsum : ‖primitiveAtlasRemainder atom z y k hA‖ ≤ C * atlasKernelSum atom z y k hA := by
    unfold primitiveAtlasRemainder atlasKernelSum
    calc
      _ ≤ ∑ j : Fin 3, ∑ d ∈ (activeD atom k).attach,
          ‖paperRemainderOn (atlasBlock atom z y k hA j d.val d.property)
            ((atlasBlock atom z y k hA j d.val d.property).qCarrier.filter
              (fun q => q.Coprime atom.residue.natAbs))
            (paperPsiNaturalCarrier atom.V) atom.V‖ := by
        apply (norm_sum_le _ _).trans
        exact sum_le_sum (fun j _ => norm_sum_le _ _)
      _ ≤ C * ∑ j : Fin 3, ∑ d ∈ (activeD atom k).attach,
          S1DivisorKernel (atlasBlock atom z y k hA j d.val d.property) := by
        simp only [mul_sum]
        apply sum_le_sum
        intro j hj
        apply sum_le_sum
        intro d hd
        exact hbound _ _ _ _ (filter_subset _ _) hV (fun m hm => paperWeight_support hV hm)
  calc
    _ ≤ C * atlasKernelSum atom z y k hA := hsum
    _ ≤ C * (96 * atom.U ^ 2 * OriginalOwnedS1PolynomialCaps.sourceLog atom.scale ^ 38 /
        keyY atom k) :=
      mul_le_mul_of_nonneg_left (atlasKernelSum_le_Y atom z y k hA hσ hk) hC.le
    _ = _ := by unfold OriginalOwnedS1PolynomialCaps.sourceLog; rw [mul_pow]; ring

/-- Bind the separately authored primitive S1 used in E S2/S3
bookkeeping to this independently proved filtered carrier dictionary. -/
theorem original_primitiveS1_eq_main_add_remainder {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) :
    (MediumLiteralS3Stages20261028.primitiveS1 atom z y k : ℂ) =
      primitiveAtlasMain atom z y k hA + primitiveAtlasRemainder atom z y k hA :=
  primitiveSourceS1_eq_main_add_remainder atom z y k hA

theorem original_primitiveS1_sub_main_le_log_over_Y :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℕ) (σ κ c0 : ℝ)
      (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom),
      0 ≤ σ → k ∈ keyBank atom z y →
      ‖(MediumLiteralS3Stages20261028.primitiveS1 atom z y k : ℂ) -
        primitiveAtlasMain atom z y k hA‖ ≤
        C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 38 / keyY atom k :=
  primitiveSourceS1_sub_main_le_log_over_Y

end
end ImbalancedChen.Part3.OriginalPrimitiveS1Atlas
