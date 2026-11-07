import ImbalancedChen.Part3OriginalS1OuterScalePayment
import ImbalancedChen.Part3MediumNativePrincipalSource
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The two sides of the principal identity have independent causal parents:
E's genuine S1 atlas versus F S3's original native MT and restored
principal source. This file imports that independent source-only base,
never a Gram bound. It keeps the S2/S3 source corrections literally.
-/

namespace ImbalancedChen.Part3.OriginalS1NativeMain20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open MediumGlobalDyadicOwnership20261028 MediumActualPreliminaryCauchy20261028
open MediumActualPsiPreliminaryDispersion20261028 MediumLiteralS3Stages20261028
open MediumNativePrincipalSource20261028 OriginalGevreyPoissonPacket20261028
open OriginalSamePsiS1OwnedAtlas OriginalPrimitiveS1Atlas
open OriginalLiteralS1AtlasIdentification OriginalSamePsiS1Remainder
open OriginalPaperPsiCoprimeCount OriginalMediumPrincipalFiniteCRT OriginalMediumS3ZeroCentering
open OriginalMediumS1CommonMCount OriginalMediumS1WeightedRemainder
open OriginalS1OuterCauchy20261028 OriginalS1OuterScalePayment20261028

/-- A pointwise dictionary entry, not a second definition of nativeMT.
It is used only to reindex the independent original principal source. -/
def nativeMainEntry (atom : MediumAtom) (receiver y : ℝ) (k : Key)
    (q d r s : ℕ) : ℂ :=
  lambdaTrim atom receiver y k d r * star (lambdaTrim atom receiver y k d s) *
    (atom.V * paperMass : ℂ) * paperPrincipalCoefficient (q * d) r s *
    paperCoprimeMean atom.alphaCarrier atom.alpha (q * d) r *
    star (paperCoprimeMean atom.alphaCarrier atom.alpha (q * d) s)

theorem nativeMT_eq_sum_entries (atom : MediumAtom) (receiver y : ℝ) (k : Key) :
    nativeMT atom receiver y k =
      ∑ q ∈ (paperPsiNaturalCarrier atom.Q1).filter
          (fun q => q.Coprime atom.residue.natAbs),
        ∑ d ∈ activeD atom k, (paperQWeight atom q : ℂ) *
          ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
            nativeMainEntry atom receiver y k q d r s := by
  unfold nativeMT nativeQD nativeMainEntry
  simp only [sum_product, mul_sum]
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro r hr
  apply sum_congr rfl
  intro s hs
  ring

@[simp] theorem paperS1PrincipalPair_atlas_eq_native_entry
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (receiver y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (j : Fin 3) (d : ℕ)
    (hd : d ∈ activeD atom k) (q r s : ℕ) :
    paperS1PrincipalPair (atlasBlock atom receiver y k hA j d hd) atom.V q r s =
      nativeMainEntry atom receiver y k q d r s := by
  change lambdaTrim atom receiver y k d r * star (lambdaTrim atom receiver y k d s) *
    ((atom.V * paperMass : ℝ) : ℂ) * paperPrincipalCoefficient (q * d) r s *
    paperCoprimeMean atom.alphaCarrier atom.alpha (q * d) r *
    star (paperCoprimeMean atom.alphaCarrier atom.alpha (q * d) s) = _
  unfold nativeMainEntry
  push_cast <;> ring

private theorem nativeMainEntry_zero_left (atom : MediumAtom) (receiver y : ℝ)
    (k : Key) (q d r s : ℕ) (hr : r ∉ dyadicWindow k.w) :
    nativeMainEntry atom receiver y k q d r s = 0 := by
  simp [nativeMainEntry, lambdaTrim_zero_outside_rough_window atom receiver y k d r hr]

private theorem nativeMainEntry_zero_right (atom : MediumAtom) (receiver y : ℝ)
    (k : Key) (q d r s : ℕ) (hs : s ∉ dyadicWindow k.w) :
    nativeMainEntry atom receiver y k q d r s = 0 := by
  simp [nativeMainEntry, lambdaTrim_zero_outside_rough_window atom receiver y k d s hs]

private theorem sum_closed_nativeMainEntries (atom : MediumAtom) (receiver y : ℝ)
    (k : Key) (q d : ℕ) :
    (∑ r ∈ roughClosed k, ∑ s ∈ roughClosed k,
      nativeMainEntry atom receiver y k q d r s) =
    ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
      nativeMainEntry atom receiver y k q d r s := by
  have hsub : dyadicWindow k.w ⊆ roughClosed k := by
    intro r hr
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hr
    exact mem_Icc.mpr ⟨hlo, hhi.le⟩
  calc
    _ = ∑ r ∈ dyadicWindow k.w, ∑ s ∈ roughClosed k,
        nativeMainEntry atom receiver y k q d r s := by
      symm
      apply sum_subset hsub
      intro r hr hnot
      exact sum_eq_zero (fun s _ => nativeMainEntry_zero_left atom receiver y k q d r s hnot)
    _ = _ := by
      apply sum_congr rfl
      intro r hr
      symm
      apply sum_subset hsub
      intro s hs hnot
      exact nativeMainEntry_zero_right atom receiver y k q d r s hnot

/-- Exact equality between E's S1 principal term and S3's independently
defined original MT. Both retain primitive q, actual d, alpha, lambda,
the very same paperPsi(q/Q) and h0=integral paperPsi. -/
theorem primitiveAtlasMain_eq_nativeMT {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (receiver y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) :
    primitiveAtlasMain atom receiver y k hA = nativeMT atom receiver y k := by
  rw [nativeMT_eq_sum_entries]
  unfold primitiveAtlasMain
  simp only [paperS1PrincipalPair_atlas_eq_native_entry, actualQWeight_atlas_eq_paper,
    atlasBlock_qCarrier, atlasBlock_wCarrier]
  simp only [← mul_sum]
  simp_rw [sum_closed_nativeMainEntries]
  calc
    _ = ∑ j : Fin 3, ∑ q ∈ (qPiece atom.Q1 j).filter
        (fun q => q.Coprime atom.residue.natAbs),
        ∑ d ∈ (activeD atom k).attach, (paperQWeight atom q : ℂ) *
          ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
            nativeMainEntry atom receiver y k q d.val r s := by
      apply sum_congr rfl
      intro j hj
      exact sum_comm
    _ = _ := by
      simp only [sum_attach]
      exact sum_qPieces_filtered hA.2.2.1 atom.residue.natAbs _

theorem original_S1_eq_nativeMT_add_remainder {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (receiver y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) :
    (primitiveS1 atom receiver y k : ℂ) =
      nativeMT atom receiver y k + primitiveAtlasRemainder atom receiver y k hA := by
  rw [original_primitiveS1_eq_main_add_remainder, primitiveAtlasMain_eq_nativeMT]

def nativePrincipalFunctional (atom : MediumAtom) (receiver y : ℝ) : ℝ :=
  ((keyBank atom receiver y).card : ℝ) * ∑ k ∈ keyBank atom receiver y, outerL2 atom k *
    (primitiveS3 atom receiver y k - 2 * primitiveS2 atom receiver y k +
      (nativeMT atom receiver y k).re)

theorem atlasPrincipalFunctional_eq_native {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (receiver y : ℝ) (hA : MediumAdmissible b σ κ c0 atom) :
    atlasPrincipalFunctional atom receiver y hA = nativePrincipalFunctional atom receiver y := by
  unfold atlasPrincipalFunctional nativePrincipalFunctional
  simp_rw [primitiveAtlasMain_eq_nativeMT]

/-- This identity identifies exactly the MT consumed by S3's positive
centering. The literal S3 and S2 source corrections remain on both sides;
no assertion that these corrections vanish or are small is inserted. -/
theorem original_dispersion_main_eq_centered_source
    (atom : MediumAtom) (receiver y : ℝ) (k : Key) (hQ : 0 < atom.Q1) :
    primitiveS3 atom receiver y k - 2 * primitiveS2 atom receiver y k +
        (nativeMT atom receiver y k).re =
      (primitiveS3 atom receiver y k - (nativeRestoredZero atom receiver y k).re) -
        2 * (primitiveS2 atom receiver y k - (nativeMT atom receiver y k).re) +
          nativeP atom receiver y k := by
  rw [nativeRestoredZero_re_eq_MT_add_P atom receiver y k hQ]
  ring

theorem retainedSource_norm_sq_le_native_main_add_log_error (b : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (σ κ c0 : ℝ) (atom : MediumAtom) (receiver y : ℝ)
        (hA : MediumAdmissible b σ κ c0 atom),
        0 < σ → x0 ≤ atom.scale →
        ‖retainedSource atom receiver y‖ ^ 2 ≤ nativePrincipalFunctional atom receiver y +
          C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨C, hC, x0, hx0, hbound⟩ := retainedSource_norm_sq_le_main_add_log_error b A
  refine ⟨C, hC, x0, hx0, ?_⟩
  intro σ κ c0 atom receiver y hA hσ hx
  rw [← atlasPrincipalFunctional_eq_native atom receiver y hA]
  exact hbound σ κ c0 atom receiver y hA hσ hx

/-- Complete original Cauchy with the S1 main term identified as the
same native MT used in S3 centering, and the complete S1 error paid.
The positive nativeP is an unchanged internal term, not an assumption
or a replaced target bound. All S2/S3 restoration differences remain. -/
theorem retainedSource_norm_sq_le_centered_source_add_log_error (b : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (σ κ c0 : ℝ) (atom : MediumAtom) (receiver y : ℝ)
        (hA : MediumAdmissible b σ κ c0 atom),
        0 < σ → x0 ≤ atom.scale →
        ‖retainedSource atom receiver y‖ ^ 2 ≤
          ((keyBank atom receiver y).card : ℝ) *
            ∑ k ∈ keyBank atom receiver y, outerL2 atom k *
              ((primitiveS3 atom receiver y k - (nativeRestoredZero atom receiver y k).re) -
                2 * (primitiveS2 atom receiver y k - (nativeMT atom receiver y k).re) +
                  nativeP atom receiver y k) +
          C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨C, hC, x0, hx0, hbound⟩ := retainedSource_norm_sq_le_native_main_add_log_error b A
  refine ⟨C, hC, x0, hx0, ?_⟩
  intro σ κ c0 atom receiver y hA hσ hx
  have h := hbound σ κ c0 atom receiver y hA hσ hx
  unfold nativePrincipalFunctional at h
  have heq (k : Key) := original_dispersion_main_eq_centered_source atom receiver y k
    (lt_of_lt_of_le zero_lt_one hA.2.2.1)
  simp_rw [heq] at h
  exact h

/-- Original inclusive numeric cutoff, unchanged original source and
unchanged analytic scale. Only the exact discrete receiver is translated. -/
theorem original_numeric_source_norm_sq_le_native_main_add_log_error (b : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (σ κ c0 : ℝ) (atom : MediumAtom) (z y : ℝ)
        (hA : MediumAdmissible b σ κ c0 atom),
        0 ≤ z → 0 < σ → x0 ≤ atom.scale →
        ‖originalRetainedSource atom z y‖ ^ 2 ≤ nativePrincipalFunctional atom
          (MediumReceiverCutoffArithmetic20261028.strictReceiverCutoff z) y +
            C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨C, hC, x0, hx0, hbound⟩ := original_numeric_source_norm_sq_le_main_add_log_error b A
  refine ⟨C, hC, x0, hx0, ?_⟩
  intro σ κ c0 atom z y hA hz hσ hx
  rw [← atlasPrincipalFunctional_eq_native atom _ y hA]
  exact hbound σ κ c0 atom z y hA hz hσ hx

end
end ImbalancedChen.Part3.OriginalS1NativeMain20261028
