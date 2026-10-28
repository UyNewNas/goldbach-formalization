import ImbalancedChen.Part3OriginalLiteralS1CountDictionary
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Identify the original independently defined samePsiS1 with the actual
owned atlas. The proof uses the original mean's shared-m dictionary,
the three disjoint q pieces, gamma-forced inactive-d zeros, and the
lambda-forced rough endpoint zeros. No carrier equality is an input.
-/

namespace ImbalancedChen.Part3.OriginalLiteralS1AtlasIdentification
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalLiteralS1CountDictionary OriginalOwnedS1BlockBudget
open OriginalSamePsiS1OwnedAtlas OriginalSamePsiS1Remainder OriginalPaperPsiCoprimeCount
open OriginalMediumS1WeightedRemainder OriginalMediumS1CommonMCount
open OriginalMediumPhysicalE3Block OriginalGevreyPoissonPacket20261028
open MediumActualPsiPreliminaryDispersion20261028 MediumActualPreliminaryCauchy20261028
open MediumGlobalDyadicOwnership20261028

def roughClosed (k : Key) : Finset ℕ := Icc (2 ^ k.w) (2 ^ (k.w + 1))

theorem atlasBlock_wCarrier {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom)
    (j : Fin 3) (d : ℕ) (hd : d ∈ activeD atom k) :
    (atlasBlock atom z y k hA j d hd).wCarrier = roughClosed k := by
  change Icc (Nat.ceil ((((2 : ℕ) ^ k.w : ℕ) : ℝ)))
      (Nat.floor (2 * ((((2 : ℕ) ^ k.w : ℕ) : ℝ)))) = _
  rw [Nat.ceil_natCast]
  have hcast : (2 : ℝ) * (((2 : ℕ) ^ k.w : ℕ) : ℝ) =
      (((2 : ℕ) ^ (k.w + 1) : ℕ) : ℝ) := by
    rw [pow_succ]
    push_cast
    ring
  rw [hcast, Nat.floor_natCast]
  rfl

theorem nativePurePair_zero_left_outside (atom : MediumAtom) (z y : ℝ)
    (k : Key) (q d r s : ℕ) (hr : r ∉ dyadicWindow k.w) :
    nativePurePair atom z y k q d r s = 0 := by
  simp [nativePurePair, lambdaTrim_zero_outside_rough_window atom z y k d r hr]

theorem nativePurePair_zero_right_outside (atom : MediumAtom) (z y : ℝ)
    (k : Key) (q d r s : ℕ) (hs : s ∉ dyadicWindow k.w) :
    nativePurePair atom z y k q d r s = 0 := by
  simp [nativePurePair, lambdaTrim_zero_outside_rough_window atom z y k d s hs]

/-- The closed FixedBlock rough carrier adds only zero endpoints. -/
theorem sum_roughClosed_native_pairs (atom : MediumAtom) (z y : ℝ)
    (k : Key) (q d : ℕ) :
    (∑ r ∈ roughClosed k, ∑ s ∈ roughClosed k,
      nativePurePair atom z y k q d r s) =
    ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
      nativePurePair atom z y k q d r s := by
  have hsub : dyadicWindow k.w ⊆ roughClosed k := by
    intro r hr
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hr
    exact mem_Icc.mpr ⟨hlo, hhi.le⟩
  calc
    _ = ∑ r ∈ dyadicWindow k.w, ∑ s ∈ roughClosed k,
        nativePurePair atom z y k q d r s := by
      symm
      apply sum_subset hsub
      intro r hr hnot
      exact sum_eq_zero (fun s _ => nativePurePair_zero_left_outside atom z y k q d r s hnot)
    _ = _ := by
      apply sum_congr rfl
      intro r hr
      symm
      apply sum_subset hsub
      intro s hs hnot
      exact nativePurePair_zero_right_outside atom z y k q d r s hnot

theorem native_pairs_zero_nonprimitive {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom)
    (q d : ℕ) (hd : ¬d.Coprime atom.residue.natAbs) :
    (∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
      nativePurePair atom z y k q d r s) = 0 := by
  apply sum_eq_zero
  intro r hr
  apply sum_eq_zero
  intro s hs
  simp [nativePurePair, lambdaTrim_zero_of_nonprimitive atom z y k d r hA hd]

theorem sum_native_pairs_d_eq_active {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom)
    (q : ℕ) :
    (∑ d ∈ dyadicWindow k.d, (paperQWeight atom q : ℂ) *
      ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
        nativePurePair atom z y k q d r s) =
    ∑ d ∈ activeD atom k, (paperQWeight atom q : ℂ) *
      ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
        nativePurePair atom z y k q d r s := by
  unfold activeD
  rw [sum_filter]
  apply sum_congr rfl
  intro d hd
  by_cases hc : d.Coprime atom.residue.natAbs
  · simp [hc]
  · simp [hc, native_pairs_zero_nonprimitive atom z y k hA q d hc]

@[simp] theorem paperS1PurePair_atlas_eq_native {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom)
    (j : Fin 3) (d : ℕ) (hd : d ∈ activeD atom k) (q r s : ℕ) :
    paperS1PurePair (atlasBlock atom z y k hA j d hd)
      (paperPsiNaturalCarrier atom.V) atom.V q r s =
        nativePurePair atom z y k q d r s := rfl

@[simp] theorem actualQWeight_atlas_eq_paper {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom)
    (j : Fin 3) (d : ℕ) (hd : d ∈ activeD atom k) (q : ℕ) :
    actualQWeight (atlasBlock atom z y k hA j d hd) q = (paperQWeight atom q : ℂ) := rfl

theorem atlasPureS1_eq_original_active_fibres {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) :
    atlasPureS1 atom z y k hA =
      ∑ q ∈ paperPsiNaturalCarrier atom.Q1, ∑ d ∈ activeD atom k,
        (paperQWeight atom q : ℂ) *
          ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
            nativePurePair atom z y k q d r s := by
  unfold atlasPureS1
  simp only [paperS1PurePair_atlas_eq_native, actualQWeight_atlas_eq_paper,
    atlasBlock_qCarrier, atlasBlock_wCarrier]
  simp only [← mul_sum]
  simp_rw [sum_roughClosed_native_pairs]
  calc
    _ = ∑ j : Fin 3, ∑ q ∈ qPiece atom.Q1 j,
        ∑ d ∈ (activeD atom k).attach, (paperQWeight atom q : ℂ) *
          ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
            nativePurePair atom z y k q d.val r s := by
      apply sum_congr rfl
      intro j hj
      exact sum_comm
    _ = ∑ j : Fin 3, ∑ q ∈ qPiece atom.Q1 j,
        ∑ d ∈ activeD atom k, (paperQWeight atom q : ℂ) *
          ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
            nativePurePair atom z y k q d r s := by simp only [sum_attach]
    _ = _ := sum_qPieces hA.2.2.1 _

/-- Original source identity: both sides were independently defined in
prior batches. Every coefficient, m count, q piece and endpoint is proved. -/
theorem original_samePsiS1_eq_owned_atlas {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) :
    (samePsiS1 atom z y k : ℂ) = atlasPureS1 atom z y k hA := by
  rw [samePsiS1_cast_eq_native_pure_pairs, atlasPureS1_eq_original_active_fibres]
  apply sum_congr rfl
  intro q hq
  exact sum_native_pairs_d_eq_active atom z y k hA q

theorem original_samePsiS1_eq_main_add_actual_remainder {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom) :
    (samePsiS1 atom z y k : ℂ) =
      atlasMainS1 atom z y k hA + atlasRemainder atom z y k hA := by
  rw [original_samePsiS1_eq_owned_atlas, atlasPureS1_eq_main_add_remainder]

/-- The D budget now applies to the original same-paperPsi S1 term. -/
theorem original_samePsiS1_sub_main_le_log_over_Y :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℕ) (σ κ c0 : ℝ)
      (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom),
      0 ≤ σ → k ∈ keyBank atom z y →
      ‖(samePsiS1 atom z y k : ℂ) - atlasMainS1 atom z y k hA‖ ≤
        C * atom.U ^ 2 * (1 + Real.log atom.scale) ^ 38 / keyY atom k := by
  obtain ⟨C, hC, hbound⟩ := actual_atlas_pureS1_sub_main_le_log_over_Y
  refine ⟨C, hC, ?_⟩
  intro b σ κ c0 atom z y k hA hσ hk
  rw [original_samePsiS1_eq_owned_atlas]
  exact hbound b σ κ c0 atom z y k hA hσ hk

end
end ImbalancedChen.Part3.OriginalLiteralS1AtlasIdentification
