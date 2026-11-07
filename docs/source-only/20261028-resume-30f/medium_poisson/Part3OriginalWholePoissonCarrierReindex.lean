import ImbalancedChen.Part3OriginalPoissonCarrierCells
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.
The independent genuine fibre retained packet is reindexed into the
existing actual lambdaTrim family. Primitive q, excluded d, independent
rough labels, individual alpha carriers, all three q pieces and both
real H signs are accounted for by exact finite identities.
-/

noncomputable section
open Classical Finset Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalTrimmedCleanE3Assembly20261028
open ImbalancedChen.Part3.OriginalSourcePoissonFamilyDictionary20261028
open ImbalancedChen.Part3.OriginalPoissonFrequencyOwnership20261028
open ImbalancedChen.Part3.OriginalPoissonCarrierCells20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumGenuinePoissonFibre20261028

namespace ImbalancedChen.Part3.OriginalWholePoissonCarrierReindex20261028

attribute [local instance] Classical.propDecidable

/-- This side is the peer's independently defined genuine retained
Poisson fibre packet, including diagonal and nonclean frequencies. -/
def retainedSourceKey (atom : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ v ∈ fibreCarrier atom k,
    headCoefficient atom (strictReceiverCutoff z) y k v *
      retainedModes atom (sourceKeyH atom k) v

/-- Local finite Fubini on the actual source labels, not an analytic
separation of either lambdaTrim copy or any coprimality gate. -/
private theorem inner_modes_eq_signed_cells (atom : MediumAtom) (z y : ℝ)
    (k : Key) (q small : ℕ) :
    (∑ i ∈ innerCarrier atom k, ∑ j ∈ innerCarrier atom k,
      ∑ negative : Bool, ∑ h ∈ signedHWindow (keyRealH atom k) negative,
        maskedMode atom z y k (sourceFibre q small i.1 j.1 i.2 j.2) h) =
      ∑ negative : Bool,
        modeCell atom z y k (dyadicWindow k.w) q small negative := by
  simp only [innerCarrier, Finset.sum_product]
  calc
    _ = ∑ r ∈ dyadicWindow k.w, ∑ n1 ∈ atom.alphaCarrier,
        ∑ s ∈ dyadicWindow k.w, ∑ negative : Bool,
          ∑ n2 ∈ atom.alphaCarrier,
            ∑ h ∈ signedHWindow (keyRealH atom k) negative,
              maskedMode atom z y k (sourceFibre q small r s n1 n2) h := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro n1 hn1
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_comm
    _ = ∑ r ∈ dyadicWindow k.w, ∑ n1 ∈ atom.alphaCarrier,
        ∑ negative : Bool, ∑ s ∈ dyadicWindow k.w,
          ∑ n2 ∈ atom.alphaCarrier,
            ∑ h ∈ signedHWindow (keyRealH atom k) negative,
              maskedMode atom z y k (sourceFibre q small r s n1 n2) h := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro n1 hn1
      exact Finset.sum_comm
    _ = ∑ r ∈ dyadicWindow k.w, ∑ negative : Bool,
        ∑ n1 ∈ atom.alphaCarrier, ∑ s ∈ dyadicWindow k.w,
          ∑ n2 ∈ atom.alphaCarrier,
            ∑ h ∈ signedHWindow (keyRealH atom k) negative,
              maskedMode atom z y k (sourceFibre q small r s n1 n2) h := by
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_comm
    _ = ∑ negative : Bool, ∑ r ∈ dyadicWindow k.w,
        ∑ n1 ∈ atom.alphaCarrier, ∑ s ∈ dyadicWindow k.w,
          ∑ n2 ∈ atom.alphaCarrier,
            ∑ h ∈ signedHWindow (keyRealH atom k) negative,
              maskedMode atom z y k (sourceFibre q small r s n1 n2) h :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro negative hn
      unfold modeCell
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_comm

/-- Reindex the genuine fibre carrier, with its primitive-q filter. -/
theorem retainedSourceKey_eq_primitive_cells
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key) :
    retainedSourceKey atom z y k =
      ∑ q ∈ (paperPsiNaturalCarrier atom.Q1).filter
          (fun q => q.Coprime atom.residue.natAbs),
        ∑ small ∈ dyadicWindow k.d, ∑ negative : Bool,
          modeCell atom z y k (dyadicWindow k.w) q small negative := by
  unfold retainedSourceKey fibreCarrier
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro small hd
  simp_rw [head_retained_eq_actual_signed_windows hA z y k]
  have hqp := (Finset.mem_filter.mp hq).2
  simpa only [maskedMode, sourceFibre, if_pos hqp] using
    inner_modes_eq_signed_cells atom z y k q small

/-- The primitive-q mask is not dropped: it is moved from the actual
carrier into the exact source coefficient. -/
theorem retainedSourceKey_eq_all_q_cells
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key) :
    retainedSourceKey atom z y k =
      ∑ q ∈ paperPsiNaturalCarrier atom.Q1,
        ∑ small ∈ dyadicWindow k.d, ∑ negative : Bool,
          modeCell atom z y k (dyadicWindow k.w) q small negative := by
  rw [retainedSourceKey_eq_primitive_cells hA z y k, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqp : q.Coprime atom.residue.natAbs
  · simp only [if_pos hqp]
  · simp [hqp, modeCell, maskedMode, sourceFibre]

/-- Excluded preliminary d have zero genuine lambdaTrim coefficient. -/
theorem retainedSourceKey_eq_active_cells
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key) :
    retainedSourceKey atom z y k =
      ∑ small ∈ activeD atom k, ∑ q ∈ paperPsiNaturalCarrier atom.Q1,
        ∑ negative : Bool,
          modeCell atom z y k (dyadicWindow k.w) q small negative := by
  rw [retainedSourceKey_eq_all_q_cells hA z y k, Finset.sum_comm]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro small hd hdnot
  have hdc : ¬small.Coprime atom.residue.natAbs := by
    intro hc
    exact hdnot (Finset.mem_filter.mpr ⟨hd, hc⟩)
  simp_rw [modeCell_zero_d hA z y k _ _ small _ hdc]
  simp

/-- The actual q carrier splits into exactly its three source pieces,
while the same signed h coefficient remains inside each piece. -/
theorem all_q_cells_eq_three_qPieces {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key) (small : ℕ) :
    (∑ q ∈ paperPsiNaturalCarrier atom.Q1, ∑ negative : Bool,
      modeCell atom z y k (dyadicWindow k.w) q small negative) =
      ∑ j : Fin 3, ∑ negative : Bool, ∑ q ∈ qPiece atom.Q1 j,
        modeCell atom z y k (dyadicWindow k.w) q small negative := by
  rw [← sum_qPieces hA.2.2.1]
  apply Finset.sum_congr rfl
  intro j hj
  exact Finset.sum_comm

/-- A fixed-key sum over the genuinely constructed blocks. -/
def keyRawFamily {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ) : ℂ :=
  ∑ small : {d : ℕ // d ∈ activeD atom k}, ∑ j : Fin 3, ∑ negative : Bool,
    coefficientRawSum (poissonAtlasBlock atom z y k hA Csep j
      small.val small.property negative)

/-- WHOLE retained genuine packet equals the entire constructed raw
family at this key. This is proved from independent source carriers;
no SourceBind or clean-cover equality is an assumption. -/
theorem retainedSourceKey_eq_keyRawFamily
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key) (Csep : ℕ) :
    retainedSourceKey atom z y k = keyRawFamily atom z y k hA Csep := by
  rw [retainedSourceKey_eq_active_cells hA z y k]
  simp_rw [all_q_cells_eq_three_qPieces hA z y k]
  unfold keyRawFamily
  simp_rw [blockRaw_eq_q_cells]
  have ha : (activeD atom k).attach =
      (Finset.univ : Finset {d : ℕ // d ∈ activeD atom k}) := by
    ext d
    simp
  rw [← ha]
  simp only [Finset.sum_attach]

/-- Original genuine retained packets summed at their actual keys,
with the same physical normalization V. -/
def retainedSourceTotal (atom : MediumAtom) (z y : ℝ) : ℂ :=
  ∑ k ∈ keyBank atom (strictReceiverCutoff z) y,
    retainedSourceKey atom z y k / (atom.V : ℂ)

/-- The entire finite source-carrier identity, including all actual
keys/d/q/sign blocks. Diagonal rows are retained on BOTH sides. -/
theorem retainedSourceTotal_eq_genuineRawE2
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (Csep : ℕ) :
    retainedSourceTotal atom z y = genuineRawE2 atom z y hA Csep := by
  unfold retainedSourceTotal
  simp_rw [retainedSourceKey_eq_keyRawFamily hA z y _ Csep]
  unfold genuineRawE2 SourceBlockIndex genuineBlock keyRawFamily
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, ← Finset.sum_div]
  have ha : (keyBank atom (strictReceiverCutoff z) y).attach =
      (Finset.univ : Finset {k : Key // k ∈ keyBank atom (strictReceiverCutoff z) y}) := by
    ext k
    simp
  rw [← ha]
  simp only [Finset.sum_attach]

/-- Exact clean E3 and the unchanged general-D/root complement now
belong to the independent full retained preliminary Poisson source. -/
theorem retainedSourceTotal_eq_typed_plus_nonclean
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (Csep : ℕ) :
    retainedSourceTotal atom z y = genuineTypedE3 atom z y hA Csep +
      genuineNoncleanE2 atom z y hA Csep := by
  rw [retainedSourceTotal_eq_genuineRawE2 hA z y Csep,
    genuineRawE2_eq_typed_plus_nonclean]

end ImbalancedChen.Part3.OriginalWholePoissonCarrierReindex20261028
