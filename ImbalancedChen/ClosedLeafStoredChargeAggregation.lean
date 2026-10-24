import ImbalancedChen.Part4ActualThirdOriginalClosedSplitAggregation
import Mathlib.Data.List.Forall2
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / OPEN30. Proposed unique installation module:
ImbalancedChen.Part4ActualThirdOriginalClosedLeafStoredChargeAggregationP4A.

This consumes the actual ClosedCutTree, closedLeaves, compactRegion and
compactKernel. The already proved closed-face integral identity pays every
overlap using coordinate-face nullness; no closed sets are declared disjoint.

The supplier is POSITIONAL: one real leaf estimate and one integer charge for
each occurrence in closedLeaves. List.Forall₂ prevents truncation, missing
zero leaves, duplicate elimination and an unbound permutation of charges.
Each analytic premise concerns just one actual leaf integral. Alternatively,
the pointwise supplier theorem proves that premise from a kernel ceiling
and its leaf-volume charge. Neither supplier contains the compact integral,
the final K inequality, or any bound on a sum of real integrals.

The exact original allowance is only obtained after a separate finite integer
sum inequality. This file supplies no tree, leaf estimates, stored charges,
or computed sum witness. It makes no all-40 installation/compilation claim.
The All40 concrete ABI can feed local analytic suppliers; it is not imported
here because the finite aggregation does not inspect or rebuild a query.
-/

namespace ImbalancedChen.OriginalThirdClosedLeafStoredChargeP4ASourceOnly

noncomputable section
open Set MeasureTheory
open scoped ENNReal
open OriginalThirdFiniteReserveSourceOnly
open OriginalThirdCompactPartitionSourceOnly

/-- The actual compact domain lies in a fixed compact cube. This finiteness
fact is proved from the literal ordering inequalities, not supplied by a
numerical leaf certificate. -/
theorem compactRegion_subset_unitCube :
    compactRegion ⊆ Icc (fun _ : Fin 3 => (0 : ℝ)) (fun _ => 1) := by
  intro t ht
  have ho : 0 < t 2 ∧ t 2 ≤ thirdPrefixRho ∧ t 2 ≤ t 1 ∧
      t 1 ≤ t 0 ∧ t 0 ≤ thirdPrefixRho := ht.1.1
  have hrho : thirdPrefixRho ≤ (1 : ℝ) := by norm_num [thirdPrefixRho]
  constructor
  · intro i
    fin_cases i
    · exact ho.1.le.trans (ho.2.2.1.trans ho.2.2.2.1)
    · exact ho.1.le.trans ho.2.2.1
    · exact ho.1.le
  · intro i
    fin_cases i
    · exact ho.2.2.2.2.trans hrho
    · exact (ho.2.2.2.1.trans ho.2.2.2.2).trans hrho
    · exact ho.2.1.trans hrho

theorem volume_ne_top_of_subset_compactRegion {s : Set Point}
    (hsub : s ⊆ compactRegion) : volume s ≠ ∞ := by
  have hcube : volume (Icc (fun _ : Fin 3 => (0 : ℝ)) (fun _ => 1)) < ∞ :=
    isCompact_Icc.measure_lt_top
  exact (lt_of_le_of_lt
    (measure_mono (hsub.trans compactRegion_subset_unitCube)) hcube).ne

/-- Every actual closed leaf is measurable and remains inside the original
compact domain. This does not require positive width or distinct leaves. -/
theorem closedLeaves_measurable_subset (tree : ClosedCutTree) {s : Set Point}
    (hs : MeasurableSet s) (hsub : s ⊆ compactRegion) :
    ∀ c ∈ closedLeaves tree s, MeasurableSet c ∧ c ⊆ compactRegion := by
  induction tree generalizing s with
  | leaf =>
      intro c hc
      have he : c = s := by simpa only [closedLeaves, List.mem_singleton] using hc
      subst c
      exact ⟨hs, hsub⟩
  | split j m left right ihL ihR =>
      intro c hc
      change c ∈ closedLeaves left
          (s ∩ {t : Point | t j ≤ (m : ℝ) / coordinateDenominator}) ++
        closedLeaves right
          (s ∩ {t : Point | (m : ℝ) / coordinateDenominator ≤ t j}) at hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ihL
          (hs.inter (isClosed_le (continuous_apply j) continuous_const).measurableSet)
          (fun t ht => hsub ht.1) c hc
      · exact ihR
          (hs.inter (isClosed_le continuous_const (continuous_apply j)).measurableSet)
          (fun t ht => hsub ht.1) c hc

/-- A truly local pointwise ceiling gives a real integral estimate. In
particular no integrability field needs to be included in a leaf supplier. -/
theorem leaf_integral_le_volume_mul_ceiling {c : Set Point}
    (hc : MeasurableSet c) (hsub : c ⊆ compactRegion) (height : ℝ)
    (hheight : ∀ t ∈ c, compactKernel t ≤ height) :
    (∫ t in c, compactKernel t) ≤ volume.real c * height := by
  have hf : IntegrableOn compactKernel c := integrableOn_compactKernel.mono_set hsub
  have hg : IntegrableOn (fun _ : Point => height) c :=
    integrableOn_const (volume_ne_top_of_subset_compactRegion hsub)
  calc
    (∫ t in c, compactKernel t) ≤ ∫ _ in c, height :=
      setIntegral_mono_on hf hg hc hheight
    _ = volume.real c * height := by rw [setIntegral_const, smul_eq_mul]

/-- Direct addition of genuinely local charges, without an assumption about
the sum of the integrals. This helper also covers pointwise suppliers. -/
theorem sum_leaf_integrals_le_sum_charges
    {cells : List (Set Point)} {entries : List (ℝ × ℤ)}
    (hlocal : List.Forall₂ (fun c e =>
      (∫ t in c, compactKernel t) ≤ (e.2 : ℝ) / 2^80) cells entries) :
    (cells.map (fun c => ∫ t in c, compactKernel t)).sum ≤
      (entries.map (fun e => (e.2 : ℝ) / 2^80)).sum := by
  induction hlocal with
  | nil => simp
  | cons hhead htail ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add hhead ih

/-- Finite scalar addition with the actual kernel. The entry's real field is
a local analytic estimate; its integer field is an outward 80-bit charge. -/
theorem sum_leaf_integrals_le_sum_rounded_charges
    {cells : List (Set Point)} {entries : List (ℝ × ℤ)}
    (hlocal : List.Forall₂ (fun c e =>
      (∫ t in c, compactKernel t) ≤ e.1 ∧ e.1 ≤ (e.2 : ℝ) / 2^80)
      cells entries) :
    (cells.map (fun c => ∫ t in c, compactKernel t)).sum ≤
      (entries.map (fun e => (e.2 : ℝ) / 2^80)).sum := by
  induction hlocal with
  | nil => simp
  | cons hhead htail ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (hhead.1.trans hhead.2) ih

/-- The sum is taken in the stored integer format before its one exact real
rescaling. No finite evaluation or arithmetic replay occurs in this lemma. -/
theorem sum_rounded_charges_eq_integer_sum (entries : List (ℝ × ℤ)) :
    (entries.map (fun e => (e.2 : ℝ) / 2^80)).sum =
      (((entries.map Prod.snd).sum : ℤ) : ℝ) / 2^80 := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add]
      rw [ih]
      exact (add_div _ _ _).symm

/-- The missing original compact-integral aggregation endpoint. Every local
estimate and charge must cover the actual ordered closed leaf list. The
partition identity used here already accounts for all split faces. -/
theorem originalCompactThirdCorrection_le_sum_storedCharges
    (tree : ClosedCutTree) (entries : List (ℝ × ℤ))
    (hlocal : List.Forall₂ (fun c e =>
      (∫ t in c, compactKernel t) ≤ e.1 ∧ e.1 ≤ (e.2 : ℝ) / 2^80)
      (closedLeaves tree compactRegion) entries) :
    originalCompactThirdCorrection ≤
      (((entries.map Prod.snd).sum : ℤ) : ℝ) / 2^80 := by
  rw [originalCompactThirdCorrection_eq_sum_closedLeaves tree]
  exact (sum_leaf_integrals_le_sum_rounded_charges hlocal).trans_eq
    (sum_rounded_charges_eq_integer_sum entries)

/-- A second supplier route: each entry stores a pointwise ceiling and an
integer charge. Leaf geometry, finite measure and kernel integrability are
all obtained internally from the actual tree and compact domain. -/
theorem originalCompactThirdCorrection_le_sum_storedCharges_of_pointwise
    (tree : ClosedCutTree) (entries : List (ℝ × ℤ))
    (hlocal : List.Forall₂ (fun c e =>
      (∀ t ∈ c, compactKernel t ≤ e.1) ∧
        volume.real c * e.1 ≤ (e.2 : ℝ) / 2^80)
      (closedLeaves tree compactRegion) entries) :
    originalCompactThirdCorrection ≤
      (((entries.map Prod.snd).sum : ℤ) : ℝ) / 2^80 := by
  have hgeometry : ∀ c ∈ closedLeaves tree compactRegion,
      MeasurableSet c ∧ c ⊆ compactRegion :=
    closedLeaves_measurable_subset tree measurableSet_compactRegion (fun _ ht => ht)
  have hboth : List.Forall₂ (fun c e =>
      (MeasurableSet c ∧ c ⊆ compactRegion) ∧
        ((∀ t ∈ c, compactKernel t ≤ e.1) ∧
          volume.real c * e.1 ≤ (e.2 : ℝ) / 2^80))
      (closedLeaves tree compactRegion) entries := by
    exact (List.forall₂_and_left _ _).2 ⟨hgeometry, hlocal⟩
  have hintegral : List.Forall₂ (fun c e =>
      (∫ t in c, compactKernel t) ≤ (e.2 : ℝ) / 2^80)
      (closedLeaves tree compactRegion) entries := by
    exact List.Forall₂.imp (fun c e he =>
      (leaf_integral_le_volume_mul_ceiling he.1.1 he.1.2 e.1 he.2.1).trans he.2.2) hboth
  rw [originalCompactThirdCorrection_eq_sum_closedLeaves tree]
  exact (sum_leaf_integrals_le_sum_charges hintegral).trans_eq
    (sum_rounded_charges_eq_integer_sum entries)

/-- The final compact allowance follows only after the local suppliers and
the separate integer charge sum have both been provided. This is not a
claim that either finite witness currently exists. -/
theorem originalCompactThirdCorrection_le_originalAllowance
    (tree : ClosedCutTree) (entries : List (ℝ × ℤ))
    (hlocal : List.Forall₂ (fun c e =>
      (∫ t in c, compactKernel t) ≤ e.1 ∧ e.1 ≤ (e.2 : ℝ) / 2^80)
      (closedLeaves tree compactRegion) entries)
    (hcharge : (entries.map Prod.snd).sum ≤ (144590669409566793572719 : ℤ)) :
    originalCompactThirdCorrection ≤ 144590669409566793572719 / (2 : ℝ)^80 := by
  apply (originalCompactThirdCorrection_le_sum_storedCharges tree entries hlocal).trans
  apply div_le_div_of_nonneg_right
  · exact_mod_cast hcharge
  · positivity

end
end ImbalancedChen.OriginalThirdClosedLeafStoredChargeP4ASourceOnly
