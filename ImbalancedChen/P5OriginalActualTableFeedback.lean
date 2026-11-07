import ImbalancedChen.P5OriginalFeedbackDomains

/-!
Actual adopted h248/H248 evaluations of the original W1/W2 positive RHS.
SOURCE ONLY; not compiled or installed. The finite-cell identities retain
all knot atoms and the literal unclamped child argument. H430 is not used.
These are analytic integral objects, not a count license or a certified
numeric recurrence inequality.
-/

namespace ImbalancedChen.P5OriginalActualTableFeedback

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5UpperTables.Renewal
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels P5OriginalFeedbackDomains

def singletonIntegrand (s0 : ℝ) : ℝ → ℝ :=
  weightedTable true adoptedH248Numerators (singletonProfile s0) singletonKernel

def pairIntegrand (p : W2Parameters) (j : Fin 4) : Point → ℝ :=
  weightedTable false H248Numerators (pairProfile p j) pairKernel

theorem measurable_singletonIntegrand (s0 : ℝ) : Measurable (singletonIntegrand s0) :=
  measurable_weightedTable true _ (measurable_singletonProfile s0)
    singletonKernel_continuous.measurable

theorem measurable_pairIntegrand (p : W2Parameters) (j : Fin 4) :
    Measurable (pairIntegrand p j) :=
  measurable_weightedTable false _ (measurable_pairProfile p j)
    pairKernel_continuous.measurable

theorem singletonIntegrand_bounds (s0 u : ℝ) :
    0 ≤ singletonIntegrand s0 u ∧ singletonIntegrand s0 u ≤ singletonKernel u :=
  weightedTable_bounds true adopted_h248_data_bounds _ _ _ (singletonKernel_nonneg u)

theorem pairIntegrand_bounds (p : W2Parameters) (j : Fin 4) (x : Point) :
    0 ≤ pairIntegrand p j x ∧ pairIntegrand p j x ≤ pairKernel x :=
  weightedTable_bounds false adopted_H248_data_bounds _ _ _ (pairKernel_nonneg x)

theorem integrableOn_singletonKernel {D : Set ℝ} (hD : D ⊆ singletonAmbient) :
    IntegrableOn singletonKernel D :=
  (singletonKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set hD

theorem integrableOn_pairKernel {D : Set Point} (hD : D ⊆ pairAmbient) :
    IntegrableOn pairKernel D :=
  (pairKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set hD

theorem integrableOn_W1_singleton (i : Fin 7) (j : Fin 10) :
    IntegrableOn (singletonIntegrand (W1Anchor j)) (W1Domain i j) :=
  integrableOn_weightedTable true _ (measurable_singletonProfile _) measurableSet_Ioo
    (integrableOn_singletonKernel (W1Domain_subset i j))

theorem integrableOn_W2_singleton {p : W2Parameters} (hp : W2Geometry p) (j : Fin 3) :
    IntegrableOn (singletonIntegrand p.s0) (W2SingletonDomain p j) :=
  integrableOn_weightedTable true _ (measurable_singletonProfile _)
    (measurableSet_W2SingletonDomain p j)
    (integrableOn_singletonKernel (W2SingletonDomain_subset hp j))

theorem integrableOn_W2_pair {p : W2Parameters} (hp : W2Geometry p) (j : Fin 4) :
    IntegrableOn (pairIntegrand p j) (W2PairDomain p j) :=
  integrableOn_weightedTable false _ (measurable_pairProfile p j)
    (measurableSet_W2PairDomain p j)
    (integrableOn_pairKernel (W2PairDomain_subset hp j))

/-- Literal denominator margins: no singular denominator reaches the domain. -/
theorem singleton_denominator_margin {u : ℝ} (hu : u ∈ singletonAmbient) :
    (1 / 10 : ℝ) ≤ u * (1 - u) := by
  have hm := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ 1 - u by linarith [hu.2])
    (show 0 ≤ u by linarith [hu.1])
  nlinarith [hu.1]

theorem pair_denominator_margin {p : W2Parameters} (hp : W2Geometry p) (j : Fin 4)
    {x : Point} (hx : x ∈ W2PairDomain p j) :
    (1 / 125 : ℝ) ≤ x 0 * x 1 * (1 - x 0 - x 1) := by
  obtain ⟨hbox, hr⟩ := W2PairDomain_geometry hp j hx
  have hu := hbox.1 0
  have hv := hbox.1 1
  have huv : (1 / 25 : ℝ) ≤ x 0 * x 1 :=
    by nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)]
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ x 0 * x 1 by linarith)
  nlinarith

theorem singletonIntegrand_eq_original (s0 : ℝ) {u : ℝ} (hu : u ∈ singletonAmbient) :
    singletonIntegrand s0 u = adoptedH248Floor (s0 * (1 - u)) / (u * (1 - u)) := by
  change singletonKernel u * floorStep adoptedH248Numerators (singletonProfile s0 u) = _
  rw [singletonKernel_eq_raw hu]
  dsimp [adoptedH248Floor, singletonProfile]
  ring

theorem pairIntegrand_eq_original {p : W2Parameters} (hp : W2Geometry p) (j : Fin 4)
    {x : Point} (hx : x ∈ W2PairDomain p j) :
    pairIntegrand p j x = H248 (pairProfile p j x) /
      (x 0 * x 1 * (1 - x 0 - x 1)) := by
  obtain ⟨hb, hr⟩ := W2PairDomain_geometry hp j hx
  change pairKernel x * upperFloor H248Numerators (pairProfile p j x) = _
  rw [pairKernel_eq_raw hb hr]
  dsimp [H248]
  ring

theorem W1_integral_eq_original (i : Fin 7) (j : Fin 10) :
    (∫ u in W1Domain i j, singletonIntegrand (W1Anchor j) u) =
      ∫ u in W1Domain i j, adoptedH248Floor (W1Anchor j * (1 - u)) /
        (u * (1 - u)) := by
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  exact singletonIntegrand_eq_original _ (W1Domain_subset i j hu)

theorem W2_singleton_integral_eq_original {p : W2Parameters} (hp : W2Geometry p)
    (j : Fin 3) :
    (∫ u in W2SingletonDomain p j, singletonIntegrand p.s0 u) =
      ∫ u in W2SingletonDomain p j, adoptedH248Floor (p.s0 * (1 - u)) /
        (u * (1 - u)) := by
  apply setIntegral_congr_fun (measurableSet_W2SingletonDomain p j)
  intro u hu
  exact singletonIntegrand_eq_original _ (W2SingletonDomain_subset hp j hu)

theorem W2_pair_integral_eq_original {p : W2Parameters} (hp : W2Geometry p) (j : Fin 4) :
    (∫ x in W2PairDomain p j, pairIntegrand p j x) =
      ∫ x in W2PairDomain p j, H248 (pairProfile p j x) /
        (x 0 * x 1 * (1 - x 0 - x 1)) := by
  apply setIntegral_congr_fun (measurableSet_W2PairDomain p j)
  intro x hx
  exact pairIntegrand_eq_original hp j hx

/-- Actual closed-cell dictionary for each of the 70 original W1 actions. -/
theorem W1_integral_atom_sum (i : Fin 7) (j : Fin 10) :
    (∫ u in W1Domain i j, singletonIntegrand (W1Anchor j) u) =
      ∑ b : FloorAtom, floorAtomValue adoptedH248Numerators b *
        ∫ u in W1Domain i j ∩ tablePullback true (singletonProfile (W1Anchor j)) b,
          singletonKernel u :=
  weightedTable_integral_atom_sum true _ (measurable_singletonProfile _) measurableSet_Ioo
    (integrableOn_singletonKernel (W1Domain_subset i j))

/-- Three singleton domains, with their literal s0(1-u) child argument. -/
theorem W2_singleton_integral_atom_sum {p : W2Parameters} (hp : W2Geometry p) (j : Fin 3) :
    (∫ u in W2SingletonDomain p j, singletonIntegrand p.s0 u) =
      ∑ b : FloorAtom, floorAtomValue adoptedH248Numerators b *
        ∫ u in W2SingletonDomain p j ∩ tablePullback true (singletonProfile p.s0) b,
          singletonKernel u :=
  weightedTable_integral_atom_sum true _ (measurable_singletonProfile _)
    (measurableSet_W2SingletonDomain p j)
    (integrableOn_singletonKernel (W2SingletonDomain_subset hp j))

/-- Four pair domains: fixed residual for D5/D6, moving residual for D7/D8. -/
theorem W2_pair_integral_atom_sum {p : W2Parameters} (hp : W2Geometry p) (j : Fin 4) :
    (∫ x in W2PairDomain p j, pairIntegrand p j x) =
      ∑ b : FloorAtom, floorAtomValue H248Numerators b *
        ∫ x in W2PairDomain p j ∩ tablePullback false (pairProfile p j) b, pairKernel x :=
  weightedTable_integral_atom_sum false _ (measurable_pairProfile p j)
    (measurableSet_W2PairDomain p j)
    (integrableOn_pairKernel (W2PairDomain_subset hp j))

/-- Product-measure Fubini for each literal pair-domain/table-cell intersection. -/
theorem W2_pair_atom_fubini {p : W2Parameters} (hp : W2Geometry p) (j : Fin 4)
    (b : FloorAtom) :
    (∫ x in W2PairDomain p j ∩ tablePullback false (pairProfile p j) b, pairKernel x) =
      ∫ u : ℝ, ∫ v : ℝ,
        (W2PairDomain p j ∩ tablePullback false (pairProfile p j) b).indicator
          pairKernel ![u, v] := by
  let S := W2PairDomain p j ∩ tablePullback false (pairProfile p j) b
  let F := S.indicator pairKernel
  have hS : MeasurableSet S := (measurableSet_W2PairDomain p j).inter
    (measurableSet_tablePullback false (measurable_pairProfile p j) b)
  have hF : Integrable F :=
    ((integrableOn_pairKernel (W2PairDomain_subset hp j)).mono_set
      inter_subset_left).integrable_indicator hS
  let E := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hE : MeasurePreserving E := volume_preserving_piFinTwo _
  have hPF : Integrable (fun q : ℝ × ℝ => F (E.symm q)) :=
    (hE.symm.integrable_comp_emb E.symm.measurableEmbedding).mpr hF
  have hvec (u v : ℝ) : E.symm (u, v) = ![u, v] := by
    ext i
    fin_cases i <;> rfl
  calc
    _ = ∫ x, F x := (integral_indicator hS).symm
    _ = ∫ q : ℝ × ℝ, F (E.symm q) := (hE.symm.integral_comp' F).symm
    _ = ∫ u : ℝ, ∫ v : ℝ, F (E.symm (u, v)) := integral_prod _ hPF
    _ = _ := by simp only [hvec]

theorem W2_pair_integral_finite_fubini {p : W2Parameters} (hp : W2Geometry p)
    (j : Fin 4) :
    (∫ x in W2PairDomain p j, pairIntegrand p j x) =
      ∑ b : FloorAtom, floorAtomValue H248Numerators b *
        ∫ u : ℝ, ∫ v : ℝ,
          (W2PairDomain p j ∩ tablePullback false (pairProfile p j) b).indicator
            pairKernel ![u, v] := by
  rw [W2_pair_integral_atom_sum hp j]
  apply Finset.sum_congr rfl
  intro b _
  rw [W2_pair_atom_fubini hp j b]

def actualW1Feedback (i : Fin 7) (j : Fin 10) : ℝ :=
  W1FeedbackValue i j H248 adoptedH248Floor

def actualW2Feedback (p : W2Parameters) : ℝ :=
  W2FeedbackValue p H248 adoptedH248Floor

theorem actualW1Feedback_eq (i : Fin 7) (j : Fin 10) :
    actualW1Feedback i j = H248 (W1Anchor j) +
      (∫ u in W1Domain i j, singletonIntegrand (W1Anchor j) u) / 2 := by
  rfl

theorem actualW1Feedback_eq_atom_sum (i : Fin 7) (j : Fin 10) :
    actualW1Feedback i j = H248 (W1Anchor j) +
      (∑ b : FloorAtom, floorAtomValue adoptedH248Numerators b *
        ∫ u in W1Domain i j ∩ tablePullback true (singletonProfile (W1Anchor j)) b,
          singletonKernel u) / 2 := by
  rw [actualW1Feedback_eq, W1_integral_atom_sum]

/-- The original 4/5 and 1/5 point masses and all seven original integrals. -/
theorem actualW2Feedback_eq (p : W2Parameters) :
    actualW2Feedback p = (4 * H248 p.s0 + H248 p.phi1 +
      (∫ u in W2SingletonDomain p 0, singletonIntegrand p.s0 u) +
      (∫ u in W2SingletonDomain p 1, singletonIntegrand p.s0 u) +
      (∫ u in W2SingletonDomain p 2, singletonIntegrand p.s0 u) +
      (∫ x in W2PairDomain p 0, pairIntegrand p 0 x) +
      (∫ x in W2PairDomain p 1, pairIntegrand p 1 x) +
      (∫ x in W2PairDomain p 2, pairIntegrand p 2 x) +
      (∫ x in W2PairDomain p 3, pairIntegrand p 3 x)) / 5 := by
  rfl

theorem actualW1Feedback_nonneg (i : Fin 7) (j : Fin 10) : 0 ≤ actualW1Feedback i j := by
  rw [actualW1Feedback_eq]
  exact add_nonneg (upperFloor_bounds_of_data adopted_H248_data_bounds _).1
    (div_nonneg (integral_nonneg (fun u => (singletonIntegrand_bounds _ u).1)) (by norm_num))

theorem actualW2Feedback_nonneg (p : W2Parameters) : 0 ≤ actualW2Feedback p := by
  rw [actualW2Feedback_eq]
  have hH (s : ℝ) : 0 ≤ H248 s := (upperFloor_bounds_of_data adopted_H248_data_bounds s).1
  have hs (j : Fin 3) : 0 ≤ ∫ u in W2SingletonDomain p j, singletonIntegrand p.s0 u :=
    integral_nonneg (fun u => (singletonIntegrand_bounds _ u).1)
  have ht (j : Fin 4) : 0 ≤ ∫ x in W2PairDomain p j, pairIntegrand p j x :=
    integral_nonneg (fun x => (pairIntegrand_bounds p j x).1)
  apply div_nonneg ?_ (by norm_num)
  nlinarith [hH p.s0, hH p.phi1, hs 0, hs 1, hs 2, ht 0, ht 1, ht 2, ht 3]

/-- All original 36 parameter choices discharge the geometry prerequisites. -/
theorem integrableOn_originalW2_singleton (k : Fin 36) (j : Fin 3) :
    IntegrableOn (singletonIntegrand (originalW2At k).s0)
      (W2SingletonDomain (originalW2At k) j) :=
  integrableOn_W2_singleton
    (originalRepairedW2Bank_geometry _ (originalW2At_mem k)) j

theorem integrableOn_originalW2_pair (k : Fin 36) (j : Fin 4) :
    IntegrableOn (pairIntegrand (originalW2At k) j) (W2PairDomain (originalW2At k) j) :=
  integrableOn_W2_pair (originalRepairedW2Bank_geometry _ (originalW2At_mem k)) j

def actual106Feedback : Original106Action → ℝ
  | .inl (i, j) => actualW1Feedback i j
  | .inr k => actualW2Feedback (originalW2At k)

theorem actual106Feedback_nonneg (a : Original106Action) : 0 ≤ actual106Feedback a := by
  rcases a with ⟨i, j⟩ | k
  · exact actualW1Feedback_nonneg i j
  · exact actualW2Feedback_nonneg _

end
end ImbalancedChen.P5OriginalActualTableFeedback
