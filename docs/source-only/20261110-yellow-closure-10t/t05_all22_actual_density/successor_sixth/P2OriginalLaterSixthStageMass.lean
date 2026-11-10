import ImbalancedChen.P2OriginalLaterSixthCorrections

/-! Assign each original integral term to its actual sixth-stage update.
The two G13 comparison corrections occur at the clean ascending34 and
descending34 stages; their owning slot and chronology are kept distinct. -/
namespace ImbalancedChen.P2OriginalLaterSixthStageMass
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalLaterSixthKernel
open P2OriginalLaterSixthArchive (Individual physicalRow)
open P2OriginalLaterSixthOwnedIntegral (support inner row_integrable)
open P2OriginalLaterSixthSourceIntegral (domain owned domain_open seven_original_source_floors)
open P2OriginalSixthSimplexMoments (Point support_measurable support_compact)

def epoch (i : Piece) : Fin 8 :=
  ⟨P4AOriginalSixthLaterLiteral.stage (action i),P4AOriginalSixthLaterSemantics.original_stage_range _⟩
def charge (i : Piece) : Point → ℝ := (owned i).indicator (kernel i)
def stageDensity (k : Fin 8) (t : Point) : ℝ :=
  ∑ i∈Finset.univ.filter (fun i => epoch i=k),charge i t

theorem inner_compact (i : Piece) : IsCompact (inner i) := by
  let s := support i
  have h (f : Finset (Individual i)) : IsCompact (⋃ j∈f,s j) := by
    induction f using Finset.induction_on with
    | empty => simp
    | @insert j f _ ih =>
      have he : (⋃ k∈insert j f,s k)=s j∪⋃ k∈f,s k := by ext t; simp
      rw [he]
      exact (support_compact _ _).union ih
  simpa [s,inner] using h Finset.univ

theorem owned_measurable (i : Piece) : MeasurableSet (owned i) :=
  (inner_compact i).isClosed.measurableSet.inter (domain_open i).measurableSet

theorem kernel_nonneg (i : Piece) {t : Point} (ht : t∈inner i) : 0≤kernel i t := by
  obtain ⟨j,hj⟩ := mem_iUnion.mp ht
  let r := (physicalRow i j).toRow
  rw [←row_density (physicalRow i j),P2OriginalSixthMomentRow.rowDensity]
  exact div_nonneg (mul_nonneg (by norm_num) (P2OriginalSixthMomentRow.row_gap_nonneg r hj))
    (Finset.prod_nonneg (fun k _ => (P2OriginalSixthMomentRow.row_factor_pos r hj k).le))

theorem charge_nonneg (i : Piece) (t : Point) : 0≤charge i t := by
  by_cases h : t∈owned i
  · simpa [charge,Set.indicator_of_mem h] using kernel_nonneg i h.1
  · simp only [charge,Set.indicator_of_not_mem h,le_refl]

theorem integral_charge (i : Piece) : (∫ t,charge i t)=sourceIntegral i (owned i) :=
  integral_indicator (owned_measurable i)

theorem integrable_charge (i : Piece) : Integrable (charge i) := by
  have h (f : Finset (Individual i)) : IntegrableOn (kernel i) (⋃ j∈f,support i j) := by
    induction f using Finset.induction_on with
    | empty => simp
    | @insert j f _ ih =>
      have he : (⋃ k∈insert j f,support i k)=support i j∪⋃ k∈f,support i k := by ext t; simp
      rw [he]
      exact (row_integrable i j).union ih
  have hi : IntegrableOn (kernel i) (inner i) := by simpa [inner] using h Finset.univ
  exact (hi.mono_set Set.inter_subset_left).integrable_indicator (owned_measurable i)

theorem integral_stages :
    (∑ k : Fin 8,∫ t,stageDensity k t)=∑ i : Piece,sourceIntegral i (owned i) := by
  have h (k : Fin 8) : (∫ t,stageDensity k t)=
      ∑ i∈Finset.univ.filter (fun i => epoch i=k),sourceIntegral i (owned i) := by
    rw [stageDensity,integral_finsetSum _ (fun i _ => integrable_charge i)]
    exact Finset.sum_congr rfl (fun i _ => integral_charge i)
  simp_rw [h]
  exact Finset.sum_fiberwise_of_maps_to (s:=Finset.univ) (t:=Finset.univ) (g:=epoch)
    (fun _ _ => Finset.mem_univ _) (fun i => sourceIntegral i (owned i))

/-- All seven claimed original rationals, redistributed on precisely
the eight successive chronological increments. -/
theorem seven_slots_le_eight_stage_integrals :
    (∑ j : Fin 7,currentUpperEighteenGains ⟨7+j.val,by omega⟩)≤
    ∑ k : Fin 8,∫ t,stageDensity k t := by
  rw [integral_stages]
  exact (Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 7))) =>
    seven_original_source_floors j)).trans_eq
      (Finset.sum_fiberwise_of_maps_to (s:=Finset.univ) (t:=Finset.univ) (g:=slot)
        (fun _ _ => Finset.mem_univ _) (fun i => sourceIntegral i (owned i)))

end
end ImbalancedChen.P2OriginalLaterSixthStageMass
