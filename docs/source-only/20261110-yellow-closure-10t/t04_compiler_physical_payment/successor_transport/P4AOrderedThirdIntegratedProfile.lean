import ImbalancedChen.P4AOrderedThirdTransportKernel

namespace ImbalancedChen.P4AOrderedThirdIntegratedProfile
noncomputable section
open Set MeasureTheory HistoricalThirdCoarse
open HistoricalThirdCoarse.P1ActualTuple (mem_gateRegion)
open P4AOriginalHistoricalThirdMajorant (boxRegion ordered)
open P4AOriginalOrderedThirdTable (Point retained capValue atPoint atPoint_on_cell)
open P4AOrderedThirdArithmeticOccurrence (region)
open P4AOrderedThirdFixedOmegaLimit (functional integralOnCell)
open P4AOrderedThirdFifthOwnersAndTail (levelAt)
open P4AOrderedThirdTransportKernel (K)
open scoped Classical BigOperators

def D (w : ℝ) := boxRegion w ∩ ordered

theorem measurable_D (w : ℝ) : MeasurableSet (D w) :=
  (measurableSet_logPrimeBox _ _).inter (measurableSet_primeAffineGateRegion _ _)

theorem order {w : ℝ} (hw : 0<w) {t : Point} (ht : t∈D w) :
    0<t 2 ∧ t 2<t 1 ∧ t 1<t 0 ∧ t 0<thirdPrefixRho := by
  have b := mem_logPrimeBox.mp ht.1
  have h := ((mem_gateRegion 2 2 t).mp ht.2).1
  exact ⟨hw.trans_le (b 2).1,h (by decide),h (by decide),(b 0).2⟩

theorem compact_subset {w : ℝ} {t : Point} (hw : 0<w) (ht : t∈D w) :
    t∈actualExtendedThirdCompactOrder w := by
  have ho := order hw ht
  exact ⟨(mem_logPrimeBox.mp ht.1 2).1,ho.2.1.le,ho.2.2.1.le,ho.2.2.2.le⟩

theorem integrable_K (e w : ℝ) (m : ℕ) (hw : 0<w) : IntegrableOn (K e w m) (D w) := by
  apply Measure.integrableOn_of_bounded
    (ne_of_lt (((measure_mono (fun _ ht => compact_subset hw ht :
      D w ⊆ actualExtendedThirdCompactOrder w)).trans (actualExtendedThirdCompactOrder_volume_le hw)).trans_lt ENNReal.ofReal_lt_top))
    (P4AOrderedThirdTransportKernel.measurable_kernel e w m).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurable_D w)] with t ht
  have hb := mem_logPrimeBox.mp ht.1
  simpa only [Real.norm_eq_abs] using actualExtendedThirdCapKernel_abs_le
    (e:=e) (lam:=levelAt e w m t) hw (hb 0).1 (hb 1).1 (hb 2).1

def J (a : ℝ) (t : Point) := primeTupleMinusProfile a t * ∏ i,1/t i

theorem difference_eq {t : Point} (hp : ∀ i,0<t i) (e a : ℝ) :
    J (initial e) t-J a t=actualExtendedThirdCapKernel e a (t 0) (t 1) (t 2) := by
  rw [J,J,primeTupleMinusProfile_eq_extendedThirdFactor _ _ (hp 2),
    primeTupleMinusProfile_eq_extendedThirdFactor _ _ (hp 2),Fin.prod_univ_three]
  change _=4*(_-_)/(t 0*t 1*t 2^2)
  change 4*actualExtendedThirdLowerFactor ((thirdPrefixTheta-2*e-t 0-t 1-t 2)/t 2)/t 2*_
    -4*actualExtendedThirdLowerFactor ((a-t 0-t 1-t 2)/t 2)/t 2*_=_
  field_simp [(hp 0).ne',(hp 1).ne',(hp 2).ne'] <;> ring

theorem functional_eq (e w : ℝ) (m : ℕ) (hw : 0<w) :
    functional e m w=∫ t in D w,K e w m t := by
  let C := fun (j : Cell m) => logPrimeMeshCell 0 (19/96) m j
  let U := fun (j : Cell m) => (C j).indicator (fun t => J (initial e) t-J (capValue e m j) t)
  have hC (j : Cell m) : MeasurableSet (C j) := measurableSet_logPrimeMeshCell _ _ _ _
  have hint (a : ℝ) : IntegrableOn (J a) (D w) :=
    (integrableOn_logPrimeBox_test_cube hw _ (continuousOn_primeTupleMinusProfile hw a)).mono_set inter_subset_left
  have hI (j : Cell m) : IntegrableOn (U j) (D w) :=
    ((hint _).sub (hint _)).indicator (hC j)
  have cell (j : Cell m) : integralOnCell w (initial e) j-integralOnCell w (capValue e m j) j=
      ∫ t in D w,U j t := by
    have hset : boxRegion w ∩ region j=D w ∩ C j := by ext t; change (_ ∧ _ ∧ _) ↔ (_ ∧ _) ∧ _; tauto
    unfold integralOnCell
    rw [hset,←integral_sub ((hint _).mono_set inter_subset_left) ((hint _).mono_set inter_subset_left)]
    exact (setIntegral_indicator (hC j)).symm
  rw [functional,Finset.sum_congr rfl (fun j _ => cell j),←integral_finsetSum _ (fun j _ => hI j)]
  apply setIntegral_congr_fun (measurable_D w)
  intro t ht
  have hb := mem_logPrimeBox.mp ht.1
  have hz := (hb 2).1
  have hp (i : Fin 3) := hw.trans_le (hb i).1
  by_cases hh : ∃ j∈retained e m,t∈C j
  · obtain ⟨j,hj,htj⟩ := hh
    rw [Finset.sum_eq_single_of_mem j hj]
    · rw [U,indicator_of_mem htj,difference_eq hp,K,levelAt,if_pos hz,atPoint_on_cell hj htj]
    · intro k hk hn
      exact indicator_of_notMem (fun hh : t∈C k => hn (logPrimeMeshCell_unique (by norm_num) hh htj)) _
  · rw [Finset.sum_eq_zero (fun j hj => indicator_of_notMem (fun hh' : t∈C j => hh ⟨j,hj,hh'⟩) _),
      K,levelAt,if_pos hz,atPoint,dif_neg hh,←difference_eq hp,sub_self]

end
end ImbalancedChen.P4AOrderedThirdIntegratedProfile

