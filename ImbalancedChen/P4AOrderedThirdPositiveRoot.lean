import ImbalancedChen.P4AOrderedThirdIntegratedProfile
import ImbalancedChen.P4AOriginalHistoricalThirdActualRoot

namespace ImbalancedChen.P4AOrderedThirdPositiveRoot
noncomputable section
open Set MeasureTheory Filter Topology HistoricalThirdCoarse VariableEnvelope
open P4AOriginalOrderedThirdTable (Point retained capValue atPoint)
open P4AOrderedThirdFifthOwnersAndTail (levelAt)
open P4AOrderedThirdFixedOmegaLimit (functional evenFilter)
open P4AOrderedThirdTransportKernel (K physical_tail)
open P4AOrderedThirdIntegratedProfile (D measurable_D order integrable_K functional_eq)
open P4AOriginalHistoricalThirdMajorant (envelope envelope_eq envelope_le)
open scoped Classical BigOperators ENNReal

abbrev ideal (t : Point) := actualExtendedThirdGatedKernel 0 (t 0) (t 1) (t 2)

theorem point_lower {e g w : ℝ} (he : 0≤e) (hg : 0≤g) (hw : 0<w) {m : ℕ}
    (hm : logPrimeMeshStep 0 (19/96) m≤g) (hf : e+7*g≤3/256) {t : Point} (ht : t∈D w) :
    envelope t-(4*e+6*g)≤levelAt e w m t := by
  have ho := order hw ht
  have horder : t∈actualExtendedThirdClosedOrder := ⟨ho.1.le,ho.2.1.le,ho.2.2.1.le⟩
  rw [levelAt,if_pos (mem_logPrimeBox.mp ht.1 2).1]
  by_cases h : ∃ j∈retained e m,t∈logPrimeMeshCell 0 (19/96) m j
  · obtain ⟨j,hj,htj⟩ := h
    rw [P4AOriginalOrderedThirdTable.atPoint_on_cell hj htj]
    exact P4AOrderedThirdCompactComparison.cell_lower he hg hm hf
      (P4AOriginalOrderedThirdTable.owned_portion htj horder)
  · rw [atPoint,dif_neg h]
    change _≤thirdPrefixTheta-2*e
    linarith only [envelope_le t,he,hg]

/-- The same compact error works for every physical w, even below the
analytic tail split h. Only the compact [h,rho] modulus enters E. -/
theorem compact_upper {h tol : ℝ} (hh : 0<h) (htol : 0<tol) :
    ∃ E : ℝ,0<E ∧ ∀ e w : ℝ,0≤e → e<E → 0<w → ∀ m : ℕ,
      logPrimeMeshStep 0 (19/96) m≤e/2 → ∀ t∈D w,h≤t 2 → K e w m t≤ideal t+tol := by
  obtain ⟨u,hu,hm⟩ := actualExtendedThirdCapKernel_uniform_approx hh htol
  refine ⟨min (u/8) (1/1000),lt_min (by positivity) (by norm_num),?_⟩
  intro e w he hE hw m hstep t ht hz
  have he1 := hE.trans_le (min_le_left _ _)
  have he2 := hE.trans_le (min_le_right _ _)
  have ho := order hw ht
  let L := envelope t
  let a := min (levelAt e w m t) L
  have hL : L≤thirdPrefixTheta := envelope_le t
  have hr := point_lower he (half_nonneg he) hw hstep (by linarith only [he2]) ht
  have hmain := hm e a L (t 0) (t 1) (t 2) he (by linarith only [he1,hu])
    ((min_le_right _ _).trans hL) hL (by
      dsimp only [a,L]; apply abs_le.mpr
      exact ⟨by have := le_min hr (by linarith : envelope t-(4*e+6*(e/2))≤envelope t)
                linarith only [this,he1,hu],
        by linarith only [min_le_right (levelAt e w m t) (envelope t),hu]⟩)
    (hz.trans (ho.2.1.le.trans ho.2.2.1.le)) (hz.trans ho.2.1.le) hz
  have hmon : K e w m t≤actualExtendedThirdCapKernel e a (t 0) (t 1) (t 2) := by
    have hF := monotone_actualExtendedThirdLowerFactor
      (div_le_div_of_nonneg_right (by linarith only [min_le_left (levelAt e w m t) L] :
        a-t 0-t 1-t 2≤levelAt e w m t-t 0-t 1-t 2) ho.1.le)
    have hx := ho.1.trans (ho.2.1.trans ho.2.2.1)
    have hy := ho.1.trans ho.2.1
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (sub_le_sub_left hF _) (by norm_num))
      (mul_nonneg (mul_nonneg hx.le hy.le) (sq_nonneg _))
  have hId : ideal t=actualExtendedThirdCapKernel 0 L (t 0) (t 1) (t 2) := by
    rw [actualExtendedThirdGatedKernel_zero_buffer_eq_capKernel ho.1]
    rw [show L=actualExtendedThirdIdealCap (t 0) (t 1) (t 2) from envelope_eq ho.1.le ho.2.1.le ho.2.2.1.le]
  rw [hId]; linarith only [hmon,(abs_le.mp hmain).2]

theorem functional_upper {eta : ℝ} (heta : 0<eta) :
    ∃ E : ℝ,0<E ∧ ∀ e w : ℝ,0≤e → e<E → e≤1/384 → 0<w → ∀ m : ℕ,
      logPrimeMeshStep 0 (19/96) m≤e/2 → functional e m w≤actualExtendedThirdIdealFunctional+eta := by
  let tol := eta/2
  have htol : 0<tol := half_pos heta
  obtain ⟨h,hh,hs,hsmall⟩ := P4AOrderedThirdFifthOwnersAndTail.uniform_tail htol
  obtain ⟨E,hE,hcmp⟩ := compact_upper hh htol
  refine ⟨E,hE,?_⟩
  intro e w he hl hecap hw m hm
  let S := D w ∩ {t : Point | t 2<h}
  let C := D w ∩ {t : Point | h≤t 2}
  have hS : MeasurableSet S := (measurable_D w).inter (isOpen_lt (continuous_apply 2) continuous_const).measurableSet
  have hC : MeasurableSet C := (measurable_D w).inter (isClosed_le continuous_const (continuous_apply 2)).measurableSet
  have hd : Disjoint S C := Set.disjoint_left.mpr (fun _ ht hc => (not_lt_of_ge hc.2) ht.2)
  have hu : S∪C=D w := by
    ext t
    change ((t∈D w ∧ t 2<h) ∨ (t∈D w ∧ h≤t 2)) ↔ t∈D w
    constructor
    · rintro (ht|ht) <;> exact ht.1
    · intro ht
      rcases lt_or_ge (t 2) h with hn|hn
      · exact Or.inl ⟨ht,hn⟩
      · exact Or.inr ⟨ht,hn⟩
  have hSsub : S ⊆ actualExtendedThirdOrderedTailRegion h := by
    intro t ht; have ho := order hw ht.1
    exact ⟨ho.1,ht.2.le,ho.2.1.trans ho.2.2.1,ho.2.2.2.le,ho.2.1,ho.2.2.1.le⟩
  have hCS : C ⊆ actualExtendedThirdCompactOrder h := by
    intro t ht; have ho := order hw ht.1
    exact ⟨ht.2,ho.2.1.le,ho.2.2.1.le,ho.2.2.2.le⟩
  have hfull : C ⊆ actualExtendedThirdClosedOrderRegion thirdPrefixRho := by
    intro t ht; have ho := order hw ht.1
    exact ⟨ho.1,(ho.2.1.trans (ho.2.2.1.trans ho.2.2.2)).le,ho.2.1.le,ho.2.2.1.le,ho.2.2.2.le⟩
  have hI := integrable_K e w m hw
  have hSnon : ∀ᵐ t ∂volume.restrict S,0≤K e w m t := by
    filter_upwards [ae_restrict_mem hS] with t ht
    have ho := order hw ht.1
    have hr := (P4AOrderedThirdFifthOwnersAndTail.residual he hecap w m (t:=t)
      ⟨ho.1.le,ho.2.1.le,ho.2.2.1.le⟩ ho.2.2.2.le).2
    have hF := monotone_actualExtendedThirdLowerFactor
      (div_le_div_of_nonneg_right (by linarith only [hr] :
        levelAt e w m t-t 0-t 1-t 2≤thirdPrefixTheta-2*e-t 0-t 1-t 2) ho.1.le)
    have hy := ho.1.trans ho.2.1; have hx := hy.trans ho.2.2.1
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hF)) (by positivity)
  have htiny : (∫ t in S,K e w m t)≤tol := by
    apply (ENNReal.ofReal_le_ofReal_iff htol.le).mp
    rw [ofReal_integral_eq_lintegral_ofReal (hI.mono_set inter_subset_left) hSnon]
    exact (lintegral_mono_set hSsub).trans ((physical_tail he hecap hs w m).le.trans (hsmall e he hecap m w))
  have hvol := (measure_mono hCS).trans (actualExtendedThirdCompactOrder_volume_le hh)
  have hv : volume.real C≤1 := by
    have hx := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    rw [ENNReal.toReal_ofReal (by norm_num [thirdPrefixRho])] at hx
    exact hx.trans (by norm_num [thirdPrefixRho])
  have hconst : IntegrableOn (fun _ : Point => tol) C :=
    integrableOn_const (hvol.trans_lt ENNReal.ofReal_lt_top).ne
  have hi := integrableOn_actualExtendedThirdGatedKernel_full (by norm_num : (0:ℝ)≤0) (by norm_num)
  have hbig : (∫ t in C,K e w m t)≤(∫ t in C,ideal t)+tol := by
    calc
      _ ≤ ∫ t in C,ideal t+tol := setIntegral_mono_on (hI.mono_set inter_subset_left)
        ((hi.mono_set hfull).add hconst) hC (fun t ht => hcmp e w he hl hw m hm t ht.1 ht.2)
      _ = (∫ t in C,ideal t)+volume.real C*tol := by
        rw [integral_add (hi.mono_set hfull) hconst,setIntegral_const,smul_eq_mul]
      _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_right hv htol.le]
  have hnon : ∀ᵐ t ∂volume.restrict (actualExtendedThirdClosedOrderRegion thirdPrefixRho),0≤ideal t := by
    rw [Measure.restrict_congr_set (actualExtendedThirdClosedOrderRegion_ae_eq thirdPrefixRho)]
    filter_upwards [ae_restrict_mem (measurableSet_actualExtendedThirdOrderedTailRegion thirdPrefixRho)] with t ht
    exact actualExtendedThirdGatedKernel_nonneg_on_region 0 thirdPrefixRho ht
  have hpaid := setIntegral_mono_set hi hnon (Eventually.of_forall hfull)
  rw [functional_eq e w m hw,←hu,setIntegral_union hd hC (hI.mono_set inter_subset_left) (hI.mono_set inter_subset_left),
    actualExtendedThirdIdealFunctional_eq_gated]
  linarith only [hpaid,hbig,htiny,show tol=eta/2 from rfl]

/-- The fourth and later producer data are fixed independently of w.
Both E and the subsequent prescribed mesh threshold precede every positive w. -/
theorem original_four_positive (eta : ℝ) (heta : 0<eta) :
    ∃ E : ℝ,0<E ∧ ∀ e : ℚ,0<(e:ℝ) → (e:ℝ)<E → ∃ q0 : ℕ,0<q0 ∧ ∀ q : ℕ,q0≤q →
      ∀ a w : ℝ,0<w → w<thirdPrefixRho →
      ∀ᶠ N : ℕ in atTop,Even N →
        P5OriginalCommonPositivePresieve.normalize N
          (P4AOriginalFull87RawChronology.rawRoot (P4AOrderedThirdArithmeticOccurrence.fresh
            (P4AOriginalNewFifthUnion.data e q a) w N) N) < (∑ i,currentUpperEighteenPositive i)+eta := by
  let eps := eta/3
  have heps : 0<eps := by dsimp [eps]; positivity
  obtain ⟨Ef,hEf,hf⟩ := functional_upper heps
  obtain ⟨Ei,hEi,hi⟩ := P4AOriginalHistoricalFirstStop.initial_approx eps heps
  refine ⟨min Ef (min Ei (1/384)),lt_min hEf (lt_min hEi (by norm_num)),?_⟩
  intro e he hE
  have hf' := hE.trans_le (min_le_left _ _)
  have hi' := hE.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs := hE.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨q0,hq0,_,hmesh⟩ := P4AActualRefinableArchivePayment.exists_actual_refinement_threshold ((e:ℝ)/2) (by positivity) 0 0
  refine ⟨q0,hq0,?_⟩
  intro q hq a w hw hwr
  let d := P4AOriginalNewFifthUnion.data e q a
  have hstep : logPrimeMeshStep 0 (19/96) d.m≤(e:ℝ)/2 := (hmesh q hq).2
  have hinit := hi _ he hi' d.m (hstep.trans (half_le_self he.le))
  have hlim := P4AOrderedThirdFixedOmegaLimit.root_limit d hw hwr he hs hstep
  have hup := hlim.eventually (gt_mem_nhds (lt_add_of_pos_right _ heps))
  simp only [evenFilter,Filter.eventually_inf_principal] at hup
  have hfinal := hf e w he.le hf' hs hw d.m hstep
  filter_upwards [hinit,hup,eventually_ge_atTop 2] with N hI hNs hn hEven
  have hdiff := hNs ⟨by omega,hEven⟩
  change P5OriginalCommonPositivePresieve.normalize N
    (P4AOriginalFull87RawChronology.rawRoot (P4AOrderedThirdArithmeticOccurrence.fresh d w N) N -
     P4AOriginalFull87RawChronology.rawRoot (P4AOriginalHistoricalThirdOccurrence.base d N) N)
    < functional (d.e:ℝ) d.m w+eps at hdiff
  rw [P5OriginalCommonPositivePresieve.normalize_sub] at hdiff
  have hI' := hI hEven
  change P5OriginalCommonPositivePresieve.normalize N
    (P4AOriginalFull87RawChronology.rawRoot (P4AOriginalHistoricalThirdOccurrence.base d N) N)<_ at hI'
  change P5OriginalCommonPositivePresieve.normalize N (P4AOriginalFull87RawChronology.rawRoot
    (P4AOrderedThirdArithmeticOccurrence.fresh d w N) N) < _
  linarith only [hI',hdiff,hfinal,P4AOriginalFourPositiveEndpoints.original_root_add_third_le_original_positive_sum,
    show eps=eta/3 from rfl]

end
end ImbalancedChen.P4AOrderedThirdPositiveRoot

