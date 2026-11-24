import ImbalancedChen.P4AOriginalThirdFallbackAdmission

/-! All candidate rows are retained in the signed estimate. At an actual
admitted G6 occurrence the old cap is at most v(x), so it costs no extra
continuity error on that side. Outside the positive lower prime box the
entire row is exactly zero. -/
namespace ImbalancedChen.P4AOriginalThirdFallbackActualGain
noncomputable section
open Set Filter
open scoped Classical BigOperators Topology
open P4AOriginalThirdFallbackPrimeTests
open P4AOriginalThirdFallbackAdmission
open P4AOriginalThirdFallbackOccurrence (active saving lower original_increment)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalNewFifthUnion (data)
open P4ACatalogFiveCoarseWeightedPayment (candidateTuples carrier weight)
open P4ACatalogFiveCoarseResidualUniformity (exists_all_caps_ownCube_uniform_threshold)
open P5OriginalCommonRefinedConstructor P5OriginalCommonThirdScreenedSource
open P5OriginalCommonFourthSourceNavigation (firstCoordinate)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient (ThirdRegion thirdGuard rho thirdQ)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalFull87RawChronology (thirdIncrement)
open P4AOriginalRankThreeRestorationSource (beforeThirdPolicy)
open HistoricalThirdCoarse.P1ActualTuple (history)
open VariableEnvelope (v v_le_cap)

def oldExp (d : OriginalData) (N : ℕ) (p : Fin 3 → ℕ) := originalSeed d (N : ℝ) (history p)
def newExp (N : ℕ) (p : Fin 3 → ℕ) := v (actualPrimeTupleLog N p 1+actualPrimeTupleLog N p 2)
def actual (d : OriginalData) (N : ℕ) (p : Fin 3 → ℕ) :=
  normalize N (saving d N (history p))
def applied (d : OriginalData) (N : ℕ) (p : Fin 3 → ℕ) : ℝ :=
  if p ∈ candidateTuples d N ∧ Hit d N p then actual d N p else 0

theorem actual_hit (d : OriginalData) (he : 0 ≤ (d.e : ℝ)) {N : ℕ} (hN : 1 < N)
    {p : Fin 3 → ℕ} (hp : p ∈ candidateTuples d N) (hh : Hit d N p) :
    actual d N p = actualPrimeTupleOwnCubeMinus N N (newExp N p) p -
      actualPrimeTupleOwnCubeMinus N N (oldExp d N p) p := by
  have hg := (guard_eq N p).mp hh.1.2
  have hbox := hit_in_box d hN hp hh
  have hpos := fun i => (mem_actualPrimeBoxTuples_iff.mp hbox i).1.pos
  have horder := ((mem_firstExitAdmittedTuples_iff_of_decreasing 3 (beforeThirdPolicy (old3 d (N:ℝ)))
    (carrier N) (roughPrimeUniverse_pairwise_gt _ _ _ _) p).mp hp).1
  have hraw := raw_eq d N p
  change _ = (N : ℝ)^oldExp d N p at hraw
  have hc := ((HistoricalThirdCoarse.policy_third_iff (d.e : ℝ) d.chi d.m d.omega (N : ℝ)
    (p 0) (p 1) (p 2) (hpos 2) (horder (by decide : (1:Fin 3)<2)) (horder (by decide : (0:Fin 3)<1)))).mp hh.2
  change (p 0 : ℝ)^3 < _ ∧ (p 0 : ℝ)*p 1*(p 2 : ℝ)^3 <
    HistoricalThirdCoarse.rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ) (history p) at hc
  rw [hraw] at hc
  have hprod : (history p).prod = ∏ i,p i := by simp [history,Fin.prod_univ_three] <;> ac_rfl
  have hcube : ((∏ i,p i : ℕ) : ℝ)*(p 2 : ℝ)^2 < (N : ℝ)^oldExp d N p := by
    convert hc.2 using 1
    simp [Fin.prod_univ_three]
    ring
  have hmu : VariableEnvelope.mu < firstCoordinate (N : ℝ) (history p) := by rw [first_eq]; exact hg.1
  have hseed := (originalSeed_supported_interval d he (N : ℝ) (history p) (by simp [history]) hh.1.1 hmu).2
  rw [first_eq] at hseed
  have hcap : oldExp d N p ≤ newExp N p := by
    have hh := (P5OriginalAboveMuThirdLowerPhysicalCoefficient.third_initial_physical_gates hg).2.2.2.2.2
    dsimp only [oldExp,newExp]
    linarith
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN.le
  have hnCube := hcube.trans_le (Real.rpow_le_rpow_of_exponent_le hNr hcap)
  have hnew := third_eq N p
  change _ = (N : ℝ)^newExp N p at hnew
  rw [actual,saving,if_pos hh,actualPrimeTupleOwnCubeMinus,if_pos hnCube,
    actualPrimeTupleOwnCubeMinus,if_pos hcube]
  dsimp only [lower,normalize]
  rw [hraw,hnew,hprod]
  change (_-_)*Real.log (N : ℝ)/singularSeries N = _*Real.log (N : ℝ)/singularSeries N -
    _*Real.log (N : ℝ)/singularSeries N
  ring

theorem actual_sum (e : ℚ) (q : ℕ) (a : ℝ) (he : 0 ≤ (e : ℝ))
    (hsmall : (e : ℝ) ≤ 11/64000) {N : ℕ} (hN : 1<N) :
    -normalize N (thirdIncrement e q a N) =
      ∑ p ∈ primes N,(∏ i,weight (p i))*applied (data e q a) N p := by
  let d := data e q a
  rw [original_increment e q a he hsmall N (by exact_mod_cast hN.le)]
  simp_rw [pre_eq]
  let S := (candidateTuples d N).filter (Hit d N)
  have hleft : (∑ p ∈ candidateTuples d N,(∏ i,weight (p i))*actual d N p) =
      ∑ p ∈ S,(∏ i,weight (p i))*actual d N p := by
    apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro p hp hn
    have hh : ¬Hit d N p := fun hh => hn (Finset.mem_filter.mpr ⟨hp,hh⟩)
    have hz : saving d N (history p) = 0 := if_neg hh
    rw [actual,hz]
    simp [normalize]
  have hsub : S ⊆ primes N := fun p hp => hit_in_box d hN (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  change (∑ p ∈ candidateTuples d N,(∏ i,weight (p i))*actual d N p) = _
  rw [hleft]
  calc
    _ = ∑ p ∈ S,(∏ i,weight (p i))*applied d N p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [applied,if_pos (Finset.mem_filter.mp hp)]
    _ = _ := Finset.sum_subset hsub (fun p _ hp => by
      have hh : ¬(p ∈ candidateTuples d N ∧ Hit d N p) := fun h => hp (Finset.mem_filter.mpr h)
      rw [applied,if_neg hh,mul_zero])

theorem row_lower (d : OriginalData) (he : 0 ≤ (d.e : ℝ)) (r N : ℕ) (hN : 1<N)
    (eta : ℝ) (heta : 0 ≤ eta) (p : Fin 3 → ℕ) (hp : p ∈ primes N)
    (hc : combined r (actualPrimeTupleLog N p) ≠ 0 → p ∈ candidateTuples d N ∧ Hit d N p)
    (hb : ∀ L : ℝ,L ≤ thirdPrefixTheta →
      |actualPrimeTupleOwnCubeMinus N N L p-primeTupleMinusProfile L (actualPrimeTupleLog N p)|<eta) :
    combined r (actualPrimeTupleLog N p)-2*eta ≤ applied d N p := by
  let t := actualPrimeTupleLog N p
  by_cases hh : p ∈ candidateTuples d N ∧ Hit d N p
  · rw [applied,if_pos hh,actual_hit d he hN hh.1 hh.2]
    have hg := (guard_eq N p).mp hh.2.1.2
    have hmu : VariableEnvelope.mu < firstCoordinate (N : ℝ) (history p) := by rw [first_eq]; exact hg.1
    have hseed := (originalSeed_supported_interval d he (N : ℝ) (history p) (by simp [history]) hh.2.1.1 hmu).2
    rw [first_eq] at hseed
    have hold : oldExp d N p ≤ v (t 0) := by dsimp only [oldExp,t]; linarith
    have hceil (x : ℝ) : v x ≤ thirdPrefixTheta := (v_le_cap x).trans (by norm_num [VariableEnvelope.cap,thirdPrefixTheta])
    have ho := (abs_lt.mp (hb (oldExp d N p) (hold.trans (hceil _)))).2
    have hn := (abs_lt.mp (hb (newExp N p) (hceil _))).1
    have hz : 0 < t 2 := hg.2.2.1
    have harg := div_le_div_of_nonneg_right (show oldExp d N p-t 0-t 1-t 2 ≤ v (t 0)-t 0-t 1-t 2 by linarith) hz.le
    have hm : primeTupleMinusProfile (oldExp d N p) t ≤ primeTupleMinusProfile (v (t 0)) t := by
      rw [primeTupleMinusProfile_eq_extendedThirdFactor _ _ hz,primeTupleMinusProfile_eq_extendedThirdFactor _ _ hz]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (monotone_actualExtendedThirdLowerFactor harg) (by norm_num)) hz.le
    have htest := (combined_bounds r t).2
    rw [guard_profile hg] at htest
    change -eta < actualPrimeTupleOwnCubeMinus N N (newExp N p) p -
      primeTupleMinusProfile (v (t 1+t 2)) t at hn
    change actualPrimeTupleOwnCubeMinus N N (oldExp d N p) p-primeTupleMinusProfile (oldExp d N p) t < eta at ho
    change combined r t-2*eta ≤ _
    linarith only [hn,ho,hm,htest]
  · have hz : combined r t = 0 := Classical.byContradiction (fun h => hh (hc h))
    rw [applied,if_neg hh]
    change combined r t-2*eta ≤ 0
    linarith only [hz,heta]

/-- Original signed G6 floor along the actual d+ schedule. The trim,
endpoint tolerance, old mesh and enabled rough cutoff all precede N. -/
theorem exists_actual_gain (eps : ℝ) (heps : 0 < eps) :
    ∃ e0 : ℝ,0 < e0 ∧ ∀ e : ℚ,0 < (e : ℝ) → (e : ℝ) < e0 →
    ∃ q0 : ℕ,0 < q0 ∧ ∀ q : ℕ,q0 ≤ q → ∀ a : ℝ,a ≤ 1/800 →
    ∀ᶠ N : ℕ in atTop,Even N →
      currentUpperEighteenGains 5-eps < -normalize N (thirdIncrement e q a N) := by
  have hfloor : currentUpperEighteenGains 5 ≤ total := P4AOriginalThirdFallbackJacobian.slot_le_physical_images
  obtain ⟨r,hr⟩ := ((integral_limit.eventually (lt_mem_nhds (by linarith : total-eps/3<total))).exists)
  have hh := width_pos r
  refine ⟨min (width r/10) (11/64000),lt_min (by positivity) (by norm_num),?_⟩
  intro e he hsmall
  obtain ⟨q0,hq0,hcover⟩ := exists_trim_admission r e he (hsmall.trans_le (min_le_left _ _))
  refine ⟨q0,hq0,?_⟩
  intro q hq a ha
  obtain ⟨M,hM,hm⟩ := exists_eventually_bounded_mass_of_tendsto
    (tendsto_actualPrimeBoxMass (fun _ : Fin 3 => cut) (fun _ => rho)
      (fun _ => cut_pos) (fun _ => by norm_num [cut,rho]))
  let eta := eps/(6*(M+1))
  have heta : 0 < eta := div_pos heps (by linarith)
  have hs : 2*eta*M ≤ eps/3 := by
    have hmul := (div_mul_cancel₀ eps (by linarith : 6*(M+1) ≠ 0))
    change eps/(6*(M+1))*(6*(M+1)) = _ at hmul
    change 2*eta*M ≤ eps/3
    change eta*(6*(M+1)) = eps at hmul
    nlinarith only [hmul,heta]
  obtain ⟨N0,h0,hbound⟩ := exists_all_caps_ownCube_uniform_threshold cut eta cut_pos heta
  have hP := (prime_limit r).eventually (lt_mem_nhds (by linarith : testIntegral r-eps/3<testIntegral r))
  filter_upwards [eventually_ge_atTop N0,hm,hP] with N hN hmass htest hEven
  have hN1 : 1<N := by omega
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN1.le
  have hcap : (N : ℝ)^rho ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr (by norm_num [rho] : rho≤1)
  have hrow (p : Fin 3 → ℕ) (hp : p ∈ primes N) := row_lower (data e q a) he.le r N hN1 eta heta.le p hp
    (hcover q hq a ha N hN1 p hp) (hbound N hN hEven N hcap p hp)
  have hsum := Finset.sum_le_sum (s := primes N) (fun p hp =>
    mul_le_mul_of_nonneg_left (hrow p hp) (actualPrimeBoxWeight_nonneg hp))
  simp_rw [mul_sub] at hsum
  rw [Finset.sum_sub_distrib,← Finset.sum_mul] at hsum
  change testSum r N-actualPrimeBoxMass N (fun _ : Fin 3 => cut) (fun _ => rho)*(2*eta) ≤ _ at hsum
  rw [actual_sum e q a he.le (hsmall.trans_le (min_le_right _ _)).le hN1]
  linarith only [hfloor,hr,htest,hsum,hs,mul_le_mul_of_nonneg_right hmass
    (show 0 ≤ 2*eta by positivity)]

end
end ImbalancedChen.P4AOriginalThirdFallbackActualGain

