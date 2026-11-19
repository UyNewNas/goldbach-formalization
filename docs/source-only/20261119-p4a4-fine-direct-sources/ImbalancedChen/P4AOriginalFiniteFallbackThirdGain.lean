import ImbalancedChen.P4AOriginalFiniteFallbackCompactRows

namespace ImbalancedChen.P4AOriginalFiniteFallbackThirdGain
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter
open VariableEnvelope
open P4AOriginalFiniteFallbackBank (read read_some_iff)
open P4AOriginalFiniteFallbackOwnCubeRows (thirdRow old)
open P4AOriginalFiniteFallbackCanonical (selected_third)
open P4AOriginalFiniteFallbackCompactRows (applied sum_eq)
open P4AOriginalFiniteFallbackSignedSource (sum)
open P4AFallbackCanonicalBanks (bank third_some_iff meshCell_subset_closedBox)
open P4AFallbackOriginalCompactTrims (exists_third_combined_owners)
open P4AFallbackJointFiniteCover (exists_endpoint_accuracy third_closed_error)
open P4AOriginalThirdFallbackPrimeTests
open P4AOriginalThirdFallbackAdmission (Hit)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient (rho)
open P4AOriginalNewFifthUnion (data)
open P5OriginalCommonRefinedConstructor (OriginalData old3 originalSeed)
open P4ACatalogFiveCoarseWeightedPayment (candidateTuples weight)
open HistoricalThirdCoarse.P1ActualTuple (history)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalOrderedThirdFullPolicy (current prior root_on_old_owner)

theorem retained_on_old_hit {d : OriginalData} {N : ℕ} (hN : 1<N) (he : 0≤(d.e:ℝ))
    {w : ℝ} (hw : w≤d.omega) {p : Fin 3 → ℕ} (h : Hit d N p) :
    ordinaryRosserPrefixAdmissible false ((N:ℝ)^old d w N p) (history p) := by
  have eqv := congrArg P4AOriginalOrderedThirdFullPolicy.Root.scalar
    (root_on_old_owner he (by exact_mod_cast hN.le : (1:ℝ)≤N) hw h.1.1)
  have hl : old d w N p=originalSeed d N (history p) := by
    simpa [current,prior,old,P4AOriginalThirdFallbackAdmission.self] using eqv
  have ha := h.2
  rw [P5OriginalCommonRefinedPreservation.old3_after_two d _ false _ (by simp [history])] at ha
  rw [hl]
  simpa [ordinaryParityRosserPolicy,oddFirstExitPolicy] using ha

private theorem vtop (x : ℝ) : v x≤thirdPrefixTheta :=
  (v_le_cap x).trans (by norm_num [VariableEnvelope.cap,thirdPrefixTheta])

/-- Every finite retained, unretained, and missed weighted row is included.
The bound uses uniform arithmetic approximation on legal own-cube levels
and independent compact coverage of precisely the original G6 tests. -/
theorem gain (eps : ℝ) (heps : 0<eps) :
    ∃ m0 : ℕ,∀ m≥m0, ∃ e0 : ℝ,0<e0 ∧ ∀ e : ℚ,0<(e:ℝ) → (e:ℝ)<e0 →
      ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,∀ a w : ℝ,a≤1/800 → w≤a →
      ∀ᶠ N : ℕ in atTop,Even N →
        currentUpperEighteenGains 5-eps<sum (data e q a) N (thirdRow m (data e q a) w N) := by
  have hfloor := P4AOriginalThirdFallbackJacobian.slot_le_physical_images
  obtain ⟨r,hr⟩ := (integral_limit.eventually (lt_mem_nhds (by linarith : total-eps/3<total))).exists
  obtain ⟨M,hM,hmass⟩ := exists_eventually_bounded_mass_of_tendsto
    (tendsto_actualPrimeBoxMass (fun _ : Fin 3 => cut) (fun _ => rho) (fun _ => cut_pos)
      (fun _ => by norm_num [cut,rho]))
  let err := eps/(9*(M+1))
  have herr : 0<err := div_pos heps (by linarith)
  obtain ⟨dlt,hdlt,Nb,hNb,H⟩ := P4AOriginalFiniteFallbackCompactRows.compact cut err cut_pos herr
  obtain ⟨mA,hA⟩ := exists_endpoint_accuracy dlt hdlt
  obtain ⟨mT,_,hT⟩ := exists_third_combined_owners r
  refine ⟨max mA mT,?_⟩
  intro m hm
  refine ⟨width r/10,div_pos (width_pos r) (by norm_num),?_⟩
  intro e he he'
  obtain ⟨q0,hq0,had⟩ := P4AOriginalThirdFallbackAdmission.exists_trim_admission r e he he'
  refine ⟨q0,hq0,?_⟩
  intro q hq a w ha hw
  let d := data e q a
  have htest := (prime_limit r).eventually (lt_mem_nhds (by linarith : testIntegral r-eps/3<testIntegral r))
  filter_upwards [eventually_ge_atTop Nb,hmass,htest] with N hN hM' ht hEven
  have hn : 1<N := by omega
  have hrow (p : Fin 3 → ℕ) (hp : p∈primes N) :
      combined r (actualPrimeTupleLog N p)-3*err≤applied m d w N p := by
    let t := actualPrimeTupleLog N p
    have cover (hnz : combined r t≠0) :
        p∈candidateTuples d N ∧ (read m (bank m).third t).isSome ∧
        ordinaryRosserPrefixAdmissible false ((N:ℝ)^old d w N p) (history p) := by
      obtain ⟨hc,hh⟩ := had q hq a ha N hn p hp hnz
      obtain ⟨j,hj,HR⟩ := hT m ((le_max_right _ _).trans hm) t hnz
      exact ⟨hc,by simp [P4AOriginalFiniteFallbackBank.read_on_cell hj,HR],
        retained_on_old_hit hn he.le hw hh⟩
    by_cases act : p∈candidateTuples d N ∧ (read m (bank m).third t).isSome ∧
        ordinaryRosserPrefixAdmissible false ((N:ℝ)^old d w N p) (history p)
    · obtain ⟨hc,hs,hold⟩ := act
      cases hy : read m (bank m).third t with
      | none => simp [hy] at hs
      | some c =>
        obtain ⟨j,hj,hsj⟩ := read_some_iff.mp hy
        obtain ⟨hg,rfl⟩ := (third_some_iff m j c).mp hsj
        let c := P4AFallbackCanonicalBanks.level3 m j
        have hgeom := selected_third hy
        have hwz : w≤t 2 := by linarith [hgeom.1.2.2.2.2.2.2.2.2.1]
        have ho := P4AOriginalFiniteFallbackCandidate.high_upper hn he.le hc hwz hgeom.1.1
        have herr' := third_closed_error m j t (meshCell_subset_closedBox _ _ hj)
        have hclose : |(c:ℝ)-v (t 1+t 2)|≤dlt := by
          rw [abs_of_nonpos (by linarith [herr'.1] : (c:ℝ)-v (t 1+t 2)≤0)]
          linarith [hA m ((le_max_left _ _).trans hm),herr'.2]
        have hy' := (H N hN hEven p hp (old d w N p) c (v (t 0)) (v (t 1+t 2)) ho (vtop _)
          hgeom.2.2.2.2.1.le (vtop _) hclose).1
        have ht' := (combined_bounds r t).2
        rw [guard_profile hgeom.1] at ht'
        simp only [applied,if_pos hc,thirdRow,hy,if_pos hold]
        linarith only [ht',hy']
    · have hz : combined r t=0 := Classical.byContradiction (fun hh => act (cover hh))
      have hv : applied m d w N p=0 := by
        by_cases hc : p∈candidateTuples d N
        · cases h : read m (bank m).third t with
          | none => simp [applied,hc,thirdRow,show read m (bank m).third (actualPrimeTupleLog N p)=none from h]
          | some c =>
            have hn' : ¬ordinaryRosserPrefixAdmissible false ((N:ℝ)^old d w N p) (history p) :=
              fun H => act ⟨hc,by simp [h],H⟩
            simp [applied,hc,thirdRow,show read m (bank m).third (actualPrimeTupleLog N p)=some c from h,hn']
        · exact if_neg hc
      rw [hv,show combined r (actualPrimeTupleLog N p)=0 from hz]; linarith
  have hs := Finset.sum_le_sum (s:=primes N) (fun p hp =>
    mul_le_mul_of_nonneg_left (hrow p hp) (actualPrimeBoxWeight_nonneg hp))
  simp_rw [mul_sub] at hs
  rw [Finset.sum_sub_distrib,←Finset.sum_mul,←sum_eq m d w N hn] at hs
  change testSum r N-actualPrimeBoxMass N (fun _ : Fin 3 => cut) (fun _ => rho)*(3*err)≤_ at hs
  have herr' : err*(9*(M+1))=eps := div_mul_cancel₀ _ (by linarith)
  have hcost : M*(3*err)≤eps/3 := by nlinarith only [herr',herr]
  have hbound := mul_le_mul_of_nonneg_right hM' (by linarith : 0≤3*err)
  linarith only [hfloor,hr,ht,hs,hcost,hbound]

end
end ImbalancedChen.P4AOriginalFiniteFallbackThirdGain
