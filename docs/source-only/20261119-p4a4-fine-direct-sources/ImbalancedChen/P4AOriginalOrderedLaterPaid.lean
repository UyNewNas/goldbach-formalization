import ImbalancedChen.P4AOriginalLaterSixthPointwise

/-! All seven original later sixth debits, in the eight chronological
updates on the corrected whole ordered third and the enlarged fifth
bank. The bounded mass is the genuine target-deleted positive prime
cube. No atom outside a purchased source or on a computing wall is
discarded from the signed raw density. -/
namespace ImbalancedChen.P4AOriginalOrderedLaterPaid
noncomputable section
open Set Filter MeasureTheory
open scoped Classical BigOperators Topology
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalSavedSixthHistoricalOwner (bank)
open P4AOriginalOrderedSixthStages (policy)
open P4AOriginalOrderedSixthSigned (admitted tupleResidual)
open P4AOriginalFull87RawChronology (rawRoot)
open P5OriginalCommonPositivePresieve (normalize normalize_sub)
open P4AOriginalLaterSixthOccurrence (primes)
open P2OriginalLaterSixthInnerTests (test testSum testIntegral)
open P2OriginalLaterSixthKernel (Piece)
open P2OriginalLaterSixthStageMass (epoch)
open P2OriginalSixthMomentRow (cutoff cutoff_pos)
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)

def gain (k : Fin 8) (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) :=
  normalize N (rawRoot (policy (k.val+2) n d omega (N:ℝ)) N-rawRoot (policy (k.val+3) n d omega (N:ℝ)) N)
def total (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) :=
  normalize N (rawRoot (policy 2 n d omega (N:ℝ)) N-rawRoot (policy 10 n d omega (N:ℝ)) N)
def original : ℝ := ∑ j : Fin 7,currentUpperEighteenGains ⟨7+j.val,by omega⟩
def mass (N : ℕ) := actualPrimeBoxMass N (fun _ : Fin 6=>cutoff) (fun _=>(1/5:ℝ))

theorem telescope (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) :
    (∑ k : Fin 8,gain k n d omega N)=total n d omega N := by
  simp only [gain,total,normalize_sub]
  let f := fun m : ℕ=>normalize N (rawRoot (policy m n d omega (N:ℝ)) N)
  change (∑ k : Fin 8,f (k.val+2)-f (k.val+3))=f 2-f 10
  simp [Fin.sum_univ_succ] <;> ring

theorem gain_eq_box (k : Fin 8) (n : ℕ) (d : OriginalData) (omega : ℝ) {N : ℕ} (hN : 1<N) :
    gain k n d omega N=∑ p∈primes N,(∏ j,1/((p j:ℝ)-1))*
      (if p∈admitted n d omega N N (P4AOriginalFull87RawChronology.cutoff N)
        then tupleResidual (k.val+2) n d omega N N p else 0) := by
  let A := admitted n d omega N N (P4AOriginalFull87RawChronology.cutoff N)
  let B := primes N
  let f := fun p : Fin 6→ℕ=>(∏ j,1/((p j:ℝ)-1))*tupleResidual (k.val+2) n d omega N N p
  rw [gain,rawRoot,rawRoot,P4AOriginalOrderedSixthSigned.signed_at_stage (k.val+2) n d omega N N _
    (by exact_mod_cast hN.le)]
  change (∑ p∈A,f p)=_
  have hres : (∑ p∈A∩B,f p)=∑ p∈A,f p := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro p hp hn
    have hnb : p∉B := fun hh=>hn (Finset.mem_inter.mpr ⟨hp,hh⟩)
    have hlist := ((mem_firstExitAdmittedTuples_iff 6 _ _ p).mp hp).1
    have hpri (j : Fin 6) := mem_roughPrimeUniverse.mp (hlist.subset (List.mem_ofFn.mpr ⟨j,rfl⟩))
    have hwin : actualPrimeTupleLog N p∉P4AOriginalOrderedLaterChanged.window := by
      intro hh
      exact hnb ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
        ⟨fun j=>⟨(hpri j).2.1,(hpri j).2.2.1⟩,hh⟩)
    simp only [f,P4AOriginalOrderedLaterChanged.outside_zero k.val n d omega N N p hwin,mul_zero]
  rw [←hres,Finset.inter_comm]
  have he : B∩A=B.filter (fun p=>p∈A) := by ext p;simp
  rw [he,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp only [f,mul_zero]

theorem test_fibre (r N : ℕ) (k : Fin 8) :
    (∑ i∈Finset.univ.filter (fun i=>epoch i=k),testSum N r i)=
      ∑ p∈primes N,(∏ j,1/((p j:ℝ)-1))*P2OriginalLaterSixthJointTests.sum r k (actualPrimeTupleLog N p) := by
  simp only [testSum,actualPrimeBoxTestSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  exact (Finset.mul_sum _ _ _).symm

theorem stage_tests_lower (r : ℕ) (eta : ℝ) (heta : 0<eta) :
    ∃ N0 : ℕ,2≤N0 ∧ ∃ n0 : ℕ,∀ n≥n0,∃ E : ℝ,0<E ∧ ∀ e : ℚ,0<e → (e:ℝ)<E →
    ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,∀ a omega : ℝ,a≤1/100 → omega≤a → ∀ N≥N0,Even N →
      ∀ k : Fin 8,(∑ i∈Finset.univ.filter (fun i=>epoch i=k),testSum N r i)≤
        gain k n (bank e q a) omega N+(8*width n/cutoff^2+eta)*mass N := by
  obtain ⟨N0,h0,n0,hp⟩ := P4AOriginalLaterSixthPointwise.exists_test_lower r eta heta
  refine ⟨N0,h0,n0,?_⟩
  intro n hn
  obtain ⟨E,hE,hq'⟩ := hp n hn
  refine ⟨E,hE,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,h⟩ := hq' e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hq a omega ha hwa N hN hev
  let err := 8*width n/cutoff^2+eta
  let d := bank e q a
  have hN' : 1<N := by omega
  have hstage (k : Fin 8) : (∑ i∈Finset.univ.filter (fun i=>epoch i=k),testSum N r i)≤gain k n d omega N+err*mass N := by
    rw [test_fibre,gain_eq_box k n d omega hN']
    have hsum := Finset.sum_le_sum (fun p (hp : p∈primes N)=>
      mul_le_mul_of_nonneg_left (h q hq a omega ha hwa N hN hev p hp k) (actualPrimeBoxWeight_nonneg hp))
    apply hsum.trans_eq
    simp only [mass,actualPrimeBoxMass,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    dsimp only [err];ring
  exact hstage


theorem stage_integral (k : Fin 8) :
    (∫ t,P2OriginalLaterSixthStageMass.stageDensity k t)=
      ∑ i∈Finset.univ.filter (fun i=>epoch i=k),P2OriginalLaterSixthKernel.sourceIntegral i (P2OriginalLaterSixthSourceIntegral.owned i) := by
  rw [P2OriginalLaterSixthStageMass.stageDensity,MeasureTheory.integral_finsetSum _ (fun i _=>P2OriginalLaterSixthStageMass.integrable_charge i)]
  exact Finset.sum_congr rfl (fun i _=>P2OriginalLaterSixthStageMass.integral_charge i)

theorem exists_each_epoch (eps : ℝ) (heps : 0<eps) :
    ∃ n0 : ℕ,∀ n≥n0,∃ E : ℝ,0<E ∧ ∀ e : ℚ,0<e → (e:ℝ)<E →
    ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,∀ a omega : ℝ,a≤1/100 → omega≤a →
    ∀ᶠ N : ℕ in atTop,Even N → ∀ k : Fin 8,(∫ t,P2OriginalLaterSixthStageMass.stageDensity k t)-eps<
      gain k n (bank e q a) omega N := by
  let K := fun k : Fin 8=>∫ t,P2OriginalLaterSixthStageMass.stageDensity k t
  let F := fun k : Fin 8=>Finset.univ.filter (fun i : Piece=>epoch i=k)
  have hi (k : Fin 8) : ∀ᶠ r : ℕ in atTop,K k-eps/3<∑ i∈F k,testIntegral r i := by
    have hh := tendsto_finsetSum (F k) (fun i _=>P2OriginalLaterSixthInnerTests.testIntegral_tendsto i)
    have he : K k=∑ i∈F k,P2OriginalLaterSixthKernel.sourceIntegral i (P2OriginalLaterSixthSourceIntegral.owned i) :=
      stage_integral k
    exact hh.eventually (lt_mem_nhds (by linarith only [he,heps]))
  obtain ⟨r,hr⟩ := (eventually_all.mpr hi).exists
  have ht (k : Fin 8) : ∀ᶠ N : ℕ in atTop,K k-2*eps/3<∑ i∈F k,testSum N r i := by
    have hh := tendsto_finsetSum (F k) (fun i _=>P2OriginalLaterSixthInnerTests.testSum_tendsto r i)
    exact hh.eventually (lt_mem_nhds (by linarith only [hr k,heps]))
  let L : ℝ := ∏ _j : Fin 6,Real.log ((1/5:ℝ)/cutoff)
  let C := |L|+1
  have hC : 0<C := by dsimp [C];positivity
  let eta := eps/(8*C)
  have heta : 0<eta := by dsimp [eta];positivity
  obtain ⟨N0,h0,n0,hp⟩ := stage_tests_lower r eta heta
  have hmass : ∀ᶠ N : ℕ in atTop,mass N<C := by
    apply (tendsto_actualPrimeBoxMass (fun _ : Fin 6=>cutoff) (fun _=>(1/5:ℝ))
      (fun _=>cutoff_pos) (fun _=>by norm_num [cutoff])).eventually
    exact gt_mem_nhds (show L<C by dsimp [C];linarith [le_abs_self L])
  have hwidth : Tendsto (fun n : ℕ=>8*width n/cutoff^2) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_div] using (width_tendsto.const_mul (8:ℝ)).div_const (cutoff^2)
  obtain ⟨nw,hnw⟩ := eventually_atTop.mp (hwidth.eventually (gt_mem_nhds heta))
  refine ⟨max n0 nw,?_⟩
  intro n hn
  obtain ⟨E,hE,hq'⟩ := hp n ((le_max_left _ _).trans hn)
  refine ⟨E,hE,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hQ⟩ := hq' e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hq a omega ha hwa
  have hw := hnw n ((le_max_right _ _).trans hn)
  have hwn := width_pos n
  have hcost : (8*width n/cutoff^2+eta)*C≤eps/4 := by
    calc
      _ ≤ (2*eta)*C := mul_le_mul_of_nonneg_right (by linarith) hC.le
      _ = _ := by dsimp [eta];field_simp [hC.ne'];ring
  filter_upwards [eventually_all.mpr ht,hmass,eventually_ge_atTop N0] with N hT hM hN
  intro hev k
  have hpay := hQ q hq a omega ha hwa N hN hev k
  have hmasscost := (mul_le_mul_of_nonneg_left hM.le
    (by positivity : 0≤8*width n/cutoff^2+eta)).trans hcost
  change K k-eps<_
  change (∑ i∈F k,testSum N r i)≤_ at hpay
  linarith only [hT k,hpay,hmasscost,heps]

theorem exists_original_later_payment (eps : ℝ) (heps : 0<eps) :
    ∃ n0 : ℕ,∀ n≥n0,∃ E : ℝ,0<E ∧ ∀ e : ℚ,0<e → (e:ℝ)<E →
    ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,∀ a omega : ℝ,a≤1/100 → omega≤a →
    ∀ᶠ N : ℕ in atTop,Even N → original-eps<total n (bank e q a) omega N := by
  obtain ⟨n0,hn⟩ := exists_each_epoch (eps/8) (by positivity)
  refine ⟨n0,?_⟩
  intro n hnn
  obtain ⟨E,hE,he⟩ := hn n hnn
  refine ⟨E,hE,?_⟩
  intro e hep hee
  obtain ⟨q0,hq0,hq⟩ := he e hep hee
  refine ⟨q0,hq0,?_⟩
  intro q hqq a omega ha hwa
  filter_upwards [hq q hqq a omega ha hwa] with N h
  intro hev
  have hsum := Finset.sum_lt_sum
    (fun k (_ : k∈(Finset.univ : Finset (Fin 8)))=>(h hev k).le)
    ⟨(0:Fin 8),Finset.mem_univ _,h hev 0⟩
  rw [Finset.sum_sub_distrib,telescope] at hsum
  have hfee : (∑ _k : Fin 8,eps/8)=eps := by simp [nsmul_eq_mul] <;> ring
  rw [hfee] at hsum
  exact (sub_le_sub_right P2OriginalLaterSixthStageMass.seven_slots_le_eight_stage_integrals eps).trans_lt hsum

end
end ImbalancedChen.P4AOriginalOrderedLaterPaid
