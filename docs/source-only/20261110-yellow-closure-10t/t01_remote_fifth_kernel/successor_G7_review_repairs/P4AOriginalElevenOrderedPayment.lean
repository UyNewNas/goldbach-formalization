import ImbalancedChen.P4AOriginalElevenOrderedSum

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Original G7 replacement floor, with arbitrary positive tolerance, on the
ACTUAL updated whole-third/R17 fifth predecessor and the same target,
cutoff, singular series and ordinary signed source. Every original2631
six-dimensional simplex enters through the proved continuous test floor.
The full admitted sum, including all outside-trim words, is retained.
All22 count/ledger insertion and remote proof validation remain separate.
-/
namespace ImbalancedChen.P4AOriginalElevenOrderedPayment
noncomputable section
open Filter VariableEnvelope
open scoped Classical BigOperators Topology
open P2OriginalSixthMomentRow (cutoff)
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)
open P4AOriginalElevenActualCommonHistory (bank)
open P4AOriginalElevenOrderedSum (gain)

def originalFloor : ℝ := (1208544915921356327515701:ℝ)/(2:ℝ)^96

/-- One resolution schedule precedes the early geometric buffer. The mesh
precedes the late physical cutoff and target. The early a and late omega
remain distinct. No target-level saving or licence occurs as a premise. -/
theorem exists_original_G7_ordered_payment (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ n0 : ℕ,∀ n≥n0,∃ e0 : ℝ,0<e0 ∧
    ∀ e : ℚ,0<e → (e:ℝ)<e0 → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,
    ∀ a omega : ℝ,a≤1/100 → omega≤a →
    ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N → originalFloor-epsilon<gain n (bank e q a) omega N := by
  obtain ⟨r,hr⟩ := P2OriginalSixthInnerPrimeTests.exists_continuous_original_G7_floor
    (epsilon/3) (by positivity)
  let L : ℝ := ∏ _j : Fin 6,Real.log (mu/cutoff)
  let C : ℝ := |L|+1
  have hC : 0<C := by dsimp [C]; positivity
  have hmass := tendsto_actualPrimeBoxMass (fun _ : Fin 6 => cutoff) (fun _ => mu)
    (fun _ => by norm_num [cutoff]) (fun _ => by norm_num [cutoff,mu])
  have hLC : L<C := by dsimp [C]; linarith [le_abs_self L]
  obtain ⟨NM,hNM⟩ := eventually_atTop.mp (hmass.eventually (gt_mem_nhds hLC))
  let eta : ℝ := epsilon/(12*C)
  have heta : 0<eta := by dsimp [eta]; positivity
  obtain ⟨NS,hNS,nS,hS⟩ := P4AOriginalElevenOrderedSum.exists_ordered_G7_sum_lower r eta heta
  have hwidth : Tendsto (fun n : ℕ => 8*width n/cutoff^2) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_div] using (width_tendsto.const_mul (8:ℝ)).div_const (cutoff^2)
  obtain ⟨nW,hnW⟩ := eventually_atTop.mp (hwidth.eventually (gt_mem_nhds heta))
  have htlim := tendsto_finsetSum (Finset.univ : Finset (Fin 11))
    (fun i _ => P2OriginalSixthInnerPrimeTests.testSum_tendsto r i)
  have hTI : originalFloor-2*epsilon/3<∑ i : Fin 11,P2OriginalSixthInnerPrimeTests.testIntegral r i := by
    change (1208544915921356327515701:ℝ)/(2:ℝ)^96-2*epsilon/3<_
    linarith
  obtain ⟨NT,hNT⟩ := eventually_atTop.mp (htlim.eventually (lt_mem_nhds hTI))
  refine ⟨max nS nW,?_⟩
  intro n hn
  have hwpos : 0≤width n := (width_pos n).le
  obtain ⟨e0,he0,hE⟩ := hS n ((le_max_left _ _).trans hn)
  refine ⟨e0,he0,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hQ⟩ := hE e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hq a omega ha hwa
  refine ⟨max NS (max NM NT),hNS.trans (le_max_left _ _),?_⟩
  intro N hN hev
  have hNS' := (le_max_left NS (max NM NT)).trans hN
  have hNM' := ((le_max_left NM NT).trans (le_max_right NS (max NM NT))).trans hN
  have hNT' := ((le_max_right NM NT).trans (le_max_right NS (max NM NT))).trans hN
  have hpaid := hQ q hq a omega ha hwa N hNS' hev
  have htests := hNT N hNT'
  have hM : actualPrimeBoxMass N (fun _ : Fin 6 => cutoff) (fun _ => mu)≤C := (hNM N hNM').le
  have hW : 8*width n/cutoff^2<eta := hnW n ((le_max_right nS nW).trans hn)
  have hE0 : 0≤8*width n/cutoff^2+eta := by positivity
  have herr : (8*width n/cutoff^2+eta)*actualPrimeBoxMass N
      (fun _ : Fin 6 => cutoff) (fun _ => mu)≤epsilon/6 := by
    calc
      _ ≤ (8*width n/cutoff^2+eta)*C := mul_le_mul_of_nonneg_left hM hE0
      _ ≤ (2*eta)*C := mul_le_mul_of_nonneg_right (by linarith) hC.le
      _ = _ := by dsimp [eta]; field_simp [hC.ne']; ring
  linarith

end
end ImbalancedChen.P4AOriginalElevenOrderedPayment
