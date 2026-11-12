import ImbalancedChen.P4AOriginalFiniteAll22LatePayments
import ImbalancedChen.P4AOriginalFiniteAll22PhysicalLedger

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Actual final finite-bank Q/rho/count,with all17 lower late slots,the true
two upper slots and the positive root on one cofinal schedule. The sole
unpaid scalar remains the explicitly defined ACTUAL low early0/1/2
defect. Its sign is NOT a premise. The final All22 K theorem may only
remove it after the separate actual new-parent supplier is constructed.
-/
namespace ImbalancedChen.P4AOriginalFiniteAll22CommonCoefficient
noncomputable section
open scoped Classical BigOperators
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalFiniteAll22RawLedger
  (finalPolicy lowerEarly lowerSaved lowerEleven lowerLater lowerEighth upperFallback lowerEarlyDefect
    lowerEarlySlots upperFallbackSlots)
open P4AOriginalFiniteAll22Slots (originalScalar laterSlots eighthSlots)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AOriginalFull87HistoryCore (width)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AOriginalFull87CompiledCounting (moduli)

def upper (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega eps u_c : ℝ) (N : ℕ) : ℝ :=
  (originalScalar+lowerEarlyDefect n e q a omega N+6*eps+u_c)*
    (singularSeries N/Real.log (N:ℝ))-
      p4aActualPresieveCorrection (F (bank m) (width r) n (data e q a) omega N)
        N N ((N:ℝ)^omega) (cutoff N)

private theorem actual_scalar_read (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega eps : ℝ) (N : ℕ)
    (hp : normalize N (rawRoot (P4AOrderedThirdArithmeticOccurrence.fresh (data e q a) omega N) N)<
      (∑ i,currentUpperEighteenPositive i)+eps)
    (h4 : currentUpperEighteenGains 3-eps<lowerSaved n e q a omega N)
    (h7 : P4AOriginalElevenOrderedPayment.originalFloor-eps<lowerEleven n e q a omega N)
    (hl : laterSlots-eps<lowerLater n e q a omega N)
    (hi : eighthSlots-eps<lowerEighth r n e q a omega N)
    (hu : upperFallbackSlots-eps<upperFallback m r n e q a omega N) :
    normalize N (rawRoot (finalPolicy m r n e q a omega N) N)<
      originalScalar+lowerEarlyDefect n e q a omega N+6*eps := by
  rw [P4AOriginalFiniteAll22RawLedger.exact_all22_telescope]
  unfold originalScalar lowerEarlyDefect
  linarith only [hp,h4,h7,hl,hi,hu]

/-- This is an unconditional ACTUAL physical/count endpoint with a named
actual remainder. It is not the final K bound and assumes no bound at all
on that remainder. A single beta and aligned rectangle serve every term. -/
theorem original_same_rho_with_actual_early_defect (eps : ℝ) (heps : 0<eps) :
    ∃ m0 : ℕ,∀ m≥m0,∃ r0 : ℕ,∀ r≥r0,∃ n0 : ℕ,∀ n≥n0,
    ∃ E : ℝ,0<E ∧ ∀ e : ℚ,0<e → (e:ℝ)<E → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,
    ∀ a : ℝ,0<a → a≤1/800 → ∀ nu v u_c betaMax : ℝ,
    0<nu → 0<v → nu*v=19/96 → 0<u_c → 0<betaMax →
    ∃ beta : ℝ,0<beta ∧ beta<1/8 ∧ beta<betaMax ∧ beta^2<v ∧
      nu*beta^2<a ∧ nu*beta<1/1000 ∧
    ∃ k N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N →
      let omega := nu*beta^2
      let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
      let w := (N:ℝ)^omega
      let z := cutoff N
      let L := (N:ℝ)^(nu*beta)
      let Q := moduli N w
      let rho := P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L
      let f := F (bank m) (width r) n (data e q a) omega N
      ((N:ℝ)/Real.log (N:ℝ))*P4AFiniteCapTaggedConstructor.compilerExpense f (fun _ => []) N N w z tau L
          <u_c*singularNormalization N ∧
      physicalDensitySum Q rho<upper m r n e q a omega eps u_c N ∧
      (∀ x : ℕ,rho x≠0 → (x:ℝ)<(N:ℝ)^(599/1000:ℝ)) ∧
      ∀ b T : ℝ,0<b → b<1 → 0<T → (Nat.ceil z:ℝ)≤T^(b/(1+b)) →
        (RealB b N:ℝ)≤((realHalfProductSource b N T).card:ℝ)*upper m r n e q a omega eps u_c N+
          realPhysicalDistributionError b N T Q rho+(Nat.ceil z:ℝ)+(T+1) := by
  obtain ⟨m0,hM⟩ := P4AOriginalFiniteFallbackTerminal.joint eps eps heps heps
  obtain ⟨r0,hR⟩ := P4AOriginalFiniteAll22LatePayments.exists_common_late_payments eps heps
  refine ⟨m0,?_⟩
  intro m hm
  obtain ⟨EU,hEU,hUE⟩ := hM m hm
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨n0,hN⟩ := hR r hr
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨EL,hEL,hLE⟩ := hN n hn
  refine ⟨min EU EL,lt_min hEU hEL,?_⟩
  intro e he heE
  obtain ⟨qU,hqU,hUQ⟩ := hUE e (by exact_mod_cast he) (heE.trans_le (min_le_left _ _))
  obtain ⟨qL,hqL,hLQ⟩ := hLE e he (heE.trans_le (min_le_right _ _))
  refine ⟨max qU qL,hqU.trans_le (le_max_left _ _),?_⟩
  intro q hq a ha ha8 nu v u_c betaMax hnu hv hcut hu hmax
  obtain ⟨beta,hb,hb8,hbm,hbs,hba,hbl,k,NU,hNU,hUN⟩ :=
    hUQ q ((le_max_left _ _).trans hq) a ha ha8 r n nu v u_c betaMax hnu hv hcut hu hmax
  let omega := nu*beta^2
  obtain ⟨NL,hNL,hLN⟩ := hLQ q ((le_max_right _ _).trans hq) a omega ha8 hba.le
  refine ⟨beta,hb,hb8,hbm,hbs,hba,hbl,k,max NU NL,hNU.trans (le_max_left _ _),?_⟩
  intro N hNN hev
  have hNU' := (le_max_left NU NL).trans hNN
  have hNL' := (le_max_right NU NL).trans hNN
  have h2 := hNU.trans hNU'
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  obtain ⟨hupper,hpos,hspend,hdens,hstrict,hcount⟩ := hUN N hNU' hev
  obtain ⟨h4,h7,hl,hi⟩ := hLN N hNL' hev
  have hs := actual_scalar_read m r n e q a omega eps N hpos h4 h7 hl hi hupper
  let scale := singularSeries N/Real.log (N:ℝ)
  have hcancel : normalize N (rawRoot (finalPolicy m r n e q a omega N) N)*scale=
      rawRoot (finalPolicy m r n e q a omega N) N := by
    unfold normalize scale
    field_simp [(singularSeries_pos N).ne',(Real.log_pos hNr).ne']
    <;> ring
  have hraw := mul_lt_mul_of_pos_right hs (densityScale_pos h2)
  change normalize N (rawRoot (finalPolicy m r n e q a omega N) N)*scale<_ at hraw
  rw [hcancel] at hraw
  rw [P4AOriginalFiniteAll22PhysicalLedger.reserve_raw_is_actual_final] at hdens
  have hbound : physicalDensitySum (moduli N ((N:ℝ)^omega))
      (P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N
        (alignedWidth (jointIndex (bank m) (data e q a).m) k) ((N:ℝ)^(nu*beta)))<
      upper m r n e q a omega eps u_c N := by
    let corr := p4aActualPresieveCorrection
      (F (bank m) (width r) n (data e q a) omega N) N N ((N:ℝ)^omega) (cutoff N)
    calc
      _ < rawRoot (finalPolicy m r n e q a omega N) N-corr+u_c*scale := hdens
      _ = rawRoot (finalPolicy m r n e q a omega N) N+(u_c*scale-corr) := by ring
      _ < (originalScalar+lowerEarlyDefect n e q a omega N+6*eps)*scale+
          (u_c*scale-corr) := add_lt_add_right hraw _
      _ = upper m r n e q a omega eps u_c N := by
        unfold upper
        dsimp only [corr,scale]
        ring
  refine ⟨hspend,hbound,hstrict,?_⟩
  intro b T hb' hb1 hT hgate
  have hc := hcount b T hb' hb1 hT hgate
  have hmul := mul_le_mul_of_nonneg_left hbound.le (Nat.cast_nonneg (realHalfProductSource b N T).card)
  exact hc.trans (add_le_add_right (add_le_add_right (add_le_add_right hmul _) _) _)

end
end ImbalancedChen.P4AOriginalFiniteAll22CommonCoefficient
