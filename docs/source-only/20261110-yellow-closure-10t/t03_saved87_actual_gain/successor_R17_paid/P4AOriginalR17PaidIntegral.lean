import ImbalancedChen.P4AOriginalR17Full87SavedEndpoint
import ImbalancedChen.P4AOrderedThirdCommonSchedule

/-! The complete original eighth integral on the actual R17 rectangle
coefficient. The rectangle construction chooses the single beta. Its
physical cutoff also selects the third root used by the ordinary gain. -/
namespace ImbalancedChen.P4AOriginalR17PaidIntegral
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)
open P4AOriginalR17EighthParent (orderedSixth)
open P4AOriginalR17Full87SavedEndpoint (original_ordinary_source)
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep alignedWidth)
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87RawChronology (cutoff rawRoot)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open P4AOriginalVariableFifthPhysicalLedger (raw)
open P5OriginalCommonPositivePresieve (normalize)

/-- The actual sixth ordinary source and the actual eighth small-carrier
correction use the same physical third cutoff. -/
def integralUpper (r n : ℕ) (e : ℚ) (q : ℕ) (a omega eta u_c : ℝ) (N : ℕ) : ℝ :=
  let z := cutoff N
  let w := (N:ℝ)^omega
  let scale := singularSeries N / Real.log (N:ℝ)
  raw (orderedSixth n e q a omega N) N N 0 z -
    (∑ c : Cell,cellIntegral c)*scale -
    p4aActualPresieveCorrection (keep r n e q a omega N) N N w z + (eta+u_c)*scale

/-- All thresholds precede the target. The compiler chooses beta and
the aligned mesh after a. Its actual density and both count bounds use
the very same Q and rho, including in the distribution error. -/
theorem original_signed_density_and_count (eta : ℝ) (heta : 0<eta) :
    ∃ r0 : ℕ, ∀ r≥r0, ∃ n0 : ℕ, ∀ n≥n0,
    ∃ e0 : ℝ, 0<e0 ∧ ∀ e : ℚ, 0<e → (e:ℝ)<e0 →
    ∃ q0 : ℕ, 0<q0 ∧ ∀ q≥q0, ∀ a : ℝ, 0<a → a≤1/100 →
    ∀ nu v u_c betaMax : ℝ, 0<nu → 0<v → nu*v=19/96 → 0<u_c → 0<betaMax →
    ∃ beta : ℝ, 0<beta ∧ beta<1/8 ∧ beta<betaMax ∧ beta^2<v ∧
      nu*beta^2<a ∧ nu*beta<1/1000 ∧
    ∃ k N0 : ℕ, 2≤N0 ∧ ∀ N≥N0, Even N →
      let omega := nu*beta^2
      let tau := alignedWidth (data e q a).m k
      let w := (N:ℝ)^omega
      let z := cutoff N
      let L := (N:ℝ)^(nu*beta)
      let Q := moduli N w
      let rho := coefficient r n e q a omega N tau L
      let f := keep r n e q a omega N
      let U := integralUpper r n e q a omega eta u_c N
      normalize N (rawRoot (fresh (data e q a) omega N) N) <
          (∑ i,currentUpperEighteenPositive i)+eta ∧
      ((N:ℝ)/Real.log (N:ℝ))*P4AFiniteCapTaggedConstructor.compilerExpense f (fun _ => []) N N w z tau L
          < u_c*singularNormalization N ∧
      physicalDensitySum Q rho<U ∧
      (∀ m : ℕ,rho m≠0 → (m:ℝ)<(N:ℝ)^(599/1000:ℝ)) ∧
      ∀ b T : ℝ,0<b → b<1 → 0<T → (Nat.ceil z:ℝ)≤T^(b/(1+b)) →
        let mass := ((realHalfProductSource b N T).card:ℝ)
        let err := realPhysicalDistributionError b N T Q rho
        (RealB b N:ℝ)≤mass*physicalDensitySum Q rho+err+(Nat.ceil z:ℝ)+(T+1) ∧
        (RealB b N:ℝ)≤mass*U+err+(Nat.ceil z:ℝ)+(T+1) := by
  obtain ⟨r0,hr⟩ := original_ordinary_source eta heta
  obtain ⟨Ec,hEc,hcomp⟩ := P4AOrderedThirdCommonSchedule.common_schedule eta heta
  refine ⟨r0,?_⟩
  intro r hrr
  obtain ⟨n0,hn⟩ := hr r hrr
  refine ⟨n0,?_⟩
  intro n hnn
  obtain ⟨Eg,hEg,hgain⟩ := hn n hnn
  refine ⟨min Eg Ec,lt_min hEg hEc,?_⟩
  intro e he he0
  obtain ⟨qg,hqg,hg⟩ := hgain e he (he0.trans_le (min_le_left _ _))
  obtain ⟨qc,_,hc⟩ := hcomp e (by exact_mod_cast he) (he0.trans_le (min_le_right _ _))
  refine ⟨max qg qc,hqg.trans_le (le_max_left _ _),?_⟩
  intro q hq a ha ha1 nu v u_c betaMax hnu hv hvv hu hm
  obtain ⟨Ng,hNg,hG⟩ := hg q ((le_max_left _ _).trans hq) a ha1
  obtain ⟨beta,hp,h8,hmax,hsq,hwa,hL,k,Nc,hNc,hC⟩ :=
    hc q ((le_max_right _ _).trans hq) a ha r n nu v u_c betaMax hnu hv hvv hu hm
  refine ⟨beta,hp,h8,hmax,hsq,hwa,hL,k,max Ng Nc,hNg.trans (le_max_left _ _),?_⟩
  intro N hN hEven
  have hNgN := (le_max_left Ng Nc).trans hN
  have hNcN := (le_max_right Ng Nc).trans hN
  have h2 := hNg.trans hNgN
  have hNr : 1<(N:ℝ) := by exact_mod_cast (show 1<N by omega)
  let omega := nu*beta^2
  let w := (N:ℝ)^omega
  let z := cutoff N
  let tau := alignedWidth (data e q a).m k
  let L := (N:ℝ)^(nu*beta)
  let Q := moduli N w
  let rho := coefficient r n e q a omega N tau L
  let f := keep r n e q a omega N
  let X := raw (orderedSixth n e q a omega N) N N 0 z
  let Y := p4aReserveRawDensity f N N 0 z
  let C := p4aActualPresieveCorrection f N N w z
  let scale := singularSeries N / Real.log (N:ℝ)
  have hmu : (N:ℝ)^VariableEnvelope.mu≤z :=
    Real.rpow_le_rpow_of_exponent_le hNr.le (by norm_num [VariableEnvelope.mu])
  have hz : z≤(N:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr.le
      (show (19/96:ℝ)≤1 by norm_num)
  have hraw := hG N hNgN hEven omega hwa.le N z hmu hz
  change (∑ c : Cell,cellIntegral c)-eta < normalize N (X-Y) at hraw
  have hcancel : normalize N (X-Y)*scale=X-Y := by
    dsimp only [normalize,scale]
    field_simp [(singularSeries_pos N).ne',(Real.log_pos hNr).ne'] <;> ring
  have hs := mul_lt_mul_of_pos_right hraw (densityScale_pos h2)
  change ((∑ c : Cell,cellIntegral c)-eta)*scale < normalize N (X-Y)*scale at hs
  rw [hcancel] at hs
  obtain ⟨hroot,hspend,hdens,hstrict,hcount⟩ := hC N hNcN hEven
  change physicalDensitySum Q rho < Y-C+u_c*scale at hdens
  have hU : physicalDensitySum Q rho < integralUpper r n e q a omega eta u_c N := by
    change physicalDensitySum Q rho < X-(∑ c : Cell,cellIntegral c)*scale-C+(eta+u_c)*scale
    linarith only [hs,hdens]
  refine ⟨hroot,hspend,hU,hstrict,?_⟩
  intro b T hb hb1 hT hgate
  have hR := hcount b T hb hb1 hT hgate
  have hcost := mul_le_mul_of_nonneg_left hU.le
    (Nat.cast_nonneg (realHalfProductSource b N T).card : 0≤((realHalfProductSource b N T).card:ℝ))
  refine ⟨hR,hR.trans ?_⟩
  exact add_le_add_right (add_le_add_right (add_le_add_right hcost _) _) _

end
end ImbalancedChen.P4AOriginalR17PaidIntegral

