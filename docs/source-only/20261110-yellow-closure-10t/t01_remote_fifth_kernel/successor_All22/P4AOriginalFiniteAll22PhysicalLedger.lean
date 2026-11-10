import ImbalancedChen.P4AOriginalFiniteAll22RawLedger

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Exact read of the all22 telescope by T04's FINAL finite upper-bank
rectangle coefficient. Its actual presieve correction and compiler
expense retain the same false policy,the same N and the same carrier.
No component bound or final K bound is assumed or asserted here.
-/
namespace ImbalancedChen.P4AOriginalFiniteAll22PhysicalLedger
noncomputable section
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFiniteAll22RawLedger
  (finalPolicy lowerEarly lowerSaved lowerEleven lowerLater lowerEighth upperFallback)
open P4AFallbackCanonicalBanks (bank)

def scalar (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) : ℝ :=
  normalize N (rawRoot (P4AOrderedThirdArithmeticOccurrence.fresh (data e q a) omega N) N)-
    lowerEarly n e q a omega N-lowerSaved n e q a omega N-lowerEleven n e q a omega N-
    lowerLater n e q a omega N-lowerEighth r n e q a omega N-upperFallback m r n e q a omega N

def upper (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega u_c : ℝ) (N : ℕ) : ℝ :=
  scalar m r n e q a omega N*(singularSeries N/Real.log (N:ℝ))-
    p4aActualPresieveCorrection
      (P4AOriginalFiniteFallbackPolicy.F (bank m) (width r) n (data e q a) omega N)
      N N ((N:ℝ)^omega) (cutoff N)+u_c*(singularSeries N/Real.log (N:ℝ))

theorem reserve_raw_is_actual_final (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :
    p4aReserveRawDensity
      (P4AOriginalFiniteFallbackPolicy.F (bank m) (width r) n (data e q a) omega N)
      N N 0 (cutoff N)=rawRoot (finalPolicy m r n e q a omega N) N := by
  rfl

/-- This is exactly the upper scalar occurring in the finite bank's
same-Q/rho density-and-count theorem. There is one compiler reserve and
one actual positive-presieve correction,with no hypothetical policy swap. -/
theorem exact_same_coefficient_upper (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega u_c : ℝ)
    {N : ℕ} (hN : 2≤N) :
    let f := P4AOriginalFiniteFallbackPolicy.F (bank m) (width r) n (data e q a) omega N
    p4aReserveRawDensity f N N 0 (cutoff N)-
      p4aActualPresieveCorrection f N N ((N:ℝ)^omega) (cutoff N)+
      u_c*(singularSeries N/Real.log (N:ℝ))=upper m r n e q a omega u_c N := by
  dsimp only
  rw [reserve_raw_is_actual_final]
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hcancel (x : ℝ) : normalize N x*(singularSeries N/Real.log (N:ℝ))=x := by
    unfold normalize
    field_simp [(singularSeries_pos N).ne',(Real.log_pos hNr).ne']
    <;> ring
  unfold upper scalar
  rw [←P4AOriginalFiniteAll22RawLedger.exact_all22_telescope,hcancel]

end
end ImbalancedChen.P4AOriginalFiniteAll22PhysicalLedger
