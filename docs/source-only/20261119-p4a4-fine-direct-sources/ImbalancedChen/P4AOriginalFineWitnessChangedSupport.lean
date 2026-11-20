import ImbalancedChen.P4AOriginalFiniteFallbackActualChangedSupport
import ImbalancedChen.P4AOriginalFiniteAll22FineCofinalCoefficient
import ImbalancedChen.P4AOriginalFiniteFallbackCanonical

/-!
SOURCE_ONLY / UNCOMPILED / NOT KERNEL ACCEPTED.

Apply the existing actual-cutoff changed-cell coverage to the exact
canonical bank, data, cutoff and aligned width used by the Fine/cofinal
consumer. This theorem takes its beta and k as inputs; it selects no new
witness and makes no density, signed-PP or reserve payment claim.
-/
namespace ImbalancedChen.P4AOriginalFineWitnessChangedSupport
noncomputable section
open scoped Classical BigOperators
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AUpperTaggedParityCompiler P4AHeldTaggedCompilerSupport
open P4AFull87MarkedPrimePayment P4AFull87ActualAffineDeletion P4AFull87OrdinaryAdmissionDeletion
open P2CanonicalWallFullResidualPayment
open P4AOriginalFiniteFallbackWallRate (Charts centresFor)

/-- For any already chosen Fine parameters, every actual changed tagged
cell is covered using those same parameters and the original wall charts. -/
theorem fine_witness_all_changed_seen
    (m r n q k N : ℕ) (e : ℚ) (he : 0 ≤ e) (a nu v beta : ℝ)
    (hnu : 0 < nu) (hbeta : 0 < beta)
    (hcut : nu*v = 19/96) (hbetaV : beta^2 < v) (hN : 2 ≤ N) :
    let omega := nu*beta^2
    let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
    ∀ (tags : ℕ → List Bool) (x : ℕ),
      x ∈ universe N N ((N : ℝ)^omega) (cutoff N) →
      changed (F (bank m) (width r) n (data e q a) omega N) tags N N
        ((N : ℝ)^omega) (cutoff N) tau x →
      ∃ i : Charts (bank m) (width r) n (data e q a),
        x ∈ covered N N (J0 omega) omega (19/96 : ℝ) ((J0 omega : ℝ)*tau)
          (centresFor (bank m) (width r) n (data e q a) N (J0 omega) i) := by
  dsimp only
  intro tags x hx hc
  have homega : 0 < nu*beta^2 := mul_pos hnu (sq_pos_of_pos hbeta)
  have hcap : nu*beta^2 ≤ (19/96 : ℝ) := by
    have h := mul_lt_mul_of_pos_left hbetaV hnu
    rw [hcut] at h
    exact h.le
  have htau : 0 < alignedWidth (jointIndex (bank m) (data e q a).m) k :=
    div_pos (logPrimeMeshStep_pos (by norm_num) _) (by positivity)
  have h := P4AOriginalFiniteFallbackActualChangedSupport.actual_changed_seen
    (bank m) (P4AOriginalFiniteFallbackCanonical.bounded m)
    (width r) (width_pos r) n (data e q a) he N N hN
    (nu*beta^2) (19/96 : ℝ)
    (alignedWidth (jointIndex (bank m) (data e q a).m) k)
    homega hcap htau tags (x := x) (by simpa only [cutoff] using hx)
      (by simpa only [cutoff] using hc)
  simpa only [cutoff] using h

end
end ImbalancedChen.P4AOriginalFineWitnessChangedSupport
