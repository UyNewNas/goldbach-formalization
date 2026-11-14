import ImbalancedChen.Part3OriginalNativeCriticalTransport

/-! Quantify the cost of one actual returned prefix in the normalized
critical induction. The six edges share one coefficient budget. -/
namespace ImbalancedChen.Part3.OriginalNativeCriticalChild20261113
noncomputable section
open Finset Real
open scoped Classical BigOperators
open OriginalNativeCriticalPrices20261113 (height normPrice)
open OriginalSwitchedScaleContraction20261113 (kappa normalized_contribution transports)

theorem child {A B D M Q P ε : ℝ} (ap : 0≤A) (bp : 0<B) (dp : 0<D) (mp : 0<M)
    (qp : 0<Q) (ep : 0<ε) (pp : 0≤P) (small : height M≤B) (shrink : B≤kappa*(Q/D))
    (q1 : 1≤Q) (budget : 2*(6*A)*(kappa/D)^ε≤1/2) :
    let W := Q^2/M
    let Z := Q^2/(D*M)
    Real.sqrt (W/Z)*A*(Real.sqrt (Z/(B^2/M))*(P*normPrice M B ε))≤
      P*normPrice M Q ε/12 := by
  let H := height M
  have h1 : 1≤H := le_max_left _ _
  have hp := zero_lt_one.trans_le h1
  have b1 := h1.trans small
  have cost := normalized_contribution (A:=6*A) (by positivity) qp bp mp.le dp ep.le
    ((le_max_right 1 M).trans small) shrink budget
  have pow : (B/Q)^ε*(Q*H)^ε=(B*H)^ε := by
    rw [←Real.mul_rpow (div_nonneg bp.le qp.le) (mul_nonneg qp.le hp.le),
      show B/Q*(Q*H)=B*H by field_simp [qp.ne'] <;> ring]
  have clean : (6*A)*(B/Q)^ε*(Q*(B+M))≤(1/2)*(B*(Q+M)) := by
    apply (div_le_iff₀ (mul_pos bp (add_pos qp mp))).mp
    exact (show (6*A)*(B/Q)^ε*(Q*(B+M))/(B*(Q+M))=(6*A)*(B/Q)^ε*(Q*(B+M)/(B*(Q+M))) by ring).le.trans cost
  have factor := mul_le_mul_of_nonneg_right clean (mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (mul_nonneg qp.le hp.le) _) mp.le) pp)
  have phy : (6*A)*(Q*(B+M))*((B*H)^ε*M*P)≤(1/2)*(B*(Q+M))*((Q*H)^ε*M*P) := by
    rw [←pow]
    nlinarith only [factor]
  have tr := transports qp bp dp mp
  dsimp only
  calc
    _ = (Q/B)*A*(P*normPrice M B ε) := by
      calc
        _ = (Real.sqrt ((Q^2/M)/(Q^2/(D*M)))*Real.sqrt ((Q^2/(D*M))/(B^2/M)))*A*(P*normPrice M B ε) := by ring
        _ = _ := by rw [tr]
    _ ≤ _ := by
      dsimp only [normPrice]
      rw [max_eq_right b1,max_eq_right q1]
      apply (mul_le_mul_iff_left₀ bp).mp
      rw [show Q/B*A*(P*((B*height M)^ε*(B+M)*M))*B=
        Q*A*P*((B*height M)^ε*(B+M)*M) by field_simp [bp.ne'] <;> ring]
      dsimp only [H] at phy
      nlinarith only [phy]

end
end ImbalancedChen.Part3.OriginalNativeCriticalChild20261113

