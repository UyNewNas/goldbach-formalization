import ImbalancedChen.P4BOriginalCollisionKernel

/-! Uniform arithmetic collision payment at every actual HB frequency.
The outer parameters omega and its rank bound precede N. Every dyadic
rectangle, complementary fibre and frequency may be chosen afterward. -/
namespace ImbalancedChen.P4BOriginalCollisionModes
noncomputable section
open Classical Filter MeasureTheory
open scoped BigOperators
open ImbalancedChen.PrimeProducts.MellinInsertion20261028 (exactDiscrepancy)
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (products free grouped grouped_eq_free)
open P4BOriginalCollisionKernel (Y bound kernel_power full_difference)
open P4AHeldTaggedCompilerSupport (J0)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct hbSlots hbSlots_norm_le hb_fibre_card_le)
open P5Z.ActualRoughHeathBrownWords (Role)
open P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode physicalPhase_occurrenceMode)
open P5Z.ActualEuclideanPhysicalFourier (physicalPhase_norm)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le scaleFactor scaleFactor_one_le)
open P5Z.ProperPowerPhysicalPolynomialPayment (tau_word_rank_subpower)
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle)
open P4BUpperPairOrderedRowGeometry (integerProfile pairOwner blockScales)
open P4BOriginalHighRankPostModulusMass (block_rect)
open P4BOuterRampRoughness (baseline)

theorem grouped_complex (P : Params) (hN : 1<P.N) (x U eta : ℝ) (F : ℕ→ℂ) :
    (grouped P x U eta (fun t => (F t).re):ℂ)+Complex.I*(grouped P x U eta (fun t => (F t).im):ℂ)=
      ∑ t∈products P,(free P t:ℂ)*F t := by
  rw [grouped_eq_free P hN,grouped_eq_free P hN]
  push_cast
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun t _ => by
    have h := Complex.re_add_im (F t)
    linear_combination (free P t:ℂ)*h)

theorem live_products {u v N : ℕ} {b kap s kap0 : ℝ} (hb : 0<b) (hk : 0<kap) (hs : 0<s)
    (hg : 2*s≤baseline b kap-19/96) (hm : u+v≤12) (cj ck : ℕ) (bs : Fin (u+v)→Block)
    (I : Finset (Fin (u+v)→ℕ)) (hi : I⊆rectangle bs)
    (live : ∃ y∈I,integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0) :
    ∀ y∈I,(∀ j,0<y j) ∧ completeProduct y∈Finset.Icc 1 (Y N) := by
  obtain ⟨y,hy,hnz⟩ := live
  have hg' : 2*s≤baseline b kap-1*(19/96:ℝ) := by simpa only [one_mul] using hg
  intro z hz
  obtain ⟨hpos,hr⟩ := P4BArbitraryWidthUpperBlockGeometry.rectangle_counting_scale hb hk
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) hs hg' (pairOwner u v) bs
    (![P5Z.ExactOriginalSmoothDyadicPartition.R cj,P5Z.ExactOriginalSmoothDyadicPartition.R ck]) kap0
    hm ⟨y,block_rect (hi hy),hnz⟩ (block_rect (hi hz))
  refine ⟨hpos,Finset.mem_Icc.mpr ⟨Finset.prod_pos (fun i _ => hpos i),Nat.le_floor ?_⟩⟩
  change (completeProduct z:ℝ)≤6*countingScale N
  linarith only [hr,show 0≤countingScale N from by dsimp [countingScale,scaleFactor]; positivity]

theorem exists_mode_cost (omega loss : ℝ) (ho : 0<omega) (hloss : 0<loss) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,∀ (P : Params),P.N=N → P.omega=omega → 0≤P.e →
      P.ell+P.T*(J0 P.omega:ℝ)<1/1000 →
      ∀ {d : ℕ},d≤12 → ∀ (I : Finset (Fin d→ℕ)),
      (∀ y∈I,(∀ j,0<y j) ∧ completeProduct y∈Finset.Icc 1 (Y N)) →
      ∀ (Z : ℝ) (ys : Fin d→ℝ) (rs : Fin d→Role) (U xi : Fin d→ℝ),
      let w := fun y => hbSlots Z ys rs y*occurrenceMode U y xi
      ‖exactDiscrepancy I (products P) (fun t => (free P t:ℂ)) completeProduct N w-
        exactDiscrepancy I P.S (fun t => (P.rho t:ℂ)) completeProduct N w‖≤
        C*(N:ℝ)^(1-omega+loss)*logScale (countingScale N)^12 := by
  let eps := loss/2
  have heps : 0<eps := by dsimp [eps]; positivity
  obtain ⟨D,hD,Hd⟩ := tau_word_rank_subpower 12 heps
  let G := D*(6*scaleFactor)^eps
  let E := 2*(1+6*scaleFactor)
  have hf : 0<scaleFactor := zero_lt_one.trans_le scaleFactor_one_le
  have hG : 0<G := by dsimp [G]; positivity
  have hE : 0<E := by dsimp [E]; positivity
  let J := ((J0 omega).factorial:ℝ)
  have hJ : 0<J := by exact_mod_cast Nat.factorial_pos (J0 omega)
  refine ⟨J*G*E,by positivity,?_⟩
  filter_upwards [kernel_power omega eps ho heps,eventually_ge_atTop (2:ℕ)] with N hK hN
  intro P hPN hom hpe hbudget d hd I hp Z ys rs U xi
  let w := fun y : Fin d→ℕ => hbSlots Z ys rs y*occurrenceMode U y xi
  let L := logScale (countingScale N)
  have hX := countingScale_one_le (N:=N) (by omega)
  have hL : 1≤L := logScale_one_le hX
  have hNr : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hY : ((Y N):ℝ)≤(6*scaleFactor)*(N:ℝ) :=
    (Nat.floor_le (show 0≤6*countingScale N by linarith)).trans_eq (by dsimp [countingScale]; ring)
  have hy (y) (hy : y∈I) : ‖w y‖≤L^12 := by
    dsimp only [w]
    rw [norm_mul,←physicalPhase_occurrenceMode,physicalPhase_norm,mul_one]
    apply (hbSlots_norm_le hX Z ys rs y (hp y hy).1 _).trans (pow_le_pow_right₀ hL hd)
    exact (Nat.cast_le.mpr (Finset.mem_Icc.mp (hp y hy).2).2).trans
      (Nat.floor_le (by linarith))
  let B := (G*(N:ℝ)^eps)*L^12
  have hB : 0≤B := by dsimp [B]; positivity
  have HM (x : ℕ) (hx : x∈Finset.Icc 1 (Y N)) :
      (∑ y∈I.filter (fun y => completeProduct y=x),‖w y‖)≤B := by
    obtain ⟨hx1,hxY⟩ := Finset.mem_Icc.mp hx
    have hx0 : (x:ℝ)≤(6*scaleFactor)*(N:ℝ) := (Nat.cast_le.mpr hxY).trans hY
    have H := (Hd x d hx1 hd).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hx0 heps.le) hD.le)
    rw [Real.mul_rpow (by positivity) hNr.le] at H
    have hc : ((I.filter (fun y => completeProduct y=x)).card:ℝ)≤G*(N:ℝ)^eps := by
      apply (Nat.cast_le.mpr (hb_fibre_card_le I x hx1)).trans
      simpa only [G,mul_assoc] using H
    apply (Finset.sum_le_sum (fun y hy' => hy y (Finset.mem_filter.mp hy').1)).trans
    simpa [B,nsmul_eq_mul] using mul_le_mul_of_nonneg_right hc (pow_nonneg (zero_le_one.trans hL) 12)
  have H := full_difference P (by omega) hpe (by rwa [hom]) hbudget I completeProduct w (Y N)
    (fun y hy' => (hp y hy').2) hB HM
  rw [hPN,hom] at H
  apply H.trans
  apply (mul_le_mul_of_nonneg_left (hK P hPN hom) (mul_nonneg hJ.le hB)).trans
  have hpow : (N:ℝ)^eps*((N:ℝ)*(N:ℝ)^(eps-omega))=(N:ℝ)^(1-omega+loss) := by
    calc
      _=(N:ℝ)^eps*((N:ℝ)^(1:ℝ)*(N:ℝ)^(eps-omega)) := by rw [Real.rpow_one]
      _=(N:ℝ)^(eps+(1+(eps-omega))) := by rw [←Real.rpow_add hNr,←Real.rpow_add hNr]
      _=_ := by congr 1; dsimp [eps]; ring
  change J*B*(E*(N:ℝ)*(N:ℝ)^(eps-omega))≤_
  calc
    _=(J*G*E)*((N:ℝ)^eps*((N:ℝ)*(N:ℝ)^(eps-omega)))*L^12 := by dsimp [B]; ring
    _=_ := by rw [hpow]

end
end ImbalancedChen.P4BOriginalCollisionModes
