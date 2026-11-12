import ImbalancedChen.Part3PrescribedTensorOrbitExchange
import ImbalancedChen.Part3ComplexOrderKMellinReduction
import Batteries.Tactic.OpenPrivate

/-! The scalar K-transform of the prescribed test and the one common
finite modulus range at its original marked arithmetic row. -/
namespace ImbalancedChen.Part3.PrescribedTensorBesselGeometry20261112
noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators
open PrescribedLogTensorWindows20261112 PrescribedLogTensorCoefficients20261112
open PrescribedLogTensorExpansion20261112 PrescribedTensorOrbitExchange20261112
open ActualOppositeBesselTransform20261112 ActualOppositeBruhatCoordinates20261112
open ActualMarkedBruhatTest20261112 OriginalOppositeMarkedKuznetsov20261112
open ComplexOrderKBridgeSourceOnly ComplexOrderKMellinReduction20261025a
open OriginalSignedTraceInput20261102 OriginalCompletedReciprocalSource20261102
open OriginalSimultaneousPrefixCompletion20261102 OriginalCommonPoissonLanes20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZFourierAssembly20261102
open OriginalContinuousClassRemoval20261110 OriginalContinuousPoincarePackets20261110
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open private common_nonzero from ImbalancedChen.Part3OriginalCuspidalPoincareTrace

def transformKernel (ν : ℂ) (q : Modes) (t : ℝ) : ℂ :=
  complexOrderK (2*ν) t*orbit q t/(t:ℂ)

private theorem mellin_tail (ν : ℂ) (n : ℕ) (hn : |(2*ν).re|<(n:ℝ)+1) :
    Integrable (fun t : ℝ => t^n*‖complexOrderK (2*ν) t‖) posMeasure := by
  have H := (complexOrderK_mellin_integrable (ν:=2*ν) (s:=(n:ℂ)+1)
    (by simpa using hn)).norm
  apply H.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [add_sub_cancel_right,Complex.cpow_natCast,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_of_nonneg ht.le]

theorem transform_mass (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) (ν : ℂ) :
    (∀ q,Integrable (fun t => c ell Y q*transformKernel ν q t) posMeasure) ∧
      Summable (fun q : Modes => ∫ t,‖c ell Y q*transformKernel ν q t‖ ∂posMeasure) := by
  have I (q : Modes) : Integrable (fun t => c ell Y q*transformKernel ν q t) posMeasure :=
    ((induced_transform ν _ _ (pattern_test q.1.1 q.2.1).1 (pattern_test _ _).2.1 (pattern_test _ _).2.2
      (right_test q.1.2 q.2.2).1 (right_test _ _).2.1 (right_test _ _).2.2).1).const_mul _
  obtain ⟨n,hn⟩ := exists_nat_gt |(2*ν).re|
  let F := fun t : ℝ => t^n*‖complexOrderK (2*ν) t‖
  have IF : Integrable F posMeasure := mellin_tail ν n (by linarith)
  let δ := qFloor Y
  let B := orbitBound Y/δ^(n+1)
  have hδ : 0<δ := qFloor_pos hY
  have hB : 0≤orbitBound Y := by dsimp [orbitBound]; positivity
  have dom (q : Modes) (t : ℝ) (ht : 0<t) :
      ‖c ell Y q*transformKernel ν q t‖ ≤ (‖c ell Y q‖*B)*F t := by
    rw [transformKernel,show c ell Y q*(complexOrderK (2*ν) t*orbit q t/(t:ℂ)) =
      complexOrderK (2*ν) t*(c ell Y q*orbit q t)/(t:ℂ) by ring,norm_div,norm_mul,
      Complex.norm_real,Real.norm_of_nonneg ht.le]
    by_cases hlt : t<δ
    · rw [orbit_zero ell hY ht hlt,norm_zero,mul_zero,zero_div]
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (div_nonneg hB (pow_nonneg hδ.le _)))
        (mul_nonneg (pow_nonneg ht.le _) (norm_nonneg _))
    · have e : t⁻¹ ≤ t^n/δ^(n+1) := by
        rw [le_div_iff₀ (pow_pos hδ _)]
        have z := pow_le_pow_left₀ hδ.le (le_of_not_gt hlt) (n+1)
        calc
          _ ≤ t⁻¹*t^(n+1) := mul_le_mul_of_nonneg_left z (inv_nonneg.mpr ht.le)
          _ = t^n := by rw [pow_succ]; field_simp
      calc
        _ ≤ (‖complexOrderK (2*ν) t‖*(‖c ell Y q‖*orbitBound Y))*t⁻¹ := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (orbit_price ell hY ht q) (norm_nonneg _)) (inv_nonneg.mpr ht.le)
        _ ≤ (‖complexOrderK (2*ν) t‖*(‖c ell Y q‖*orbitBound Y))*(t^n/δ^(n+1)) :=
          mul_le_mul_of_nonneg_left e (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) hB))
        _ = _ := by dsimp [B,F]; ring
  refine ⟨I,((absolute_coefficients ell hY).mul_right (B*(∫ t,F t ∂posMeasure))).of_nonneg_of_le
    (fun q => integral_nonneg (fun _ => norm_nonneg _)) ?_⟩
  intro q
  have H := integral_mono_ae (I q).norm (IF.const_mul (‖c ell Y q‖*B))
    ((ae_restrict_mem measurableSet_Ioi).mono (dom q))
  simpa only [integral_const_mul,mul_assoc] using H

theorem transform_reconstruction (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) (ν : ℂ) :
    HasSum (fun q : Modes => c ell Y q*kTransform ν (orbit q)) (kTransform ν (spectralTest ell Y)) := by
  obtain ⟨I,S⟩ := transform_mass ell hY ν
  let F := fun q : Modes => fun t : ℝ => c ell Y q*transformKernel ν q t
  have E (q : Modes) : c ell Y q*kTransform ν (orbit q) = ∫ t,F q t ∂posMeasure := by
    dsimp only [kTransform,F,transformKernel]
    rw [integral_const_mul]
  have H : Summable (fun q : Modes => ∫ t,F q t ∂posMeasure) :=
    S.of_norm_bounded (fun q => norm_integral_le_integral_norm _)
  simp_rw [E]
  apply H.hasSum_iff.mpr
  rw [integral_tsum_of_summable_integral_norm I S]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have a := ((orbit_reconstruction ell hY ht).mul_left (complexOrderK (2*ν) t)).mul_right ((t:ℂ)⁻¹)
  convert a.tsum_eq using 1
  · apply tsum_congr; intro q; dsimp [F,transformKernel]; ring
  · ring

theorem transformed_probes (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) (ν : ℂ) :
    HasSum (fun q : Modes => c ell Y q*(star (orderProbe 1 (pattern q.1.1 q.2.1) (star ν))*
      orderProbe 1 (rightPattern q.1.2 q.2.2) ν)) (8*kTransform ν (spectralTest ell Y)) := by
  have H := (transform_reconstruction ell hY ν).mul_left 8
  apply H.congr_fun
  intro q
  have e := (induced_transform ν _ _ (pattern_test q.1.1 q.2.1).1 (pattern_test _ _).2.1 (pattern_test _ _).2.2
    (right_test q.1.2 q.2.2).1 (right_test _ _).2.1 (right_test _ _).2.2).2
  rw [← e]; dsimp [orbit]; ring

theorem modulus_reconstruction (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y)
    (z p : ℕ) (hz : 0<z) (hp : 0<p) (h : ℤ) (hh : h≠0) (d : ℕ+) :
    HasSum (fun q : Modes => c ell Y q*modulusTerm (orbit q) z p h d)
      (modulusTerm (spectralTest ell Y) z p h d) := by
  by_cases hd : z.Coprime (d:ℕ)
  · have hr : 0<4*Real.pi*Real.sqrt ((p:ℝ)*(h.natAbs:ℝ))/traceModulus z d := by
      have H : 0<(h.natAbs:ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hh
      have P : 0<(p:ℝ) := by exact_mod_cast hp
      have Z : 0<(z:ℝ) := by exact_mod_cast hz
      have C : 0<((d:ℕ):ℝ) := by exact_mod_cast d.property
      unfold traceModulus; positivity
    simp only [modulusTerm,dif_pos hd]
    apply ((orbit_reconstruction ell hY hr).mul_left _).congr_fun
    intro q; ring
  · simpa only [modulusTerm,dif_neg hd,mul_zero] using
      (hasSum_zero : HasSum (fun _ : Modes => (0:ℂ)) 0)

theorem common_modulus_cutoff (D : OriginalData) (k : BlockKey) (z : Row D k)
    (ha : D.block.atom.residue≠0) (negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    ∃ D₀ : ℕ, ∀ n∈nCarrier D k z.val, ∀ p∈commonMBlock J j, ∀ d : ℕ+, D₀<(d:ℕ) →
      (∀ q : Modes,c ell Y q*modulusTerm (orbit q) z.val p (traceIndex D k negativeM z.val n) d=0) ∧
      modulusTerm (spectralTest ell Y) z.val p (traceIndex D k negativeM z.val n) d=0 := by
  classical
  let ind := traceIndex D k negativeM z.val
  let A := ∑ n∈nCarrier D k z.val, ∑ p∈commonMBlock J j,(p:ℝ)*((ind n).natAbs:ℝ)
  have hA : 0≤A := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
  have hδ := qFloor_pos hY
  obtain ⟨D₀,h₀⟩ := exists_nat_gt (4*Real.pi*(1+A)/qFloor Y)
  refine ⟨D₀,?_⟩
  intro n hn p hp d hd
  have hz := (levelCarrier_licensed D k z.property).1
  have hpp : 0<p := Nat.pos_of_ne_zero (fun e => common_nonzero J j p hp (by simp [e]))
  have hh := traceIndex_natAbs_pos D k negativeM z.val hn ha
  have hr : 0<(p:ℝ)*((ind n).natAbs:ℝ) := mul_pos (by exact_mod_cast hpp) (by exact_mod_cast hh)
  have cpos : 0<((d:ℕ):ℝ) := by exact_mod_cast d.property
  have Z : 1≤Real.sqrt (z.val:ℝ) := by
    have h1 : (1:ℝ)≤(z.val:ℝ) := by exact_mod_cast hz
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt h1
  have cm : 0<traceModulus z.val d := mul_pos (by linarith) cpos
  have cd : ((d:ℕ):ℝ)≤traceModulus z.val d := by
    simpa only [one_mul,traceModulus] using mul_le_mul_of_nonneg_right Z cpos.le
  have hm : (p:ℝ)*((ind n).natAbs:ℝ)≤A :=
    (Finset.single_le_sum (fun b (_ : b∈commonMBlock J j) =>
      mul_nonneg (Nat.cast_nonneg b) (Nat.cast_nonneg (ind n).natAbs)) hp).trans
        (Finset.single_le_sum (fun b (_ : b∈nCarrier D k z.val) =>
          Finset.sum_nonneg (fun p (_ : p∈commonMBlock J j) =>
            mul_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg (ind b).natAbs))) hn)
  have sq : Real.sqrt ((p:ℝ)*((ind n).natAbs:ℝ))≤1+A := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by linarith)).mp
    rw [Real.sq_sqrt hr.le]; nlinarith [sq_nonneg A]
  let t := 4*Real.pi*Real.sqrt ((p:ℝ)*((ind n).natAbs:ℝ))/traceModulus z.val d
  have ht : 0<t := div_pos (mul_pos (by positivity) (Real.sqrt_pos.mpr hr)) cm
  have hq : t<qFloor Y := by
    apply (div_lt_iff₀ cm).mpr
    have dd : (D₀:ℝ)<((d:ℕ):ℝ) := by exact_mod_cast hd
    have hbound := (div_lt_iff₀ hδ).mp (h₀.trans dd)
    exact (mul_le_mul_of_nonneg_left sq (by positivity)).trans_lt
      (hbound.trans_le (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left cd hδ.le))
  have atom (q : Modes) : c ell Y q*modulusTerm (orbit q) z.val p (ind n) d=0 := by
    by_cases co : z.val.Coprime (d:ℕ)
    · rw [modulusTerm,dif_pos co]
      change c ell Y q*(_*orbit q t)=0
      rw [mul_left_comm,orbit_zero ell hY ht hq q,mul_zero]
    · simp only [modulusTerm,dif_neg co,mul_zero]
  refine ⟨atom,?_⟩
  have H := (modulus_reconstruction ell hY z.val p hz hpp (ind n) (Int.natAbs_pos.mp hh) d).tsum_eq
  simpa only [atom,tsum_zero] using H.symm

end
end ImbalancedChen.Part3.PrescribedTensorBesselGeometry20261112
