import ImbalancedChen.P4BOriginalShortMediumTriplePayment
import ImbalancedChen.P4BOriginalMediumScheduledInventory
import ImbalancedChen.P4BOriginalCollisionModes
import ImbalancedChen.P4BOriginalNativeTargetPayment
import ImbalancedChen.PowerErrorBudget
import ImbalancedChen.P5zElevenErrorTransport

/-! SOURCE ONLY / UNCOMPILED.
Remove the paid short-head, low-first triple words from one original signed
physical pair fibre. The complement is the literal remaining restored sum. -/
namespace ImbalancedChen.P4BOriginalShortMediumTripleReceiver

noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalMediumAtomFamily (Index size)
open P4BOriginalMediumOccupiedLengths (firstOwners secondOwners thirdOwners)
open P4BOriginalMediumPhysicalAtomSum (onWord boxedErrors all_free_words)
open P4BOriginalMediumAtomReconstruction (withOwners)
open P4BOriginalMediumRestoringBudget (pieces pieces_cost scalar_cost)
open P4BOriginalMediumSignedFibre (originalMode scalar)
open P4BOriginalCollisionTensor (ownerHead products free)
open P4BOriginalCollisionThirdFactor (restoring restored_mass master)
open P4BOriginalHighRankComplementBlocks (fibre)
open P4BOriginalUpperFourierTailPaid (dyadicConstant dyadicConstant_pos)
open P4AHeldTaggedCompilerSupport (J0)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le target_le_countingScale)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P4BOriginalNativeTargetPayment (localConstant localConstant_nonneg complete_to_target)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open PrimeProducts.MellinInsertion20261028 (exactDiscrepancy)

variable {order : ℕ} {zeta kap0 : ℝ} (I : Index order zeta kap0)

def tripleWords := I.P.words.attach.filter (fun J => J.val.length=3 ∧
  actualPrimeTupleLog I.P.N (ownerHead I.P J.val) 0≤VariableEnvelope.mu)

def wordTerm (K : ℕ) (j : {J // J∈I.P.words}) : ℂ :=
  (restoring I.P I.x I.U I.eta j.val:ℂ)*boxedErrors K (onWord I j)

def remaining (K : ℕ) : ℂ :=
  (scalar I:ℂ)*∑ j∈I.P.words.attach \ tripleWords I,wordTerm I K j

theorem boxed_le (K : ℕ) (E : ℝ)
    (h : ∀ D∈firstOwners I,∀ F∈secondOwners I,∀ G∈thirdOwners I,
      ‖((withOwners I D F G).atom K).signedError‖≤E) :
    ‖boxedErrors K I‖≤(pieces I:ℝ)*E := by
  let S := firstOwners I
  let T := secondOwners I
  let V := thirdOwners I
  calc
    ‖boxedErrors K I‖≤∑ D∈S,∑ F∈T,∑ G∈V,(E:ℝ) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro D hD
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro F hF
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun G hG => h D hD F hF G hG)
    _=(pieces I:ℝ)*E := by
      simp only [S,T,V,pieces,firstOwners,secondOwners,thirdOwners,Finset.sum_const,
        nsmul_eq_mul,Nat.cast_mul]
      ring

def feeConstant (omega T : ℝ) : ℝ :=
  (2:ℝ)^12*(((master omega T).card:ℝ)*((J0 omega).factorial:ℝ)^3)*
    (dyadicConstant*((J0 omega:ℝ)+2))^3

private theorem word_fee (hN : 1<I.P.N) (he : 0≤I.P.e) (ho : 0<I.P.omega)
    (hell : I.P.ell≤1) :
    scalar I*(∑ j∈tripleWords I,|restoring I.P I.x I.U I.eta j.val|*(pieces (onWord I j):ℝ))≤
      feeConstant I.P.omega I.P.T*logScale (countingScale I.P.N)^15 := by
  let L := logScale (countingScale I.P.N)
  let M := ((master I.P.omega I.P.T).card:ℝ)*((J0 I.P.omega).factorial:ℝ)^3
  let D := dyadicConstant*((J0 I.P.omega:ℝ)+2)
  have hD : 0≤D := by dsimp [D]; positivity [dyadicConstant_pos]
  have hM : 0≤M := by dsimp [M]; positivity
  have hL : 0≤L := zero_le_one.trans (logScale_one_le (countingScale_one_le I.N_pos))
  have hsmall : 0≤logScale (I.P.N:ℝ) :=
    zero_le_one.trans (logScale_one_le (by exact_mod_cast hN.le))
  have hmono : logScale (I.P.N:ℝ)≤L := by
    unfold L logScale
    apply add_le_add_left
    apply Real.log_le_log (by have hP : 0<(I.P.N:ℝ) := by exact_mod_cast I.N_pos; positivity)
    exact mul_le_mul_of_nonneg_left (target_le_countingScale I.P.N) (by norm_num)
  have hs : (∑ j∈tripleWords I,|restoring I.P I.x I.U I.eta j.val|)≤M := by
    calc
      _≤∑ j∈I.P.words.attach,|restoring I.P I.x I.U I.eta j.val| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => abs_nonneg _)
      _≤M := by simpa only [Finset.sum_attach,M] using restored_mass I.P hN he ho I.x I.U I.eta
  have hcount (j : {J // J∈I.P.words}) : (pieces (onWord I j):ℝ)≤(D*L)^3 :=
    (pieces_cost (onWord I j) hN he ho hell).trans
      (pow_le_pow_left₀ (mul_nonneg hD hsmall) (mul_le_mul_of_nonneg_left hmono hD) 3)
  have hweights : (∑ j∈tripleWords I,|restoring I.P I.x I.U I.eta j.val|*(pieces (onWord I j):ℝ))
      ≤M*(D*L)^3 := by
    calc
      _≤∑ j∈tripleWords I,|restoring I.P I.x I.U I.eta j.val|*(D*L)^3 :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hcount j) (abs_nonneg _))
      _≤_ := by
        rw [←Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right hs (pow_nonneg (mul_nonneg hD hL) 3)
  have hweight0 : 0≤∑ j∈tripleWords I,|restoring I.P I.x I.U I.eta j.val|*
      (pieces (onWord I j):ℝ) :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  apply (mul_le_mul (scalar_cost I).2 hweights hweight0
    (pow_nonneg (by linarith only [hL] : 0≤2*L) 12)).trans_eq
  change (2*L)^12*(M*(D*L)^3)=(2^12*M*D^3)*L^15
  ring

theorem free_difference (K : ℕ) (hN : 1<I.P.N) (hU : 1<I.U)
    (E : ℝ) (hE : 0≤E)
    (hp : ∀ j∈tripleWords I,‖boxedErrors K (onWord I j)‖≤(pieces (onWord I j):ℝ)*E)
    (he : 0≤I.P.e) (ho : 0<I.P.omega) (hell : I.P.ell≤1) :
    ‖exactDiscrepancy (fibre I.bs I.i I.C) (products I.P) (fun q => (free I.P q:ℂ))
      completeProduct I.P.N (originalMode I K)-remaining I K‖≤
      (feeConstant I.P.omega I.P.T*logScale (countingScale I.P.N)^15)*E := by
  have heq : (∑ j∈I.P.words.attach,wordTerm I K j)=
      (∑ j∈I.P.words.attach \ tripleWords I,wordTerm I K j)+
      (∑ j∈tripleWords I,wordTerm I K j) :=
    (Finset.sum_sdiff (Finset.filter_subset _ _)).symm
  rw [all_free_words I K hN hU]
  change ‖(scalar I:ℂ)*(∑ j∈I.P.words.attach,wordTerm I K j)-remaining I K‖≤_
  rw [heq,mul_add,remaining,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (scalar_cost I).1]
  have ht : ‖∑ j∈tripleWords I,wordTerm I K j‖≤
      (∑ j∈tripleWords I,|restoring I.P I.x I.U I.eta j.val|*(pieces (onWord I j):ℝ))*E := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    rw [wordTerm,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_assoc]
    exact mul_le_mul_of_nonneg_left (hp j hj) (abs_nonneg _)
  calc
    _≤scalar I*((∑ j∈tripleWords I,|restoring I.P I.x I.U I.eta j.val|*(pieces (onWord I j):ℝ))*E) :=
      mul_le_mul_of_nonneg_left ht (scalar_cost I).1.le
    _≤_ := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (word_fee I hN he ho hell) hE

/-- On the short-head fibres of the original retained rank-two medium row,
the physical signed count minus exact coprime mean differs from the sum of
all other words by at most eta H_N. Both the matched and unmatched sums
retain the HB scalar, factorials and original frequency. -/
theorem eventually_physical_short_three_removed (K order : ℕ) (omega T eta : ℝ)
    (ho : 0<omega) (heta : 0<eta)
    {zeta kappa kap0 : ℝ} (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ I : Index order zeta kap0,
      I.P.N=N → I.P.omega=omega → I.P.T=T → I.eta=zeta →
      0≤I.P.e → (I.P.e:ℝ)≤1/2048 → 0<I.P.q →
      I.P.T*((J0 I.P.omega:ℝ)+1)≤zeta → 0≤I.P.ell → 2*I.P.ell≤zeta/16 →
      I.U≤I.x^(1/16:ℝ) →
      ‖exactDiscrepancy (fibre I.bs I.i I.C) I.P.S (fun q => (I.P.rho q:ℂ))
        completeProduct I.P.N (originalMode I K)-remaining I K‖≤eta*singularNormalization N := by
  have hz1 : zeta≤1/400 := by linarith
  have hke : kappa≤zeta := by linarith
  obtain ⟨C,hC,HP⟩ := P4BOriginalShortMediumTriplePayment.eventually_short_three_signed
    K order 18 (by norm_num) hz hz0 hk hkz ht ht1
  obtain ⟨B,hB,HC⟩ := P4BOriginalCollisionModes.exists_mode_cost omega (omega/2) ho (half_pos ho)
  let M := feeConstant omega T
  have hM : 0≤M := by dsimp [M,feeConstant]; positivity [dyadicConstant_pos]
  let D := C*localConstant 18
  have hD : 0≤D := mul_nonneg hC.le (localConstant_nonneg _)
  filter_upwards [HP,HC,P4BOriginalHighRankScheduledCount.eventually_width 1 (by norm_num),
    P4BOriginalMediumFibreSWWindow.eventually_window K order 1 hz hz1 hk hke ht ht1,
    P4BOriginalHighRankLiveFibreModes.eventually_fixed_live_window K hz hz1 hk hke ht ht1,
    p5z_eventually_logCube_le_singularNormalization (M*2^15*D) (eta/2) (half_pos heta),
    eventually_powerLog_le_singularNormalization (B*2^12) (1-omega+omega/2) 12
      (by linarith) (eta/2) (half_pos heta)] with N Hpaid Hcoll width HW HL hfee hcollision
  intro I hIN hw hT hEta he he' hq hmesh hell hell' hshort
  have hN : 1<I.P.N := by rw [hIN]; have h := width.1; omega
  have hNr : 1<(N:ℝ) := by exact_mod_cast (show 1<N by have h := width.1; omega)
  have hlog : 0<Real.log (N:ℝ) := Real.log_pos hNr
  have hscale := width.2.2.2.2
  have hs0 : 0≤logScale (countingScale N) :=
    zero_le_one.trans (logScale_one_le (countingScale_one_le (by have h := width.1; omega)))
  have hOP : 0<I.P.omega := hw.symm ▸ ho
  have hT0 : I.P.T≤zeta := by
    exact (le_mul_of_one_le_right I.P.T_pos.le
      (le_add_of_nonneg_left (Nat.cast_nonneg (J0 I.P.omega)))).trans hmesh
  have hbudget : I.P.ell+I.P.T*(J0 I.P.omega:ℝ)<1/1000 := by
    rw [mul_add,mul_one] at hmesh
    linarith only [hmesh,I.P.T_pos,hz0,hell']
  have hdim : size I.j+size I.l≤12 := by
    have hj := I.j.isLt
    have hl := I.l.isLt
    dsimp [size]
    omega
  have hpos := P4BOriginalCollisionModes.live_products I.b_pos I.kap_pos I.s_pos I.gate
    hdim I.cj I.ck I.bs (fibre I.bs I.i I.C) (Finset.filter_subset _ _) I.live
  have HC0 := Hcoll I.P hIN hw he hbudget hdim (fibre I.bs I.i I.C)
    (by simpa only [←hIN] using hpos) (I.Z K)
    I.truncations I.roles (P4BUpperPairOrderedRowGeometry.blockScales I.bs) I.xi
  let a := exactDiscrepancy (fibre I.bs I.i I.C) I.P.S (fun q => (I.P.rho q:ℂ))
    completeProduct I.P.N (originalMode I K)
  let b := exactDiscrepancy (fibre I.bs I.i I.C) (products I.P) (fun q => (free I.P q:ℂ))
    completeProduct I.P.N (originalMode I K)
  have hab : ‖a-b‖≤eta/2*singularNormalization N := by
    rw [←hIN] at HC0 hscale hcollision hs0 ⊢
    change ‖b-a‖≤_ at HC0
    rw [norm_sub_rev]
    apply HC0.trans
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hscale 12)
      (mul_nonneg hB.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))).trans
    rw [mul_pow]
    linarith only [hcollision]
  rw [←hIN] at HW HL
  have hsel := P4BOriginalMediumFibreSWWindow.first_spec I.selected
  have hwindow := HW I.b_pos I.kap_pos I.s_pos I.gate _ _ I.cj I.ck I.bs I.i I.C I.live hsel
  have hlive := HL I.b_pos I.kap_pos I.s_pos I.gate _ _ I.cj I.ck I.bs I.i I.C I.live hsel
  have hx : 1<I.x := hwindow.2.1
  have hU : 1<I.U := hwindow.2.2.2.2.1
  have hNx : (I.P.N:ℝ)≤I.x^(1+kappa) := hlive.2.2.1
  have hc := complete_to_target 18 I.P.N (by exact_mod_cast hN) hx
    (show kappa≤1 by linarith) hNx I.scale_upper
  let E := D*(N:ℝ)/(Real.log (N:ℝ))^18
  have hE : 0≤E := div_nonneg (mul_nonneg hD (Nat.cast_nonneg _)) (pow_nonneg hlog.le _)
  have hbox (j : {J // J∈I.P.words}) (hj : j∈tripleWords I) :
      ‖boxedErrors K (onWord I j)‖≤(pieces (onWord I j):ℝ)*E := by
    obtain ⟨hr,hlo⟩ := (Finset.mem_filter.mp hj).2
    apply boxed_le
    intro d hd f hf g hg
    have h := Hpaid (onWord I j) hIN hEta he he' hq hT0 hell hell' hr hlo hshort d hd f hf g hg
    have h' : ‖((withOwners (onWord I j) d f g).atom K).signedError‖≤C*I.x/(Real.log I.x)^18 := by
      simpa only [←Real.rpow_natCast (Real.log I.x) 18,Nat.cast_ofNat] using h
    apply h'.trans
    calc
      _=C*(I.x/(Real.log I.x)^18) := by ring
      _≤C*(localConstant 18*I.P.N/(Real.log (I.P.N:ℝ))^18) :=
        mul_le_mul_of_nonneg_left hc hC.le
      _=E := by dsimp only [E,D]; rw [hIN]; ring
  have Hfree := free_difference I K hN hU E hE hbox he hOP (by linarith only [hell',hz0])
  have hrest : ‖b-remaining I K‖≤eta/2*singularNormalization N := by
    change ‖b-remaining I K‖≤_ at Hfree
    rw [hw,hT,hIN] at Hfree
    apply Hfree.trans
    change (M*logScale (countingScale N)^15)*E≤_
    calc
      _≤(M*(2*Real.log (N:ℝ))^15)*E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hscale 15) hM) hE
      _=(M*2^15*D)*(N:ℝ)/(Real.log (N:ℝ))^3 := by dsimp only [E]; field_simp [hlog.ne']; ring
      _≤_ := hfee
  change ‖a-remaining I K‖≤_
  calc
    _=‖(a-b)+(b-remaining I K)‖ := by congr 1 <;> ring
    _≤‖a-b‖+‖b-remaining I K‖ := norm_add_le _ _
    _≤eta*singularNormalization N := by linarith only [hab,hrest]

end
end ImbalancedChen.P4BOriginalShortMediumTripleReceiver
