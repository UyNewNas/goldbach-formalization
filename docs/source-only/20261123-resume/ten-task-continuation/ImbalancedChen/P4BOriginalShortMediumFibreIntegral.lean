import ImbalancedChen.P4BOriginalShortMediumWordKernel
import ImbalancedChen.P4BOriginalCollisionRetained
import ImbalancedChen.BoundaryArbitraryLog

/-! Source only. Integrate the surviving complete-modulus test on a live
short fibre. Unselected fibres keep their native physical integer sum. -/
namespace ImbalancedChen.P4BOriginalShortMediumFibreIntegral
noncomputable section
open Classical Filter MeasureTheory
open scoped BigOperators
open PrimeProducts.MellinInsertion20261028 (exactDiscrepancy functional residueKernel)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct hbSlots)
open P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode)
open P5Z.AllRankCauchyCubeTail (outsideCube measurableSet_outsideCube)
open P5Z.ActualRoughHeathBrownWords (Role)
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P4BUpperPairOrderedRowModes (amplitude amplitude_integrable amplitude_mode_integrable)
open P4BUpperPairOrderedRowGeometry (integerProfile blockScales rowRoles)
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (products free)
open P4BOriginalHighRankMotherMass (rowMass exists_row_mass)
open P4BOriginalHighRankComplementBlocks (fibre)
open P4BOriginalHighRankPostModulusRow (original retained truncated truncated_eq_band H)
open P4BOriginalHighRankPostModulusFibres (first)
open P4BOriginalHighRankScheduledCount (outerWidth eventually_width)
open P4BOriginalShortMediumWordKernel (selectedWords otherKernel exists_free_mode_cost)
open P4BOriginalMediumAtomFamily (Index size)
open P4BOriginalFiniteSmoothCount (Q)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le target_le_countingScale)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P4AHeldTaggedCompilerSupport (J0)
open P4BOuterRampRoughness (baseline)

structure WordRange (P : Params) (omega T zeta : ℝ) : Prop where
  presieve : P.omega=omega
  mesh : P.T=T
  shift_nonneg : 0≤P.e
  shift_le : (P.e:ℝ)≤1/2048
  denominator_pos : 0<P.q
  mesh_le : P.T*((J0 P.omega:ℝ)+1)≤zeta
  small_nonneg : 0≤P.ell
  small_le : 2*P.ell≤zeta/16

theorem WordRange.reserve {P : Params} {omega T zeta : ℝ} (R : WordRange P omega T zeta)
    (hz : zeta≤1/20000) : P.ell+P.T*(J0 P.omega:ℝ)<1/1000 := by
  have hm := R.mesh_le
  rw [mul_add,mul_one] at hm
  linarith only [hm,P.T_pos,R.small_le,hz]

theorem WordRange.supported {P : Params} {omega T zeta : ℝ} (R : WordRange P omega T zeta)
    (ho : 0<omega) (hz : zeta≤1/20000) (hN : 1<P.N) {d : ℕ} (hd : P.rho d≠0) :
    (d:ℝ)<(P.N:ℝ)^modulusExponent :=
  P4BOriginalCollisionPhysical.supported_physical P hN R.shift_nonneg (R.presieve.symm ▸ ho)
    (by linarith only [R.small_le,hz]) (R.reserve hz) hd

def kernelMode {m : ℕ} (rows : Finset (Fin m→ℕ)) (bs : Fin m→Block)
    (Z : ℝ) (ys : Fin m→ℝ) (rs : Fin m→Role) (F : ℕ→ℂ) (xi : Fin m→ℝ) : ℂ :=
  functional rows (fun y => F (completeProduct y))
    (fun y => hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi)

private theorem amplitude_kernel_integrable {u v N : ℕ} {b kap s : ℝ} (hb : 0<b) (hs : 0<s)
    (hg : 2*s≤baseline b kap-19/96) (kap0 : ℝ) (cj ck : ℕ) (bs : Fin (u+v)→Block)
    (rows : Finset (Fin (u+v)→ℕ)) (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role)
    (F : ℕ→ℂ) :
    Integrable (fun xi => amplitude (a:=u) (d:=v) b kap s N kap0 cj ck bs xi*
      kernelMode rows bs Z ys rs F xi) := by
  let M := amplitude (a:=u) (d:=v) b kap s N kap0 cj ck bs
  have hg' : 2*s≤baseline b kap-1*(19/96:ℝ) := by simpa only [one_mul] using hg
  have h (y : Fin (u+v)→ℕ) : Integrable (fun xi =>
      M xi*(hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi)) := by
    have hh := (amplitude_mode_integrable hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
      hs hg' N kap0 cj ck bs y).const_mul (hbSlots Z ys rs y)
    exact hh.congr (Eventually.of_forall (fun xi => by dsimp [M]; ring))
  have hh := PrimeProducts.MellinInsertion20261028.functional_integrable rows
    (fun y => F (completeProduct y))
    (fun xi y => M xi*(hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi)) (fun y _ => h y)
  simpa only [kernelMode,PrimeProducts.MellinInsertion20261028.functional_mul,M] using hh

def kernelIntegral {u v : ℕ} (b kap s : ℝ) (P : Params) (kap0 : ℝ) (cj ck order : ℕ)
    (bs : Fin (u+v)→Block) (rows : Finset (Fin (u+v)→ℕ)) (Z : ℝ)
    (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role) (F : ℕ→ℂ) : ℂ :=
  ∫ xi in (outsideCube (u+v) (H P.N order))ᶜ,
    amplitude (a:=u) (d:=v) b kap s P.N kap0 cj ck bs xi*kernelMode rows bs Z ys rs F xi

private theorem truncated_sub_kernelIntegral {u v : ℕ} {b kap s : ℝ} (hb : 0<b) (hs : 0<s)
    (hg : 2*s≤baseline b kap-19/96) (P : Params) (kap0 : ℝ) (cj ck order : ℕ)
    (bs : Fin (u+v)→Block) (rows : Finset (Fin (u+v)→ℕ)) (Z : ℝ)
    (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role) (F : ℕ→ℂ) {E : ℝ} (hE : 0≤E)
    (h : ∀ xi∈(outsideCube (u+v) (H P.N order))ᶜ,
      ‖exactDiscrepancy rows (products P) (fun q => (free P q:ℂ)) completeProduct P.N
        (fun y => hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi)-
        kernelMode rows bs Z ys rs F xi‖≤E) :
    ‖truncated (u:=u) (v:=v) b kap s P.N kap0 cj ck bs rows Z ys rs (products P) (free P) (H P.N order)-
      kernelIntegral (u:=u) (v:=v) b kap s P kap0 cj ck order bs rows Z ys rs F‖≤
      rowMass (u:=u) (v:=v) b kap s P.N kap0 cj ck bs*E := by
  let R := (outsideCube (u+v) (H P.N order))ᶜ
  let M := amplitude (a:=u) (d:=v) b kap s P.N kap0 cj ck bs
  let G := fun n => ∑ q∈products P,(free P q:ℂ)*residueKernel q P.N n
  let f := kernelMode rows bs Z ys rs G
  let g := kernelMode rows bs Z ys rs F
  have hi (k : ℕ→ℂ) := amplitude_kernel_integrable (N:=P.N) hb hs hg kap0 cj ck bs rows Z ys rs k
  have hM : Integrable M := amplitude_integrable hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
    hs (by simpa only [one_mul] using hg) P.N kap0 cj ck bs
  rw [truncated_eq_band hb hs hg]
  change ‖(∫ xi in R,M xi*f xi)-(∫ xi in R,M xi*g xi)‖≤_
  rw [←integral_sub (hi G).integrableOn (hi F).integrableOn]
  calc
    _≤∫ xi in R,‖M xi‖*E := by
      apply norm_integral_le_of_norm_le (hM.norm.mul_const E).integrableOn
      filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_outsideCube (u+v) (H P.N order)).compl]
        with xi hxi
      rw [←mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left (h xi hxi) (norm_nonneg _)
    _=(∫ xi in R,‖M xi‖)*E := integral_mul_const E _
    _≤_ := mul_le_mul_of_nonneg_right (setIntegral_le_integral hM.norm
      (Eventually.of_forall (fun xi => norm_nonneg (M xi)))) hE

/-- Whole physical fibres are preserved unless there is a genuinely selected
word, the source is live, and the complete local scale passes the short test. -/
def otherFibre {u v : ℕ} (b kap s : ℝ) (P : Params) (kap0 zeta : ℝ) (cj ck order : ℕ)
    (bs : Fin (u+v)→Block) (i : Fin (u+v)) (C : Block) (Z : ℝ)
    (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role) : ℂ :=
  let U := (lower (bs i):ℝ)
  let x := U*(lower C:ℝ)
  if U≤x^(1/16:ℝ) ∧ (selectedWords P).Nonempty ∧
      ∃ y∈fibre bs i C,integerProfile (a:=u) (d:=v) b kap s P.N kap0 cj ck y≠0 then
    kernelIntegral (u:=u) (v:=v) b kap s P kap0 cj ck order bs (fibre bs i C) Z ys rs
      (otherKernel P x U zeta)
  else original (u:=u) (v:=v) b kap s P.N kap0 cj ck (fibre bs i C) Z ys rs P.S P.rho

theorem exists_fibre_cost (K A : ℕ) (omega T : ℝ) (ho : 0<omega)
    {zeta kappa kap0 b kap : ℝ} (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000) (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1)
    (hb : 0<b) (hb1 : b≤1) (hkap : 0<kap) (hgap : 19/96<baseline b kap) :
    ∃ D : ℝ,0≤D ∧ ∀ᶠ N : ℕ in atTop,∀ P : Params,P.N=N → WordRange P omega T zeta →
      ∀ (j l : Fin 3) (cj ck : ℕ) (bs : Fin (size j+size l)→Block)
        (i : Fin (size j+size l)) (C : Block),first cj ck zeta bs=some i →
      let Z := beforeHBCutoff K [cj,ck]
      let ys := Fin.append (fun _ : Fin (size j) => hbCutoff cj) (fun _ : Fin (size l) => hbCutoff ck)
      let rs := Fin.append (rowRoles j.val) (rowRoles l.val)
      ‖original (u:=size j) (v:=size l) b kap (outerWidth N) P.N kap0 cj ck (fibre bs i C) Z ys rs P.S P.rho-
        otherFibre (u:=size j) (v:=size l) b kap (outerWidth N) P kap0 zeta cj ck A bs i C Z ys rs‖≤
        D*N/(Real.log (N:ℝ))^(A+15) := by
  let p := A+15
  obtain ⟨D,hD,hmode⟩ := exists_free_mode_cost K A (p+24) omega T ho hz hz0 hk hkz ht ht1
  obtain ⟨G,hG,hrow⟩ := exists_row_mass
  obtain ⟨B,hB,hcollision⟩ := P4BOriginalCollisionRetained.exists_row_cost omega (omega/2) ho (half_pos ho)
  obtain ⟨C,hC,htail⟩ := P4BOriginalHighRankPostModulusRow.exists_row_payment
  let M := G*2^24*D
  have hM : 0≤M := by dsimp [M]; positivity
  refine ⟨C+1+M,by positivity,?_⟩
  filter_upwards [hmode,hcollision hb hb1 hkap hgap,eventually_width _ (half_pos (sub_pos.mpr hgap)),
    eventually_one_le_nat_log,eventually_powerLog_le_logAccuracy (B*2^36) (1-omega+omega/2)
      36 p (by linarith) 1 (by norm_num)] with N hlocal hcol hw hlog hpow
  intro P hPN R j l cj ck bs i V hsel
  subst N
  dsimp only
  let s := outerWidth P.N
  let L := Real.log (P.N:ℝ)
  let Z := beforeHBCutoff K [cj,ck]
  let ys := Fin.append (fun _ : Fin (size j) => hbCutoff cj) (fun _ : Fin (size l) => hbCutoff ck)
  let rs := Fin.append (rowRoles j.val) (rowRoles l.val)
  let rows := fibre bs i V
  let U := (lower (bs i):ℝ)
  let x := U*(lower V:ℝ)
  let F := otherKernel P x U zeta
  have hN : 1<P.N := by have hh := hw.1; omega
  have hn : 0<P.N := by omega
  have hs : 0<s := hw.2.1
  have hg : 2*s≤baseline b kap-19/96 := by have hh : s≤(baseline b kap-19/96)/2 := hw.2.2.1; linarith
  have hL : 0<L := zero_lt_one.trans_le hlog
  have hscale := logScale_one_le (countingScale_one_le hn)
  have hd : size j+size l≤12 := by dsimp [size]; omega
  by_cases active : U≤x^(1/16:ℝ) ∧ (selectedWords P).Nonempty ∧
      ∃ y∈rows,integerProfile (a:=size j) (d:=size l) b kap s P.N kap0 cj ck y≠0
  · rw [otherFibre,if_pos active]
    let E := D*P.N/L^(p+24)
    have hE : 0≤E := div_nonneg (mul_nonneg hD (Nat.cast_nonneg _)) (pow_nonneg hL.le _)
    obtain ⟨jword,hword⟩ := active.2.1
    have hT : P.T≤zeta := (le_mul_of_one_le_right P.T_pos.le
      (le_add_of_nonneg_left (Nat.cast_nonneg (J0 P.omega)))).trans R.mesh_le
    have hF := truncated_sub_kernelIntegral (u:=size j) (v:=size l) hb hs hg P kap0 cj ck A
      bs rows Z ys rs F hE (by
        intro xi hxi
        let I : Index A zeta kap0 := {
          P:=P, N_pos:=hn, b:=b, kap:=kap, s:=s, b_pos:=hb, kap_pos:=hkap,
          s_pos:=hs, gate:=hg, j:=j, l:=l, cj:=cj, ck:=ck, bs:=bs, i:=i, C:=V,
          live:=active.2.2, selected:=hsel, xi:=xi, band:=hxi, eta:=zeta,
          J:=jword.val, word:=jword.property, owners:=fun _ => .unit }
        exact hlocal I rfl R.presieve R.mesh rfl R.shift_nonneg R.shift_le R.denominator_pos
          hT R.small_nonneg R.small_le active.1)
    have hprice := hrow b kap s hb hb1 hkap hs hg P.N hn kap0 cj ck _ _ hd bs
    have hprice' : G/s^24≤G*(2*L)^24 := by
      change G/(1/(P4BOriginalHighRankScheduledCount.resolution P.N+1:ℝ))^24≤_
      rw [one_div,inv_pow,div_inv_eq_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (hw.2.2.2.1.trans hw.2.2.2.2) _) hG
    have hwordPrice := hF.trans ((mul_le_mul_of_nonneg_right (hprice.trans hprice') hE).trans_eq
      (show G*(2*L)^24*E=M*P.N/L^p by
        dsimp only [M,E]; rw [pow_add,mul_pow]; field_simp [hL.ne'] <;> ring))
    have hc := hcol P rfl R.presieve R.shift_nonneg (R.reserve hz0) hd kap0 A cj ck bs rows
      (Finset.filter_subset _ _) Z ys rs
    simp only [retained,if_pos active.2.2] at hc
    have hc' : B*(P.N:ℝ)^(1-omega+omega/2)*logScale (countingScale P.N)^36≤(P.N:ℝ)/L^p := by
      calc
        _≤B*(P.N:ℝ)^(1-omega+omega/2)*(2*L)^36 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hscale) hw.2.2.2.2 _)
            (mul_nonneg hB (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        _=(B*2^36)*(P.N:ℝ)^(1-omega+omega/2)*L^36 := by ring
        _≤_ := by simpa only [one_mul] using hpow
    have hS : P.S⊆Q P.omega P.N := fun _ h => (Finset.mem_sdiff.mp h).1
    have ht' := htail hn hb hb1 hkap hg hw.2.2.2.1 hd kap0 A cj ck bs rows
      (Finset.filter_subset _ _) Z ys rs P.m P.r P.n P.e P.q P.a P.omega P.k P.ell P.S hS
      (fun d hd' => R.supported ho hz0 hN hd')
    simp only [retained,if_pos active.2.2] at ht'
    have hlogle : L≤logScale (countingScale P.N) := by
      have h := target_le_countingScale P.N
      have hh := Real.log_le_log (Nat.cast_pos.mpr hn) (show (P.N:ℝ)≤7*countingScale P.N by linarith)
      dsimp [L,logScale]; linarith
    have ht'' : C*P.N/logScale (countingScale P.N)^(A+15+3)≤C*P.N/L^p :=
      div_le_div_of_nonneg_left (mul_nonneg hC (Nat.cast_nonneg _)) (pow_pos hL _)
        ((pow_le_pow_left₀ hL.le hlogle p).trans (pow_le_pow_right₀ hscale (by dsimp [p]; omega)))
    let a := original (u:=size j) (v:=size l) b kap s P.N kap0 cj ck rows Z ys rs P.S P.rho
    let d := truncated (u:=size j) (v:=size l) b kap s P.N kap0 cj ck bs rows Z ys rs P.S P.rho (H P.N A)
    let f := truncated (u:=size j) (v:=size l) b kap s P.N kap0 cj ck bs rows Z ys rs (products P) (free P) (H P.N A)
    let g := kernelIntegral (u:=size j) (v:=size l) b kap s P kap0 cj ck A bs rows Z ys rs F
    have had : ‖a-d‖≤C*P.N/L^p := ht'.trans ht''
    have hdf : ‖d-f‖≤(P.N:ℝ)/L^p := (norm_sub_rev d f).le.trans (hc.trans hc')
    have hfg : ‖f-g‖≤M*P.N/L^p := hwordPrice
    change ‖a-g‖≤(C+1+M)*P.N/L^p
    calc
      _=‖((a-d)+(d-f))+(f-g)‖ := by congr 1 <;> ring
      _≤‖a-d‖+‖d-f‖+‖f-g‖ := (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _≤C*P.N/L^p+(P.N:ℝ)/L^p+M*P.N/L^p := add_le_add (add_le_add had hdf) hfg
      _=_ := by ring
  · rw [otherFibre,if_neg active,sub_self,norm_zero]
    exact div_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _)) (pow_nonneg hL.le _)

end
end ImbalancedChen.P4BOriginalShortMediumFibreIntegral
