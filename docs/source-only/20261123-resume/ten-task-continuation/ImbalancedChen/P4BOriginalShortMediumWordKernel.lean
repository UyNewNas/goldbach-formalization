import ImbalancedChen.P4BOriginalShortMediumTripleReceiver
import Mathlib.LinearAlgebra.Pi

/-! Source only. The surviving actual words define a finite linear functional
on complete-modulus tests. It is independent of the frequency. This allows
the literal earlier receiver to be integrated against its original profile. -/
namespace ImbalancedChen.P4BOriginalShortMediumWordKernel
noncomputable section
open Classical Filter
open scoped BigOperators
open PrimeProducts.MellinInsertion20261028 (functional residueKernel exactDiscrepancy)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (ownerHead products free)
open P4BOriginalCollisionThirdFactor (restoring splitAt factor gamma thirdSupport)
open P4BOriginalCollisionKernel (row)
open P4BOriginalHighRankComplementBlocks (fibre)
open P4BOriginalMediumAtomFamily (Index support)
open P4BOriginalMediumSignedFibre (scalar originalMode row_at_level)
open P4BOriginalMediumPhysicalAtomSum (onWord boxedErrors)
open P4BOriginalMediumAtomReconstruction (word_errors withOwners)
open P4BOriginalMediumRestoringBudget (pieces)
open P4BOriginalShortMediumTripleReceiver (tripleWords remaining wordTerm boxed_le feeConstant free_difference)
open P4BOriginalNativeTargetPayment (complete_to_target localConstant localConstant_nonneg)
open P4BOriginalHighRankScheduledCount (eventually_width)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P4BOriginalUpperFourierTailPaid (dyadicConstant_pos)

def selectedWords (P : Params) := P.words.attach.filter (fun j => j.val.length=3 ∧
  actualPrimeTupleLog P.N (ownerHead P j.val) 0≤VariableEnvelope.mu)

def modulusWord (P : Params) (x U eta : ℝ) (J : List ℕ) : (ℕ→ℂ) →ₗ[ℂ] ℂ :=
  let g := splitAt P x U eta J
  (restoring P x U eta J:ℂ) •
    ∑ a∈support P g.1,∑ b∈support P g.2.1,∑ t∈thirdSupport P J g.2.2,
      ((factor P g.1 a:ℂ)*(factor P g.2.1 b:ℂ)*(gamma P J g.2.2 t:ℂ)) •
        (LinearMap.proj (a*b*t) : (ℕ→ℂ) →ₗ[ℂ] ℂ)

def otherModuli (P : Params) (x U eta : ℝ) : (ℕ→ℂ) →ₗ[ℂ] ℂ :=
  ∑ j∈P.words.attach \ selectedWords P,modulusWord P x U eta j.val

def otherKernel (P : Params) (x U eta : ℝ) (n : ℕ) : ℂ :=
  otherModuli P x U eta (fun q => residueKernel q P.N n)

/-- The earlier scalar, factorials, all three dyadic owners and every
surviving word are precisely this frequency-independent residue kernel. -/
theorem remaining_eq_kernel {order : ℕ} {zeta kap0 : ℝ} (I : Index order zeta kap0)
    (K : ℕ) (hu : 1<I.U) :
    remaining I K=functional (fibre I.bs I.i I.C)
      (fun y => otherKernel I.P I.x I.U I.eta (completeProduct y)) (originalMode I K) := by
  let S := fibre I.bs I.i I.C
  let w := originalMode I K
  let F := otherModuli I.P I.x I.U I.eta
  let kernel := fun (y : Fin (P4BOriginalMediumAtomFamily.size I.j+
    P4BOriginalMediumAtomFamily.size I.l)→ℕ) (q : ℕ) => residueKernel q I.P.N (completeProduct y)
  have word (j : {J // J∈I.P.words}) :
      wordTerm I K j=modulusWord I.P I.x I.U I.eta j.val (fun q => (I.atom K).discrepancy q) := by
    simpa only [wordTerm,boxedErrors,modulusWord,LinearMap.smul_apply,LinearMap.sum_apply,
      LinearMap.proj_apply,smul_eq_mul] using
      congrArg (fun v : ℂ => (restoring I.P I.x I.U I.eta j.val:ℂ)*v) (word_errors (onWord I j) K)
  have hlevel : (fun q => row S completeProduct w I.P.N q)=
      (scalar I:ℂ) • (fun q => (I.atom K).discrepancy q) :=
    funext (row_at_level I K hu)
  have hrows : (fun q => row S completeProduct w I.P.N q)=∑ y∈S,w y • kernel y := by
    funext q
    simp only [row,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,kernel]
  calc
    remaining I K=F (fun q => row S completeProduct w I.P.N q) := by
      rw [hlevel,map_smul]
      simp only [F,remaining,otherModuli,LinearMap.sum_apply,smul_eq_mul]
      exact congrArg (fun v : ℂ => (scalar I:ℂ)*v) (Finset.sum_congr rfl (fun j _ => word j))
    _=∑ y∈S,w y*F (kernel y) := by simp only [hrows,map_sum,map_smul,smul_eq_mul]
    _=_ := rfl

/-- Arbitrary accuracy before restoring the outer atlas. The three original
modulus owners and the native HB scalar have already spent fifteen logarithms. -/
theorem exists_free_mode_cost (K order A : ℕ) (omega T : ℝ) (ho : 0<omega)
    {zeta kappa kap0 : ℝ} (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∃ D : ℝ,0≤D ∧ ∀ᶠ N : ℕ in atTop,∀ I : Index order zeta kap0,
      I.P.N=N → I.P.omega=omega → I.P.T=T → I.eta=zeta →
      0≤I.P.e → (I.P.e:ℝ)≤1/2048 → 0<I.P.q → I.P.T≤zeta →
      0≤I.P.ell → 2*I.P.ell≤zeta/16 → I.U≤I.x^(1/16:ℝ) →
      ‖exactDiscrepancy (fibre I.bs I.i I.C) (products I.P) (fun d => (free I.P d:ℂ))
        completeProduct I.P.N (originalMode I K)-
        functional (fibre I.bs I.i I.C) (fun y => otherKernel I.P I.x I.U I.eta (completeProduct y))
          (originalMode I K)‖≤D*N/(Real.log (N:ℝ))^A := by
  let p := A+15
  have hp : 0<(p:ℝ) := by dsimp [p]; positivity
  obtain ⟨C,hC,HP⟩ := P4BOriginalShortMediumTriplePayment.eventually_short_three_signed
    K order p hp hz hz0 hk hkz ht ht1
  let D := C*localConstant p
  let M := feeConstant omega T
  have hD : 0≤D := mul_nonneg hC.le (localConstant_nonneg _)
  have hM : 0≤M := by dsimp [M,feeConstant]; positivity [dyadicConstant_pos]
  have hz1 : zeta≤1/400 := by linarith
  have hk1 : kappa≤zeta := by linarith
  refine ⟨M*2^15*D,by positivity,?_⟩
  filter_upwards [HP,eventually_width 1 (by norm_num),
    P4BOriginalMediumFibreSWWindow.eventually_window K order 1 hz hz1 hk hk1 ht ht1,
    P4BOriginalHighRankLiveFibreModes.eventually_fixed_live_window K hz hz1 hk hk1 ht ht1]
    with N Hpaid width HW HL
  intro I hIN hw hT hEta he he' hq hm hell hell' hshort
  subst N
  have hN : 1<I.P.N := by have hh := width.1; omega
  have hNr : 1<(I.P.N:ℝ) := by exact_mod_cast hN
  have hlog := Real.log_pos hNr
  have hs := P4BOriginalMediumFibreSWWindow.first_spec I.selected
  have hgeom := HW I.b_pos I.kap_pos I.s_pos I.gate _ _ I.cj I.ck I.bs I.i I.C I.live hs
  have hcomp := HL I.b_pos I.kap_pos I.s_pos I.gate _ _ I.cj I.ck I.bs I.i I.C I.live hs
  have hU : 1<I.U := hgeom.2.2.2.2.1
  have hx : 1<I.x := hgeom.2.1
  have hcomp' := complete_to_target p I.P.N hNr hx (show kappa≤1 by linarith)
    hcomp.2.2.1 I.scale_upper
  let E := D*I.P.N/(Real.log (I.P.N:ℝ))^p
  have hE : 0≤E := div_nonneg (mul_nonneg hD (Nat.cast_nonneg _)) (pow_nonneg hlog.le _)
  have boxes (j : {J // J∈I.P.words}) (hj : j∈tripleWords I) :
      ‖boxedErrors K (onWord I j)‖≤(pieces (onWord I j):ℝ)*E := by
    obtain ⟨h3,hlo⟩ := (Finset.mem_filter.mp hj).2
    apply boxed_le
    intro d hd f hf g hg
    have hatom := Hpaid (onWord I j) rfl hEta he he' hq hm hell hell' h3 hlo hshort d hd f hf g hg
    rw [Real.rpow_natCast] at hatom
    apply hatom.trans
    calc
      _=C*(I.x/(Real.log I.x)^p) := by ring
      _≤C*(localConstant p*I.P.N/(Real.log (I.P.N:ℝ))^p) :=
        mul_le_mul_of_nonneg_left hcomp' hC.le
      _=E := by dsimp only [E,D]; ring
  have h := free_difference I K hN hU E hE boxes he (hw.symm ▸ ho)
    (by linarith only [hell',hz0])
  rw [hw,hT,remaining_eq_kernel I K hU] at h
  apply h.trans
  have hL := (zero_le_one.trans (logScale_one_le (countingScale_one_le I.N_pos)))
  calc
    _≤(M*(2*Real.log (I.P.N:ℝ))^15)*E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hL width.2.2.2.2 15) hM) hE
    _=_ := by
      dsimp only [E,p]
      rw [pow_add]
      field_simp [hlog.ne'] <;> ring

end
end ImbalancedChen.P4BOriginalShortMediumWordKernel
