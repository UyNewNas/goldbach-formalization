import ImbalancedChen.P1OriginalSingletonShortMediumTriplePayment
import ImbalancedChen.P1OriginalSingletonMediumRestoringBudget
import ImbalancedChen.P4BOriginalShortMediumWordKernel

/-! The surviving singleton words on the complete signed fibre. The public
complete-modulus kernel is frequency independent. Its equality with every
raised-action singleton word uses both real and imaginary tests. -/
namespace ImbalancedChen.P1OriginalSingletonShortMediumSignedRow
noncomputable section
open Classical Filter
open scoped BigOperators
open P1OriginalSingletonMediumLowThreeAdmissible (Index size)
open P1OriginalSingletonMediumReconstruction (originalMode scalar convolution onWord boxedErrors
  row_at_level word_errors all_free_words)
open P1OriginalSingletonMediumFourier (frequencyMode)
open P1OriginalSingletonMediumRestoringBudget (pieces modulusCost scalar_cost)
open P4BOriginalHigherLowTensor (word restore)
open P4BOriginalCollisionThirdFactor (splitAt)
open P4BOriginalCollisionTensor (products free)
open P4BOriginalCollisionKernel (row)
open P4BOriginalHighRankComplementBlocks (fibre)
open P4BOriginalShortMediumWordKernel (selectedWords modulusWord otherModuli otherKernel)
open P4BOriginalNativeTargetPayment (localConstant localConstant_nonneg complete_to_target)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open PrimeProducts.MellinInsertion20261028 (functional exactDiscrepancy residueKernel)

variable {order : ℕ} {kap zeta kap0 : ℝ} (I : Index order kap zeta kap0)

def otherMode (K : ℕ) (xi : Fin (size I.j)→ℝ) : ℂ :=
  functional (fibre I.bv I.i I.C)
    (fun y => otherKernel I.P I.x I.U zeta (completeProduct y)) (frequencyMode I K xi)

private theorem word_eq_kernel (K : ℕ) (hN : 1<I.P.N) (j : {J // J∈I.P.words}) :
    (restore I.P j.val (onWord I j).groups:ℂ)*boxedErrors (onWord I j) K=
      modulusWord I.P I.x I.U zeta j.val (convolution I K) := by
  let S := (onWord I j).groups
  have eqword (f : ℕ→ℝ) : word I.P j.val S f=word I.P j.val (splitAt I.P I.x I.U zeta j.val) f :=
    (P4BOriginalHigherActionGroups.same_word I.P hN I.x I.U zeta j.property f).trans
      (P4BOriginalHigherLowTensor.same_word I.P I.x I.U zeta j.property f)
  rw [word_errors]
  apply Complex.ext
  · simpa only [word,modulusWord,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.proj_apply,
      smul_eq_mul,←Complex.ofReal_mul,Complex.re_ofReal_mul,Complex.re_sum] using
      eqword (fun q => (convolution I K q).re)
  · simpa only [word,modulusWord,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.proj_apply,
      smul_eq_mul,←Complex.ofReal_mul,Complex.im_ofReal_mul,Complex.im_sum] using
      eqword (fun q => (convolution I K q).im)

/-- The same scalar and the same surviving labelled words as in the actual
singleton reconstruction, for every retained mode. -/
theorem remaining_reconstruction (K : ℕ) (hN : 1<I.P.N) (hu : 1<I.U) :
    (scalar I:ℂ)*(∑ j∈I.P.words.attach \ selectedWords I.P,
      (restore I.P j.val (onWord I j).groups:ℂ)*boxedErrors (onWord I j) K)=otherMode I K I.xi := by
  let S := fibre I.bv I.i I.C
  let w := originalMode I K
  let F := otherModuli I.P I.x I.U zeta
  let ker := fun (y : Fin (size I.j)→ℕ) (q : ℕ) => residueKernel q I.P.N (completeProduct y)
  have hrow : (fun q => row S completeProduct w I.P.N q)=(scalar I:ℂ) • convolution I K :=
    funext (row_at_level I K hu)
  have hsum : (fun q => row S completeProduct w I.P.N q)=∑ y∈S,w y • ker y := by
    funext q
    simp only [row,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,ker]
  calc
    _=F (fun q => row S completeProduct w I.P.N q) := by
      rw [hrow,map_smul]
      simp only [F,otherModuli,LinearMap.sum_apply,smul_eq_mul]
      exact congrArg (fun v : ℂ => (scalar I:ℂ)*v)
        (Finset.sum_congr rfl (fun j _ => word_eq_kernel I K hN j))
    _=∑ y∈S,w y*F (ker y) := by simp only [hsum,map_sum,map_smul,smul_eq_mul]
    _=_ := rfl

private theorem mode_restoration (K : ℕ) (hkap : kap<1) (hN : 1<I.P.N) (hu : 1<I.U)
    {E : ℝ} (hE : 0≤E)
    (paid : ∀ j∈selectedWords I.P,∀ d∈(onWord I j).firstOwners,
      ∀ f∈(onWord I j).secondOwners,∀ g∈(onWord I j).thirdOwners,
        ‖((onWord I j).atom K d f g).signedError‖≤E) :
    ‖exactDiscrepancy (fibre I.bv I.i I.C) (products I.P) (fun q => (free I.P q:ℂ))
      completeProduct I.P.N (originalMode I K)-otherMode I K I.xi‖≤(scalar I*modulusCost I)*E := by
  let W := I.P.words.attach
  let T := selectedWords I.P
  let term := fun j : {J // J∈I.P.words} =>
    (restore I.P j.val (onWord I j).groups:ℂ)*boxedErrors (onWord I j) K
  let cost := fun j : {J // J∈I.P.words} =>
    |restore I.P j.val (onWord I j).groups|*(pieces (onWord I j):ℝ)
  have hsub : T⊆W := Finset.filter_subset _ _
  have hparts : (∑ j∈W,term j)=(∑ j∈W \ T,term j)+(∑ j∈T,term j) :=
    (Finset.sum_sdiff hsub).symm
  have boxes (j) (hj : j∈T) : ‖boxedErrors (onWord I j) K‖≤(pieces (onWord I j):ℝ)*E := by
    let B := onWord I j
    calc
      _≤∑ d∈B.firstOwners,∑ f∈B.secondOwners,∑ g∈B.thirdOwners,E := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro d hd
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro f hf
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun g hg => paid j hj d hd f hf g hg)
      _=_ := by
        simp only [B,pieces,Finset.sum_const,nsmul_eq_mul,Nat.cast_mul]
        ring
  have hcost : (∑ j∈T,cost j)≤modulusCost I :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ =>
      mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have hterms : ‖∑ j∈T,term j‖≤modulusCost I*E := by
    apply (norm_sum_le _ _).trans
    calc
      _≤∑ j∈T,cost j*E := by
        apply Finset.sum_le_sum
        intro j hj
        dsimp only [term,cost]
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_assoc]
        exact mul_le_mul_of_nonneg_left (boxes j hj) (abs_nonneg _)
      _≤_ := by rw [←Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hcost hE
  rw [all_free_words I K hN hu,←remaining_reconstruction I K hN hu]
  change ‖(scalar I:ℂ)*(∑ j∈W,term j)-(scalar I:ℂ)*(∑ j∈W \ T,term j)‖≤_
  rw [←mul_sub,hparts,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (scalar_cost I hkap).1]
  exact (mul_le_mul_of_nonneg_left hterms (scalar_cost I hkap).1.le).trans_eq (mul_assoc _ _ _).symm

/-- The factor scalar*modulusCost is the existing nonnegative restoring
inventory for this very fibre and is independent of the frequency. -/
theorem exists_mode_cost (K order p : ℕ) (hp : 0<p)
    {kap zeta kappa kap0 : ℝ} (hkap : kap<1) (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∃ D : ℝ,0≤D ∧ ∀ᶠ N : ℕ in atTop,∀ I : Index order kap zeta kap0,
      I.P.N=N → 0≤I.P.e → (I.P.e:ℝ)≤1/2048 → 0<I.P.q →
      I.P.T≤zeta → 0≤I.P.ell → 2*I.P.ell≤zeta/16 → I.U≤I.x^(1/16:ℝ) →
      ‖exactDiscrepancy (fibre I.bv I.i I.C) (products I.P) (fun q => (free I.P q:ℂ))
        completeProduct I.P.N (originalMode I K)-otherMode I K I.xi‖≤
        (scalar I*modulusCost I)*(D*N/(Real.log (N:ℝ))^p) := by
  obtain ⟨C,hC,HP⟩ := P1OriginalSingletonShortMediumTriplePayment.eventually_short_three_signed
    K order p (by exact_mod_cast hp) hkap hz hz0 hk hkz ht ht1
  let D := C*localConstant p
  have hD : 0≤D := mul_nonneg hC.le (localConstant_nonneg _)
  have hz1 : zeta≤1/400 := by linarith
  refine ⟨D,hD,?_⟩
  filter_upwards [HP,P1OriginalSingletonMediumWindow.eventually_original_medium_window K 1
    hkap hz hz1 hk ht ht1,eventually_ge_atTop (2:ℕ)] with N HA HW hNN
  intro I hn he he' hq hT hell hell' hshort
  subst N
  have hN : 1<I.P.N := by omega
  have hNr : 1<(I.P.N:ℝ) := by exact_mod_cast hN
  obtain ⟨_,hx,_,hNx,_,hu,_⟩ := HW I.cj (size I.j) I.bv I.i I.C I.live I.selected_ofFn
  have hcap := (I.scale_upper hkap).trans
    (mul_le_mul_of_nonneg_right (show (2:ℝ)≤Real.exp 1 by linarith only [Real.add_one_le_exp 1])
      (Nat.cast_nonneg I.P.N))
  have hg := complete_to_target p I.P.N hNr hx (show kappa≤1 by linarith) hNx hcap
  apply mode_restoration I K hkap hN hu (div_nonneg (mul_nonneg hD (Nat.cast_nonneg _))
    (pow_nonneg (Real.log_pos hNr).le _))
  intro j hj d hd f hf g hg'
  obtain ⟨h3,hl⟩ := (Finset.mem_filter.mp hj).2
  have h := HA (onWord I j) rfl he he' hq hT hell hell' h3 hl hshort d hd f hf g hg'
  rw [Real.rpow_natCast] at h
  apply h.trans
  calc
    _=C*(I.x/(Real.log I.x)^p) := by ring
    _≤C*(localConstant p*I.P.N/(Real.log (I.P.N:ℝ))^p) := mul_le_mul_of_nonneg_left hg hC.le
    _=D*I.P.N/(Real.log (I.P.N:ℝ))^p := by dsimp only [D]; ring

end
end ImbalancedChen.P1OriginalSingletonShortMediumSignedRow
