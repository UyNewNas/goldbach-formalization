import ImbalancedChen.P5OriginalPresievedOuterAtomArithmetic
import ImbalancedChen.P5ZU1011FourDimensionalSmoothBoxAtoms

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

One frozen-profile outer prime box has its OWN physical fibre coefficient.
This coefficient is not restricted to the original tuple source. Adjacent
label separation and the frozen residual prime ceiling prove multiplicity
one by unique factorization. The actual compact smooth weights and genuine
common-beta row then give unit amplitude; actual padded endpoints give
the physical support bound. No whole-family/profile gluing or PP follows.
-/

namespace ImbalancedChen.P5Z.OriginalPresievedOuterAtomCoefficient

noncomputable section
open scoped BigOperators
open Classical
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenCommonSmallParameters (selectedCells)
open OriginalOrdinaryCommonBetaModel OriginalPresievedOuterAtomSupport
open OriginalPresievedOuterAtomArithmetic OriginalCommonBetaActualParameters

def frozenSupport (n:ℕ) (eta:ℚ) (j:Grid n) (N:ℕ) (w:ℝ) : Finset ℕ :=
  actualSmallRoughModuli
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.rowD
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.rowZ
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N)) w
    (U1011OriginalSixteenJointNearCapCompiler.rowZ
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N)

abbrev OuterMark:=(Fin 4→ℕ)×ℕ

def outerMarks (n:ℕ) (eta:ℚ) (j:Grid n) (N:ℕ) (w:ℝ) (a b:Fin 4→ℝ) : Finset OuterMark :=
  actualPrimeBoxTuples N a b ×ˢ frozenSupport n eta j N w

def outerModulus (m:OuterMark) : ℕ := (∏i,m.1 i)*m.2

def outerSigma (n:ℕ) (eta:ℚ) (j:Grid n) (N:ℕ) (w ell:ℝ) (a b:Fin 4→ℝ)
    (inner:Bool) (delta:ℝ) (fine:ℕ) (cell:Grid fine) (q:ℕ) : ℝ :=
  ∑m∈(outerMarks n eta j N w a b).filter (fun m=>outerModulus m=q),
    frozenCoefficient n eta j N w ell m.2 *
      U1011FourDimensionalSmoothBoxAtoms.boxAtom inner delta fine cell (actualPrimeTupleLog N m.1)

private theorem box_product_injective {N:ℕ} {a b:Fin 4→ℝ} (hN:1≤N)
    (hsep:∀i:Fin 3,b i.succ≤a i.castSucc) :
    Set.InjOn (fun t:Fin 4→ℕ=>∏i,t i) (actualPrimeBoxTuples N a b:Set (Fin 4→ℕ)) := by
  intro t ht u hu heq
  have hprimeT:∀p∈List.ofFn t,Nat.Prime p:=by
    intro p hp
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hp
    exact (mem_actualPrimeBoxTuples_iff.mp ht i).1
  have hprimeU:∀p∈List.ofFn u,Nat.Prime p:=by
    intro p hp
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hp
    exact (mem_actualPrimeBoxTuples_iff.mp hu i).1
  have hp:(List.ofFn t).prod=(List.ofFn u).prod:=by simpa only [List.prod_ofFn] using heq
  have hperm:=(Nat.primeFactorsList_unique hp hprimeT).trans
    (Nat.primeFactorsList_unique (rfl:(List.ofFn u).prod=(List.ofFn u).prod) hprimeU).symm
  apply List.ofFn_injective
  exact hperm.eq_of_pairwise'
    (List.pairwise_ofFn.mpr (actualPrimeBoxTuples_strictAnti hN hsep ht))
    (List.pairwise_ofFn.mpr (actualPrimeBoxTuples_strictAnti hN hsep hu))

private theorem box_product_rough {N:ℕ} {a b:Fin 4→ℝ} {z:ℝ} {t:Fin 4→ℕ}
    (hN:1≤N) (hsep:∀i:Fin 3,b i.succ≤a i.castSucc)
    (ht:t∈actualPrimeBoxTuples N a b) (hz:∀i,z≤(t i:ℝ)) :
    RoughPrimeSupportedAt z (∏i,t i) := by
  have hprime:∀p∈List.ofFn t,Nat.Prime p:=by
    intro p hp
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hp
    exact (mem_actualPrimeBoxTuples_iff.mp ht i).1
  have hnd:=(List.nodup_ofFn.mpr (actualPrimeBoxTuples_injective hN hsep ht))
  have hprod:((List.ofFn t).toFinset.prod id)=(List.ofFn t).prod:=by
    simpa using List.prod_toFinset (fun p:ℕ=>p) hnd
  have hpf:(∏i,t i:ℕ).primeFactors=(List.ofFn t).toFinset:=by
    rw [←List.prod_ofFn,←hprod]
    exact Nat.primeFactors_prod (fun p hp=>hprime p (List.mem_toFinset.mp hp))
  refine ⟨Nat.ne_of_gt (Finset.prod_pos (fun i hi=>(mem_actualPrimeBoxTuples_iff.mp ht i).1.pos)),?_⟩
  intro p hp
  rw [hpf] at hp
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (List.mem_toFinset.mp hp)
  exact hz i

private theorem frozenSupport_small {n N r:ℕ} {eta:ℚ} {j:Grid n} {w:ℝ}
    (hw:w≤U1011OriginalSixteenJointNearCapCompiler.rowZ
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N)
    (hr:r∈frozenSupport n eta j N w) :
    SmallPrimeSupportedAt (U1011OriginalSixteenJointNearCapCompiler.rowZ
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N) r := by
  obtain ⟨⟨e,d⟩,hed,rfl⟩:=Finset.mem_image.mp hr
  obtain ⟨he,hd⟩:=Finset.mem_product.mp hed
  have heS:=actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ he
  have hdSF:=fixedRoughSupport_squarefree _ _ _ _ _ hd
  refine ⟨mul_ne_zero heS.1 hdSF.ne_zero,?_⟩
  rw [Nat.primeFactors_mul heS.1 hdSF.ne_zero]
  intro p hp
  rcases Finset.mem_union.mp hp with hp|hp
  · exact (heS.2 p hp).trans_le hw
  · exact mem_roughPrimeUniverse_upper (fixedRoughSupport_primeFactors_mem _ _ _ _ _ hd hp)

/-- This is an independent outer-box fibre proof, rather than an appeal
to source-owned top-four uniqueness. -/
theorem outerModulus_injective {n N:ℕ} {eta:ℚ} {nu epsilon:ℝ}
    (hN:1<N) (hnu:0<nu) (he:0<epsilon) (heBudget:epsilon<epsilonBudget n eta nu)
    (j:Grid n) (hj:j∈selectedCells n) (a b:Fin 4→ℝ)
    (hsep:∀i:Fin 3,b i.succ≤a i.castSucc)
    (hcut:∀i,(U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ)≤a i) :
    Set.InjOn outerModulus
      (outerMarks n eta j N ((N:ℝ)^(nu*epsilon^2)) a b:Set OuterMark) := by
  have hNge:1≤N:=by omega
  have hn:(1:ℝ)<N:=by exact_mod_cast hN
  have hw:=(common_parameters_on_selected_cell hN hnu he heBudget j hj).1
  have hrough (t:Fin 4→ℕ) (ht:t∈actualPrimeBoxTuples N a b) :=
    box_product_rough hNge hsep ht (fun i=>
      (Real.rpow_le_rpow_of_exponent_le hn.le (hcut i)).trans
        (mem_actualPrimeBoxTuples_iff.mp ht i).2.2.1)
  intro m hm k hk hq
  obtain ⟨hmt,hmr⟩:=Finset.mem_product.mp hm
  obtain ⟨hkt,hkr⟩:=Finset.mem_product.mp hk
  have hp:(m.2,∏i,m.1 i)=(k.2,∏i,k.1 i):=smallRough_factorization_unique
    (frozenSupport_small hw hmr) (hrough m.1 hmt)
    (frozenSupport_small hw hkr) (hrough k.1 hkt)
    (by simpa only [outerModulus,Nat.mul_comm] using hq)
  have hprod:=congrArg Prod.snd hp
  have ht:=box_product_injective hNge hsep hmt hkt hprod
  exact Prod.ext ht (congrArg Prod.fst hp)

theorem outerSigma_eq_mark {n N:ℕ} {eta:ℚ} {nu epsilon:ℝ}
    (hN:1<N) (hnu:0<nu) (he:0<epsilon) (heBudget:epsilon<epsilonBudget n eta nu)
    (j:Grid n) (hj:j∈selectedCells n) (a b:Fin 4→ℝ)
    (hsep:∀i:Fin 3,b i.succ≤a i.castSucc)
    (hcut:∀i,(U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ)≤a i)
    (inner:Bool) (delta:ℝ) (fine:ℕ) (cell:Grid fine) {m:OuterMark}
    (hm:m∈outerMarks n eta j N ((N:ℝ)^(nu*epsilon^2)) a b) :
    outerSigma n eta j N ((N:ℝ)^(nu*epsilon^2)) (nu*epsilon) a b inner delta fine cell (outerModulus m)=
      frozenCoefficient n eta j N ((N:ℝ)^(nu*epsilon^2)) (nu*epsilon) m.2 *
        U1011FourDimensionalSmoothBoxAtoms.boxAtom inner delta fine cell (actualPrimeTupleLog N m.1) := by
  have hf:(outerMarks n eta j N ((N:ℝ)^(nu*epsilon^2)) a b).filter
      (fun k=>outerModulus k=outerModulus m)={m}:=by
    ext k
    constructor
    · intro hk
      obtain ⟨hk,hq⟩:=Finset.mem_filter.mp hk
      exact Finset.mem_singleton.mpr
        (outerModulus_injective hN hnu he heBudget j hj a b hsep hcut hk hm hq)
    · intro hk
      have heq:=Finset.mem_singleton.mp hk
      subst k
      exact Finset.mem_filter.mpr ⟨hm,rfl⟩
  simp only [outerSigma,hf,Finset.sum_singleton]

/-- Every physical integer receives at most one genuine frozen-row term.
No unknown one-bounded gamma or source-ownership premise is supplied. -/
theorem outerSigma_abs_le_one {n N:ℕ} {eta:ℚ} {nu epsilon:ℝ}
    (hN:1<N) (hnu:0<nu) (he:0<epsilon) (heBudget:epsilon<epsilonBudget n eta nu)
    (j:Grid n) (hj:j∈selectedCells n) (a b:Fin 4→ℝ)
    (hsep:∀i:Fin 3,b i.succ≤a i.castSucc)
    (hcut:∀i,(U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ)≤a i)
    (inner:Bool) (delta:ℝ) (fine:ℕ) (cell:Grid fine) (q:ℕ) :
    |outerSigma n eta j N ((N:ℝ)^(nu*epsilon^2)) (nu*epsilon) a b inner delta fine cell q|≤1 := by
  by_cases hq:q∈(outerMarks n eta j N ((N:ℝ)^(nu*epsilon^2)) a b).image outerModulus
  · obtain ⟨m,hm,rfl⟩:=Finset.mem_image.mp hq
    rw [outerSigma_eq_mark hN hnu he heBudget j hj a b hsep hcut inner delta fine cell hm]
    have hrow:|frozenCoefficient n eta j N ((N:ℝ)^(nu*epsilon^2)) (nu*epsilon) m.2|≤1:=
      actualSmallRoughRho_abs_le_one _ N _ _ _ _ _
    have hb:=U1011FourDimensionalSmoothBoxAtoms.boxAtom_bounds inner delta fine cell
      (actualPrimeTupleLog N m.1)
    rw [abs_mul,abs_of_nonneg hb.1]
    exact (mul_le_mul hrow hb.2 hb.1 (by norm_num)).trans_eq (one_mul 1)
  · have hz:outerSigma n eta j N ((N:ℝ)^(nu*epsilon^2)) (nu*epsilon) a b inner delta fine cell q=0:=by
      apply Finset.sum_eq_zero
      intro m hm
      obtain ⟨hm,hqm⟩:=Finset.mem_filter.mp hm
      exact (hq (Finset.mem_image.mpr ⟨m,hm,hqm⟩)).elim
    rw [hz]
    norm_num

end
end ImbalancedChen.P5Z.OriginalPresievedOuterAtomCoefficient
