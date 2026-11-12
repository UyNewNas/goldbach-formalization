import ImbalancedChen.P4AOriginalFiniteFallbackLocalScale

namespace ImbalancedChen.P4AOriginalFiniteFallbackPhysicalSelected
noncomputable section
open scoped Classical
open P4AUpperTaggedParityCompiler P4AHeldTaggedCompilerSupport
open P4AOriginalFiniteFallbackPolicy (F)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalFiniteFallbackSelectedMask (Mask front selected remaining value)
open P4AOriginalFiniteFallbackNaturalEndpoints (tag)
open P4AOriginalFiniteFallbackLocalScale (slack)
open P4BUpperSelectedBoxCapacity (endpoints)

def word (N : ℕ) (tau : ℝ) (d : ℕ) := d.primeFactorsList.reverse.map (tag N tau)

def witnesses (f : List ℕ→Bool) (N cap : ℕ) (w z tau : ℝ) (J : List ℤ) :=
  (rawSupport f N cap w z).filter (fun u => primeWordLabel N tau u=J)

def pick (f : List ℕ→Bool) (N cap : ℕ) (w z tau : ℝ) (J : List ℤ) : ℕ :=
  let S := witnesses f N cap w z tau J
  if h : S.Nonempty then S.min' h else 1

/-- Both actual beta signs, the occupied ALL/ANY cell, a retained rough
representative and its SAME whole rectangular label sequence. -/
theorem representative (m n N cap : ℕ) (delta w z tau L : ℝ) (d : OriginalData) {q : ℕ}
    (hq : P4AUpperTaggedBetaAttachment.rho (F (bank m) delta n d w N) (fun _ => [])
      N cap ((N:ℝ)^w) z tau L q≠0) :
    ∃ a b u : ℕ, a*b=q ∧ (a:ℝ)<L ∧
      coefficient (F (bank m) delta n d w N) (fun _ => []) N cap ((N:ℝ)^w) z tau b≠0 ∧
      u∈rawSupport (F (bank m) delta n d w N) N cap ((N:ℝ)^w) z ∧
      u∈cell (fun _ => []) N cap ((N:ℝ)^w) z tau b ∧ word N tau u=word N tau b ∧
      u=pick (F (bank m) delta n d w N) N cap ((N:ℝ)^w) z tau (primeWordLabel N tau b) := by
  let f := F (bank m) delta n d w N
  let y := (N:ℝ)^w
  let c := coefficient f (fun _ => []) N cap y z tau
  have hmem : q∈P4AUpperTaggedBetaAttachment.support N cap y z := by
    by_contra h
    exact hq (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ h)
  obtain ⟨⟨a,b⟩,hm,hprod⟩ := Finset.mem_image.mp hmem
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hm
  have H := P4AUpperTaggedBetaAttachment.rho_at_product f (fun _ => []) N cap y z tau L ha hb
  have hp : c b*(if 0≤c b then actualSmallRosserPlus N cap y L a else actualSmallRosserMinus N cap y L a)≠0 := by
    rw [←H,hprod]; exact hq
  obtain ⟨hc,hbeta⟩ := mul_ne_zero_iff.mp hp
  have hal : (a:ℝ)<L := by
    split_ifs at hbeta
    · exact (actualSmallRosserPlus_active hbeta).2.1
    · exact (actualSmallRosserMinus_active hbeta).2.1
  obtain ⟨u,hu,hcell,_,_⟩ := active_has_raw_witness f (fun _ => []) N cap y z tau hc
  have hw := congrArg Prod.snd (Finset.mem_filter.mp hcell).2
  change primeWordLabel N tau u=primeWordLabel N tau b at hw
  let J := primeWordLabel N tau b
  let S := witnesses f N cap y z tau J
  have hn : S.Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,hw⟩⟩
  let g := pick f N cap y z tau J
  have hg : g∈S := by
    change (if h : S.Nonempty then S.min' h else 1)∈S
    rw [dif_pos hn]
    exact S.min'_mem hn
  obtain ⟨hr,heq⟩ := Finset.mem_filter.mp hg
  have hG : g∈cell (fun _ => []) N cap y z tau b := Finset.mem_filter.mpr
    ⟨rawSupport_subset_universe _ _ _ _ _ hr,Prod.ext rfl heq⟩
  refine ⟨a,b,g,hprod,hal,hc,hr,hG,?_,rfl⟩
  simpa only [J,word,tag,primeWordLabel,P2LowerFiniteCellRounding.label,List.map_map,Function.comp_def] using
    congrArg (List.map Int.toNat) heq

def head (J : List ℕ) (i : Fin 3) := J.getD i.val 0

def upperGroups (N : ℕ) (tau D A : ℝ) (b : Mask) (J : List ℕ) :=
  endpoints D A (actualPrimeFineLabelIntegerUpper N tau) (selected b (head J))
    (remaining b (head J) (J.drop 3)) J

theorem groups_at_word (N : ℕ) (tau D A : ℝ) (b : Mask) (p : Fin 3 → ℕ) (xs : List ℕ) :
    upperGroups N tau D A b ((front p xs).map (tag N tau))=
      endpoints D A (actualPrimeFineLabelIntegerUpper N tau) ((selected b p).map (tag N tau))
        ((remaining b p xs).map (tag N tau)) ((front p xs).map (tag N tau)) := by
  cases b <;> rfl

/-- The full Type II interval of paragraph eight, actual small factor and
whole exposed label word. A, every chosen group and its upper endpoint
are determined before a tuple from the box or a distribution test is
selected. Primitive local scale conditions are deliberately explicit. -/
theorem medium (m n N cap u b a : ℕ) (delta w z tau ell : ℝ) (d : OriginalData)
    (hd : 0<delta) (he : 0≤d.e) (hN : 1<N) (hw : 0<w) (ht : 0<tau)
    {eta : ℝ} (heta : 0<eta) (hsmall : eta≤slack m) (hbudget : tau*((J0 w:ℝ)+1)≤eta)
    (hu : u∈rawSupport (F (bank m) delta n d w N) N cap ((N:ℝ)^w) z)
    (hJ : word N tau u=word N tau b) (hbeta : (a:ℝ)<(N:ℝ)^ell) (hell : 0≤ell) (hell' : 2*ell≤eta/16)
    (kind : Mask) (p : Fin 3 → ℕ) (tail : List ℕ) (hword : u.primeFactorsList.reverse=front p tail)
    {M : ℚ} (hit : value m kind N p=some M)
    {x kappa U : ℝ} (hx : 1<x) (hk : kappa≤eta) (hlo : x^(1-eta)≤N)
    (hhi : (N:ℝ)≤x^(1+eta)) (hU0 : x^(2*eta)≤U) (hU1 : U≤x^(1/3+eta/2)) :
    let A := U/x^eta
    let D := x^((M:ℝ)+4*eta)
    let abc := upperGroups N tau D A kind (word N tau b)
    let Q3 := abc.2.2*x^(2*ell)
    (a:ℝ)≤x^(2*ell) ∧ abc.1<U*x^(-eta/100) ∧ U^2*abc.2.1*Q3^2<x^(1-8*(eta/100)) ∧
      x^(7*(1+3*kappa)/32)*U*abc.1*abc.2.1^5*Q3^2<x^(2-15*(eta/100)) ∧
      U^(23/16:ℝ)*abc.1*abc.2.1^(73/16:ℝ)*Q3^(39/16:ℝ)<x^(2-15*(eta/100)) := by
  let A := U/x^eta
  let D := x^((M:ℝ)+4*eta)
  have hx0 := zero_lt_one.trans hx
  have hex := Real.rpow_pos_of_pos hx0 eta
  have hA : 1≤A := (le_div_iff₀ hex).mpr (by
    rw [one_mul]; exact (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith : eta≤2*eta)).trans hU0)
  have hau : A≤x^(1/3-eta/2) := (div_le_iff₀ hex).mpr (by
    rw [←Real.rpow_add hx0,show (1/3:ℝ)-eta/2+eta=1/3+eta/2 by ring]; exact hU1)
  have B := P4AOriginalFiniteFallbackLocalScale.selected_local m n N cap u delta w z tau d hd he hN hw ht
    heta hsmall hbudget hu kind p tail hword hit hx hk hlo hhi hA hau hell'
  have Ueq : A*x^eta=U := div_mul_cancel₀ _ hex.ne'
  have J : word N tau b=(front p tail).map (tag N tau) := by rw [←hJ,word,hword]
  dsimp only at B ⊢
  rw [J,groups_at_word]
  have hf : eta≤1/400 := hsmall.trans (min_le_right _ _)
  constructor
  · apply hbeta.le.trans
    calc
      (N:ℝ)^ell ≤ (x^(1+eta))^ell := Real.rpow_le_rpow (Nat.cast_nonneg _) hhi hell
      _ = x^((1+eta)*ell) := (Real.rpow_mul hx0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by nlinarith [mul_nonneg (show 0≤1-eta by linarith) hell])
  · simpa only [Ueq] using B

end
end ImbalancedChen.P4AOriginalFiniteFallbackPhysicalSelected
