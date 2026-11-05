import ImbalancedChen.P3SmoothScalarJets
import ImbalancedChen.P3HBLogSourceDictionary
import ImbalancedChen.P3U5ProductChartMixedL1

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
The previous concrete product chart times one HB log ratio per ORIGINAL
GROUP. Slots, group products, complete trim and the original rho are kept.
A smooth compact extension is used off the admitted source only; equality
on that source is proved below. This is not the full arbitrary W profile.
-/
namespace ImbalancedChen.P3U5HBLogChart
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P3AffineTransitionJets P3SmoothScalarJets P3U5RootAtlas
open P3U5LogChartDerivativeBudget P3U5ProductChartDerivativeBudget
open P3U5PhysicalProductChart P3HBLogSourceDictionary

abbrev HBAtom (d g : ℕ) := Sum (ProductAtom d g) (Fin g × Bool)

def hbKind {d g : ℕ} : HBAtom d g → P3HBLogScalarProfiles.Kind
  | .inl j => match productKind j with
    | .transition => .transition
    | .product => .product
  | .inr (_,false) => .logSlot
  | .inr (_,true) => .inverseGroup

def hbOffsets {d g : ℕ} (ell : ℝ) (R : Fin 2 → ℝ) (m : ℕ)
    (b : Fin g → ℝ) (trim : ℝ) (u : Fin d → ℝ) (v : Fin g → ℝ)
    (pick : Fin g → Fin d) : HBAtom d g → ℝ
  | .inl j => productOffsets ell R m b trim j
  | .inr (j,false) => u (pick j)/ell
  | .inr (j,true) => v j/ell

def hbSlopes {d g : ℕ} (ell : ℝ) (slot : Fin d → Option (Fin 2))
    (m : ℕ) (group : Fin d → Fin g) (pick : Fin g → Fin d) : HBAtom d g → Fin d → ℝ
  | .inl j,i => productSlopes ell slot m group j i
  | .inr (j,false),i => if i=pick j then (m+1 : ℝ)⁻¹/ell else 0
  | .inr (j,true),i => if group i=j then (m+1 : ℝ)⁻¹/ell else 0

def logFactorExpr (d g : ℕ) : Expr (HBAtom d g) d :=
  exprProduct (List.ofFn (fun j : Fin g =>
    Expr.mul (.step (.inr (j,false)) 0) (.step (.inr (j,true)) 0)))

def hbExpr (d g : ℕ) (l : Lane) : Expr (HBAtom d g) d :=
  .mul (P3LogProductTransitionJets.rename Sum.inl (productExpr d g l)) (logFactorExpr d g)

def hbFactor {d g : ℕ} (a ell : ℝ) (group : Fin d → Fin g)
    (u : Fin d → ℝ) (v : Fin g → ℝ) (pick : Fin g → Fin d) (x : Point d) : ℝ :=
  ∏ j,P3HBLogScalarProfiles.logProfile ((u (pick j)+x (pick j))/ell)*
    P3HBLogScalarProfiles.inverseLogProfile a ((v j+groupSum group x j)/ell)

def hbProfile {d g : ℕ} (a ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (u : Fin d → ℝ) (v : Fin g → ℝ)
    (pick : Fin g → Fin d) (m : ℕ) (l : Lane) (x : Point d) : ℝ :=
  productProfile ell R slot group b trim m l x*hbFactor a ell group u v pick x

theorem hb_log_argument {d g : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (u : Fin d → ℝ) (v : Fin g → ℝ)
    (pick : Fin g → Fin d) (m : ℕ) (j : Fin g) (which : Bool) (x : Point d) :
    affine (hbOffsets ell R m b trim u v pick) (hbSlopes ell slot m group pick)
      (m+1 : ℝ) (.inr (j,which)) x =
      if which then (v j+groupSum group x j)/ell else (u (pick j)+x (pick j))/ell := by
  have hm : (m+1 : ℝ) ≠ 0 := by positivity
  by_cases he : ell=0
  · subst ell
    cases which <;> simp [affine,hbOffsets,hbSlopes]
  cases which
  · simp only [affine,hbOffsets,hbSlopes,ite_mul,zero_mul,Finset.sum_ite_eq',
      Finset.mem_univ,if_true,Bool.false_eq_true,if_false]
    simp only [div_eq_mul_inv]
    field_simp [hm,he] <;> ring
  · have hsum : (∑ i,(if group i=j then (m+1 : ℝ)⁻¹/ell else 0)*x i) =
        ((m+1 : ℝ)⁻¹/ell)*groupSum group x j := by
      simp only [groupSum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp
    simp only [affine,hbOffsets,hbSlopes,hsum,if_true]
    simp only [div_eq_mul_inv]
    field_simp [hm,he] <;> ring

private theorem evalS_exprProduct {ι : Type*} {d : ℕ} (es : List (Expr ι d))
    (f : ι → ℝ → ℝ) (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ) (x : Point d) :
    evalS f b a s (exprProduct es) x=(es.map (fun e => evalS f b a s e x)).prod := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [exprProduct,evalS,List.map_cons,List.prod_cons,ih]

theorem eval_hbExpr {d g : ℕ} (a ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (u : Fin d → ℝ) (v : Fin g → ℝ)
    (pick : Fin g → Fin d) (m : ℕ) (l : Lane) :
    evalS (P3HBLogScalarProfiles.scalar a ∘ hbKind)
      (hbOffsets ell R m b trim u v pick) (hbSlopes ell slot m group pick)
      (m+1 : ℝ) (hbExpr d g l) = hbProfile a ell R slot group b trim u v pick m l := by
  funext x
  have hold : evalS (P3HBLogScalarProfiles.scalar a ∘ hbKind)
      (hbOffsets ell R m b trim u v pick) (hbSlopes ell slot m group pick) (m+1 : ℝ)
      (P3LogProductTransitionJets.rename Sum.inl (productExpr d g l)) x =
      productProfile ell R slot group b trim m l x := by
    rw [evalS_rename_eq_evalK _ _ _ _ _ _ productKind (by
      intro j
      cases h : productKind j <;>
        simp [Function.comp_apply,hbKind,h,P3HBLogScalarProfiles.scalar,
          P3LogProductTransitionJets.scalar])]
    exact congrFun (eval_productExpr ell R slot group b trim m l) x
  rw [hbProfile,hbExpr,evalS,hold,logFactorExpr,evalS_exprProduct,List.map_ofFn,List.prod_ofFn]
  congr 1
  unfold hbFactor
  apply Finset.prod_congr rfl
  intro j hj
  simp only [evalS,iteratedDeriv_zero,Function.comp_apply,hbKind,P3HBLogScalarProfiles.scalar,
    hb_log_argument,Bool.false_eq_true,if_false,if_true,hbFactor]

theorem hbSlopes_bound {d g : ℕ} {ell : ℝ} (hell : 1 ≤ ell)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (pick : Fin g → Fin d) (m : ℕ) (j : HBAtom d g) (i : Fin d) :
    |hbSlopes ell slot m group pick j i| ≤ 2 := by
  have he : 0 < ell := by linarith
  have hm : (1 : ℝ) ≤ m+1 := by linarith [Nat.cast_nonneg m]
  have hinv : |(m+1 : ℝ)⁻¹/ell| ≤ 2 := by
    rw [abs_div,abs_inv,abs_of_pos (by positivity : (0 : ℝ)<m+1),abs_of_pos he,
      inv_eq_one_div,div_div]
    apply (div_le_iff₀ (mul_pos (by positivity) he)).mpr
    nlinarith
  cases j with
  | inl j => exact productSlopes_bound hell slot group m j i
  | inr jb =>
      rcases jb with ⟨j,b⟩
      cases b <;> dsimp [hbSlopes] <;> split_ifs
      all_goals first | exact hinv | norm_num

/-- Source-level identity: the designated numerator may be a unit; the
inverse always belongs to the positive original group, never that unit. -/
theorem hbFactor_eq_original {d g : ℕ} {a ell : ℝ} (ha : 0 < a) (hell : 0 < ell)
    (U : Fin d → ℝ) (hU : ∀ i,0 < U i) (group : Fin d → Fin g)
    (pick : Fin g → Fin d) (x : Point d)
    (hslot : ∀ i,0 ≤ Real.log (U i*Real.exp (x i))/ell ∧
      Real.log (U i*Real.exp (x i))/ell ≤ 2)
    (hgroup : ∀ j,a ≤ Real.log (groupProduct group (fun i => U i*Real.exp (x i)) j)/ell ∧
      Real.log (groupProduct group (fun i => U i*Real.exp (x i)) j)/ell ≤ 2) :
    hbFactor a ell group (fun i => Real.log (U i))
      (fun j => Real.log (groupBase U group j)) pick x =
      originalLogFactor group pick (fun i => U i*Real.exp (x i)) := by
  have hi (i : Fin d) : Real.log (U i*Real.exp (x i))=Real.log (U i)+x i := by
    rw [Real.log_mul (hU i).ne' (Real.exp_pos _).ne',Real.log_exp]
  have hg (j : Fin g) :
      Real.log (groupProduct group (fun i => U i*Real.exp (x i)) j) =
        Real.log (groupBase U group j)+groupSum group x j := by
    change Real.log (∏ i,if group i=j then U i*Real.exp (x i) else 1)=_
    rw [← groupValue_eq_slotProduct,groupValue,
      Real.log_mul (groupBase_pos U hU group j).ne' (Real.exp_pos _).ne',Real.log_exp]
  rw [← normalized_product_eq_original ha hell group pick _ hslot hgroup]
  simp only [normalizedLogFactor,hbFactor,hi,hg]

/-- The compact extension agrees with the physical log-ratio multiplier
on every admitted source point. Outside that domain no equality is claimed. -/
theorem hbProfile_eq_physical {d g : ℕ} {a ell : ℝ} (ha : 0 < a) (hell : 0 < ell)
    (U : Fin d → ℝ) (hU : ∀ i,0 < U i) (R : Fin g → ℝ) (hR : ∀ j,0 < R j)
    (group : Fin d → Fin g) (pair : Fin 2 → Fin g) (hne : pair 0 ≠ pair 1)
    (pick : Fin g → Fin d) {T : ℝ} (hT : 0 < T) (m : ℕ) (l : Lane) (x : Point d)
    (hslot : ∀ i,0 ≤ Real.log (U i*Real.exp (x i))/ell ∧
      Real.log (U i*Real.exp (x i))/ell ≤ 2)
    (hgroup : ∀ j,a ≤ Real.log (groupProduct group (fun i => U i*Real.exp (x i)) j)/ell ∧
      Real.log (groupProduct group (fun i => U i*Real.exp (x i)) j)/ell ≤ 2) :
    hbProfile a ell (fun j => groupBase U group (pair j)) (pairSlots group pair) group
      (fun j => Real.log (groupBase U group j/R j))
      (Real.log ((∏ j,groupBase U group j)/T)) (fun i => Real.log (U i))
      (fun j => Real.log (groupBase U group j)) pick m l x =
      physicalProfile ell (groupBase U group) R group pair T m l x *
        originalLogFactor group pick (fun i => U i*Real.exp (x i)) := by
  rw [hbProfile,hbFactor_eq_original ha hell U hU group pick x hslot hgroup,
    ← physicalProfile_eq_productProfile ell (groupBase U group) R
      (groupBase_pos U hU group) hR group pair hne hT]

/-- The paper's power floor and O(N) complete size supply the extension
core. No normalized-log, nonempty-group or inverse-log licence remains. -/
theorem eventually_physical_hb_identity (alpha c C : ℝ)
    (halpha : 0 < alpha) (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,∀ (d g : ℕ) (U : Fin d → ℝ), (∀ i,0 < U i) →
      ∀ R : Fin g → ℝ,(∀ j,0 < R j) → ∀ group : Fin d → Fin g,
      ∀ pair : Fin 2 → Fin g,pair 0 ≠ pair 1 → ∀ pick : Fin g → Fin d,
      (∀ j,group (pick j)=j) → ∀ T : ℝ,0 < T → ∀ m : ℕ,∀ l : Lane,∀ x : Point d,
      (∀ i,1 ≤ U i*Real.exp (x i)) →
      (∀ j,c*(N : ℝ)^alpha ≤ groupProduct group (fun i => U i*Real.exp (x i)) j) →
      (∏ i,U i*Real.exp (x i)) ≤ C*(N : ℝ) →
      hbProfile (alpha/2) (Real.log (N : ℝ))
        (fun j => groupBase U group (pair j)) (pairSlots group pair) group
        (fun j => Real.log (groupBase U group j/R j))
        (Real.log ((∏ j,groupBase U group j)/T)) (fun i => Real.log (U i))
        (fun j => Real.log (groupBase U group j)) pick m l x =
      physicalProfile (Real.log (N : ℝ)) (groupBase U group) R group pair T m l x *
        originalLogFactor group pick (fun i => U i*Real.exp (x i)) := by
  filter_upwards [eventually_log_domains alpha c C halpha hc hC] with N hN
  intro d g U hU R hR group pair hne pick hpick T hT m l x hn hg ht
  have hh := hN.2 d g group _ hn hg ht
  exact hbProfile_eq_physical (half_pos halpha) (by linarith [hN.1])
    U hU R hR group pair hne pick hT m l x hh.1 hh.2

theorem hbProfile_sum {d g : ℕ} (a ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (u : Fin d → ℝ) (v : Fin g → ℝ)
    (pick : Fin g → Fin d) (m : ℕ) (x : Point d) :
    (∑ l : Lane,hbProfile a ell R slot group b trim u v pick m l x) =
      window x*(P3LogProductTransitionJets.logStep (trim+∑ i,x i)*
        ∏ j,P3LogProductTransitionJets.logHat (b j+groupSum group x j))*
          hbFactor a ell group u v pick x := by
  simp only [hbProfile,← Finset.sum_mul,productProfile_sum]

/-- Exact finite algebra; arithmetic kernels, signs, multiplicities and
rho remain in the same sum. No new class of PP weights is licensed. -/
theorem same_rho_hb_partition {ι : Type*} {d g : ℕ}
    (Q : Finset ℕ) (S : Finset ι) (rho : ℕ → ℝ) (F : ℕ → ι → ℝ)
    (z : ι → Point d) (a ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (u : Fin d → ℝ) (v : Fin g → ℝ)
    (pick : Fin g → Fin d) (m : ℕ) :
    (∑ l : Lane,∑ q ∈ Q,rho q*∑ t ∈ S,F q t*hbProfile a ell R slot group b trim u v pick m l (z t)) =
      ∑ q ∈ Q,rho q*∑ t ∈ S,F q t*
        (window (z t)*(P3LogProductTransitionJets.logStep (trim+∑ i,z t i)*
          ∏ j,P3LogProductTransitionJets.logHat (b j+groupSum group (z t) j))*
            hbFactor a ell group u v pick (z t)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.mul_sum,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.mul_sum,hbProfile_sum]

end
end ImbalancedChen.P3U5HBLogChart
