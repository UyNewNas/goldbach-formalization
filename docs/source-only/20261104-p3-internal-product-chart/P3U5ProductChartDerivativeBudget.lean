import ImbalancedChen.P3LogProductTransitionJets
import ImbalancedChen.P3U5ChartMixedL1Budget

/-!
Manuscript-internal / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
The PREVIOUS atlas multiplier times ALL original-group smooth dyadic hats
and ONE complete-product trim, on individual logarithmic coordinates.
The group and complete scales are offsets, not derivative constants.
No residual quotient or sharp coupled group-product gate is inserted.
-/
namespace ImbalancedChen.P3U5ProductChartDerivativeBudget
noncomputable section
open scoped Classical BigOperators Topology
open P3AffineTransitionJets P3LogProductTransitionJets
open P3U5RootAtlas P3U5LogChartDerivativeBudget

/-- Every individual variable has exactly one original-group label. -/
def groupSum {d g : ℕ} (group : Fin d → Fin g) (x : Point d) (j : Fin g) : ℝ :=
  ∑ i,if group i=j then x i else 0

abbrev ProductAtom (d g : ℕ) := Sum (Atom d) (Sum (Fin g × Bool) Unit)

def productKind {d g : ℕ} : ProductAtom d g → Kind
  | .inl _ => .transition
  | .inr _ => .product

def productOffsets {d g : ℕ} (ell : ℝ) (R : Fin 2 → ℝ) (m : ℕ)
    (b : Fin g → ℝ) (trim : ℝ) : ProductAtom d g → ℝ
  | .inl j => offsets ell R m j
  | .inr (.inl (j,false)) => b j+Real.log 2
  | .inr (.inl (j,true)) => b j
  | .inr (.inr _) => trim

def productSlopes {d g : ℕ} (ell : ℝ) (slot : Fin d → Option (Fin 2)) (m : ℕ)
    (group : Fin d → Fin g) : ProductAtom d g → Fin d → ℝ
  | .inl j,i => slopes ell slot m j i
  | .inr (.inl (j,_)),i => if group i=j then (m+1 : ℝ)⁻¹ else 0
  | .inr (.inr _),_ => (m+1 : ℝ)⁻¹

def hatsExpr (d g : ℕ) : Expr (ProductAtom d g) d :=
  exprProduct (List.ofFn (fun j : Fin g =>
    Expr.add (.step (.inr (.inl (j,false))) 0)
      (.mul (.const (-1)) (.step (.inr (.inl (j,true))) 0))))

def productExpr (d g : ℕ) (l : Lane) : Expr (ProductAtom d g) d :=
  .mul (rename Sum.inl (profileExpr d l))
    (.mul (.step (.inr (.inr ())) 0) (hatsExpr d g))

/-- b_j=log(original group product scale/original dyadic prime scale),
trim=log(complete product scale/original smooth cutoff). Exact physical
specializations are proved in the next module, not assumed in this definition. -/
def productProfile {d g : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (m : ℕ) (l : Lane) (x : Point d) : ℝ :=
  profile ell R slot m l x *
    (logStep (trim+∑ i,x i) * ∏ j,logHat (b j+groupSum group x j))

theorem product_hat_argument {d g : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (m : ℕ) (j : Fin g) (which : Bool) (x : Point d) :
    affine (productOffsets ell R m b trim) (productSlopes ell slot m group)
      (m+1 : ℝ) (.inr (.inl (j,which))) x =
        b j+groupSum group x j+(if which then 0 else Real.log 2) := by
  have hm : (m+1 : ℝ) ≠ 0 := by positivity
  have hsum : (∑ i,(if group i=j then (m+1 : ℝ)⁻¹ else 0)*x i) =
      (m+1 : ℝ)⁻¹*groupSum group x j := by
    simp only [groupSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  cases which <;> simp only [affine,productOffsets,productSlopes,hsum,
    Bool.false_eq_true,if_false,if_true] <;> field_simp [hm] <;> ring

theorem product_trim_argument {d g : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (m : ℕ) (x : Point d) :
    affine (productOffsets ell R m b trim) (productSlopes ell slot m group)
      (m+1 : ℝ) (.inr (.inr ())) x = trim+∑ i,x i := by
  have hm : (m+1 : ℝ) ≠ 0 := by positivity
  simp only [affine,productOffsets,productSlopes,← Finset.mul_sum]
  field_simp [hm]

private theorem evalK_exprProduct {ι : Type*} {d : ℕ} (es : List (Expr ι d))
    (kind : ι → Kind) (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ) (x : Point d) :
    evalK kind b a s (exprProduct es) x = (es.map (fun e => evalK kind b a s e x)).prod := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [exprProduct,evalK,List.map_cons,List.prod_cons,ih]

theorem eval_productExpr {d g : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (m : ℕ) (l : Lane) :
    evalK productKind (productOffsets ell R m b trim) (productSlopes ell slot m group)
      (m+1 : ℝ) (productExpr d g l) = productProfile ell R slot group b trim m l := by
  funext x
  have hold :
      evalK productKind (productOffsets ell R m b trim) (productSlopes ell slot m group)
        (m+1 : ℝ) (rename Sum.inl (profileExpr d l)) x = profile ell R slot m l x := by
    rw [evalK_rename_transition _ _ _ _ _ _ (fun _ => rfl)]
    exact congrFun (eval_profileExpr ell R slot m l) x
  have hh :
      evalK productKind (productOffsets ell R m b trim) (productSlopes ell slot m group)
        (m+1 : ℝ) (hatsExpr d g) x = ∏ j,logHat (b j+groupSum group x j) := by
    rw [hatsExpr,evalK_exprProduct,List.map_ofFn,List.prod_ofFn]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [evalK,iteratedDeriv_zero,productKind,scalar,product_hat_argument,
      Bool.false_eq_true,if_false,if_true,add_zero,logHat]
    ring
  rw [productExpr,evalK,hold,evalK,hh]
  simp only [evalK,iteratedDeriv_zero,productKind,scalar,product_trim_argument,productProfile]

theorem productSlopes_bound {d g : ℕ} {ell : ℝ} (hell : 1 ≤ ell)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g) (m : ℕ)
    (j : ProductAtom d g) (i : Fin d) :
    |productSlopes ell slot m group j i| ≤ 2 := by
  have hm : (1 : ℝ) ≤ m+1 := by linarith [Nat.cast_nonneg m]
  have hinv : |(m+1 : ℝ)⁻¹| ≤ 2 := by
    rw [abs_inv,abs_of_pos (by positivity : (0 : ℝ)<m+1),inv_eq_one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<m+1)).mpr
    linarith
  cases j with
  | inl j => exact slopes_bound hell slot m j i
  | inr j =>
      cases j with
      | inl jb =>
          dsimp [productSlopes]
          split_ifs
          · exact hinv
          · norm_num
      | inr u => exact hinv

/-- Constants precede ALL group scales, partition assignments, complete
cutoffs, target scales, smoothing stages and evaluation points. The number
of original groups is fixed; it changes C, not the exponent q. -/
theorem exists_productProfile_mixed_bound (d g q : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ ell : ℝ,1 ≤ ell → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ group : Fin d → Fin g,
      ∀ b : Fin g → ℝ,∀ trim : ℝ,∀ m : ℕ,∀ l : Lane,
      ∀ v : Fin q → Fin d,∀ x : Point d,
        |mixed (List.ofFn v) (productProfile ell R slot group b trim m l) x| ≤
          C*(m+1 : ℝ)^q := by
  obtain ⟨C,hC,hb⟩ := exists_family_mixed_boundK (productExpr d g) q 2 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro ell hell R slot group b trim m l v x
  rw [← eval_productExpr]
  exact hb productKind (productOffsets ell R m b trim) (productSlopes ell slot m group)
    (productSlopes_bound hell slot group m) (m+1) (by positivity) l v x

theorem continuous_mixed_productProfile {d g : ℕ} (is : List (Fin d)) (ell : ℝ)
    (R : Fin 2 → ℝ) (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (m : ℕ) (l : Lane) :
    Continuous (mixed is (productProfile ell R slot group b trim m l)) := by
  rw [← eval_productExpr]
  exact continuous_mixed_evalK _ _ _ _ _ _

/-- The physical trim and group hats are not lost in the lane summation. -/
theorem productProfile_sum {d g : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (m : ℕ) (x : Point d) :
    (∑ l : Lane,productProfile ell R slot group b trim m l x) =
      window x * (logStep (trim+∑ i,x i) * ∏ j,logHat (b j+groupSum group x j)) := by
  simp only [productProfile,← Finset.sum_mul,profile_sum]

theorem productProfile_zero_outside {d g : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (m : ℕ) (l : Lane) {x : Point d}
    (hx : x ∉ P3U5ChartMixedL1Budget.cube d) :
    productProfile ell R slot group b trim m l x=0 := by
  rw [productProfile,P3U5ChartMixedL1Budget.profile_zero_outside ell R slot m l hx,zero_mul]

end
end ImbalancedChen.P3U5ProductChartDerivativeBudget
