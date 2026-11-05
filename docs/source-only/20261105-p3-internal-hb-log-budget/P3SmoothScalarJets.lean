import ImbalancedChen.P3HBLogScalarProfiles

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
A reusable scalar interpretation of the EXISTING Expr/jet/jets/mixed.
The calculus hypotheses below are discharged for the actual four profiles
in P3U5HBLogChart. They are not a PP, energy or desired chart-norm licence.
-/
namespace ImbalancedChen.P3SmoothScalarJets
noncomputable section
open scoped Classical BigOperators Topology
open P3AffineTransitionJets

/-- Only interpretation changes; the differentiation syntax is unchanged. -/
def evalS {ι : Type*} {d : ℕ} (f : ι → ℝ → ℝ) (b : ι → ℝ)
    (a : ι → Fin d → ℝ) (s : ℝ) : Expr ι d → Point d → ℝ
  | .const c, _ => c
  | .step j n, x => iteratedDeriv n (f j) (affine b a s j x)
  | .slope j i, _ => a j i
  | .add e g, x => evalS f b a s e x+evalS f b a s g x
  | .mul e g, x => evalS f b a s e x*evalS f b a s g x

theorem evalS_hasDerivAt {ι : Type*} {d : ℕ} (e : Expr ι d)
    (f : ι → ℝ → ℝ) (hf : ∀ j,ContDiff ℝ ∞ (f j))
    (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ) (x : Point d) (i : Fin d) :
    HasDerivAt (fun t : ℝ => evalS f b a s e (shift x i t))
      (s*evalS f b a s (jet i e) x) 0 := by
  induction e with
  | const c => simpa [evalS,jet] using hasDerivAt_const (0 : ℝ) c
  | slope j k => simpa [evalS,jet] using hasDerivAt_const (0 : ℝ) (a j k)
  | step j n =>
      have hd : Differentiable ℝ (iteratedDeriv n (f j)) :=
        ContDiff.differentiable_iteratedDeriv' n ((hf j).of_le (by simp))
      have hi : HasDerivAt (fun t : ℝ => affine b a s j x+(s*a j i)*t)
          (s*a j i) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (s*a j i)).const_add
          (affine b a s j x)
      have h := (hd (affine b a s j x)).hasDerivAt.comp 0 hi
      simp only [mul_zero,add_zero] at h
      rw [← iteratedDeriv_succ] at h
      convert h using 1
      · funext t; simp only [evalS,affine_shift]
      · simp only [evalS,jet]; ring
  | add e g he hg => convert he.add hg using 1 <;> simp only [evalS,jet] <;> ring
  | mul e g he hg => convert he.mul hg using 1 <;> simp only [evalS,jet,shift_zero] <;> ring

theorem mixed_evalS {ι : Type*} {d : ℕ} (is : List (Fin d)) (e : Expr ι d)
    (f : ι → ℝ → ℝ) (hf : ∀ j,ContDiff ℝ ∞ (f j))
    (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ) :
    mixed is (evalS f b a s e) =
      fun x => s^is.length*evalS f b a s (jets is e) x := by
  induction is with
  | nil => funext x; simp [mixed,jets]
  | cons i is ih =>
      funext x
      simp only [mixed,ih,coordinateDeriv]
      rw [((evalS_hasDerivAt (jets is e) f hf b a s x i).const_mul (s^is.length)).deriv]
      simp only [jets,List.length_cons,pow_succ]
      ring

theorem continuous_evalS {ι : Type*} {d : ℕ} (e : Expr ι d)
    (f : ι → ℝ → ℝ) (hf : ∀ j,ContDiff ℝ ∞ (f j))
    (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ) : Continuous (evalS f b a s e) := by
  induction e with
  | const c => exact continuous_const
  | slope j i => exact continuous_const
  | step j n =>
      apply (ContDiff.continuous_iteratedDeriv' n ((hf j).of_le (by simp))).comp
      unfold affine
      fun_prop
  | add e g he hg => exact he.add hg
  | mul e g he hg => exact he.mul hg

theorem continuous_mixed_evalS {ι : Type*} {d : ℕ} (is : List (Fin d)) (e : Expr ι d)
    (f : ι → ℝ → ℝ) (hf : ∀ j,ContDiff ℝ ∞ (f j))
    (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ) :
    Continuous (mixed is (evalS f b a s e)) := by
  rw [mixed_evalS is e f hf]
  exact continuous_const.mul (continuous_evalS _ _ hf _ _ _)

theorem exists_evalS_bound {ι τ : Type*} {d : ℕ} (f : τ → ℝ → ℝ)
    (hb : ∀ n,∃ C : ℝ,1 ≤ C ∧ ∀ k y,|iteratedDeriv n (f k) y| ≤ C)
    (e : Expr ι d) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (kind : ι → τ) (b : ι → ℝ) (a : ι → Fin d → ℝ),
      (∀ j i,|a j i| ≤ L) → ∀ (s : ℝ) (x : Point d),|evalS (f ∘ kind) b a s e x| ≤ C := by
  induction e with
  | const c => exact ⟨|c|+1,by linarith [abs_nonneg c],by intros; dsimp [evalS]; linarith⟩
  | slope j i =>
      refine ⟨L+1,by linarith,?_⟩
      intro kind b a ha s x
      exact (ha j i).trans (by linarith)
  | step j n =>
      obtain ⟨C,hC,hc⟩ := hb n
      exact ⟨C,hC,fun kind b a ha s x => hc (kind j) _⟩
  | add e g he hg =>
      obtain ⟨C,hC,hc⟩ := he
      obtain ⟨D,hD,hd⟩ := hg
      refine ⟨C+D,by linarith,?_⟩
      intro kind b a ha s x
      exact (abs_add _ _).trans (add_le_add (hc kind b a ha s x) (hd kind b a ha s x))
  | mul e g he hg =>
      obtain ⟨C,hC,hc⟩ := he
      obtain ⟨D,hD,hd⟩ := hg
      refine ⟨C*D,by nlinarith,?_⟩
      intro kind b a ha s x
      rw [evalS,abs_mul]
      exact mul_le_mul (hc kind b a ha s x) (hd kind b a ha s x) (abs_nonneg _) (by linarith)

theorem exists_family_mixed_boundS {ι κ τ : Type*} [Fintype κ] {d : ℕ}
    (f : τ → ℝ → ℝ) (hf : ∀ k,ContDiff ℝ ∞ (f k))
    (hb : ∀ n,∃ C : ℝ,1 ≤ C ∧ ∀ k y,|iteratedDeriv n (f k) y| ≤ C)
    (E : κ → Expr ι d) (q : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (kind : ι → τ) (b : ι → ℝ) (a : ι → Fin d → ℝ),
      (∀ j i,|a j i| ≤ L) → ∀ s : ℝ,0 ≤ s → ∀ k : κ,
      ∀ v : Fin q → Fin d,∀ x : Point d,
        |mixed (List.ofFn v) (evalS (f ∘ kind) b a s (E k)) x| ≤ C*s^q := by
  have h := fun u : κ × (Fin q → Fin d) =>
    exists_evalS_bound f hb (jets (List.ofFn u.2) (E u.1)) L hL
  choose c hc hc' using h
  let C := 1+∑ u : κ × (Fin q → Fin d),c u
  have hc0 (u : κ × (Fin q → Fin d)) : 0 ≤ c u := zero_le_one.trans (hc u)
  refine ⟨C,?_,?_⟩
  · have hh := Finset.sum_nonneg (s:=Finset.univ) (fun u _ => hc0 u)
    dsimp [C]; linarith
  intro kind b a ha s hs k v x
  have hle : c (k,v) ≤ C :=
    (Finset.single_le_sum (fun u _ => hc0 u) (Finset.mem_univ (k,v))).trans (by dsimp [C]; linarith)
  rw [mixed_evalS _ _ _ (fun j => hf (kind j)),abs_mul,
    abs_of_nonneg (pow_nonneg hs _),List.length_ofFn]
  exact (mul_le_mul_of_nonneg_left (hc' (k,v) kind b a ha s x) (pow_nonneg hs q)).trans
    ((mul_le_mul_of_nonneg_left hle (pow_nonneg hs q)).trans_eq (mul_comm _ _))

/-- The previous concrete product expression is preserved exactly. -/
theorem evalS_rename_eq_evalK {ι τ : Type*} {d : ℕ} (e : Expr ι d) (rename : ι → τ)
    (f : τ → ℝ → ℝ) (b : τ → ℝ) (a : τ → Fin d → ℝ) (s : ℝ)
    (kind : ι → P3LogProductTransitionJets.Kind)
    (hf : ∀ j,f (rename j)=P3LogProductTransitionJets.scalar (kind j)) (x : Point d) :
    evalS f b a s (P3LogProductTransitionJets.rename rename e) x =
      P3LogProductTransitionJets.evalK kind (b ∘ rename) (a ∘ rename) s e x := by
  induction e with
  | const c => rfl
  | slope j i => rfl
  | step j n => simp only [P3LogProductTransitionJets.rename,evalS,hf,
      P3LogProductTransitionJets.evalK,affine,Function.comp_apply]
  | add e g he hg => simp only [P3LogProductTransitionJets.rename,evalS,
      P3LogProductTransitionJets.evalK,he,hg]
  | mul e g he hg => simp only [P3LogProductTransitionJets.rename,evalS,
      P3LogProductTransitionJets.evalK,he,hg]

end
end ImbalancedChen.P3SmoothScalarJets
