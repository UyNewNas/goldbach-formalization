import ImbalancedChen.P5RealCutoffHeathBrownThree

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal ordered-factor expansion of the ORIGINAL order-three HB identity.
The Mobius occurrences remain distinct, even when values agree. Each term
has j+1 actual real-cutoff Mobius slots, j one-slots and ONE log-slot;
there are exactly 2(j+1)<=6 occurrences. Signed tuple weights and the
coefficients +3,-3,+1 are retained. No HB interval/SW conclusion is made.
-/
namespace ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
noncomputable section
open Classical
open scoped BigOperators ArithmeticFunction.zeta
open RealTruncatedMobiusSupport RealCutoffHeathBrownThree

/-- Ordered positive factor tuples, without quotienting equal entries.
The antidiagonal construction is finite at every natural target. -/
def factorTuples : ℕ → ℕ → Finset (List ℕ)
  | 0,n => if n=1 then {[]} else ∅
  | r+1,n => n.divisorsAntidiagonal.biUnion
      (fun d => (factorTuples r d.2).image (List.cons d.1))

theorem factorTuples_spec : ∀ r n : ℕ, ∀ ps ∈ factorTuples r n,
    ps.length=r ∧ ps.prod=n ∧ ∀ p∈ps, 0<p := by
  intro r
  induction r with
  | zero =>
    intro n ps hps
    by_cases hn : n=1
    · subst n
      have hp : ps=[] := by simpa [factorTuples] using hps
      subst ps
      simp
    · simp [factorTuples,hn] at hps
  | succ r ih =>
    intro n ps hps
    obtain ⟨d,hd,hps⟩ := Finset.mem_biUnion.mp hps
    obtain ⟨qs,hqs,rfl⟩ := Finset.mem_image.mp hps
    obtain ⟨hlen,hprod,hpos⟩ := ih d.2 qs hqs
    have hanti := Nat.mem_divisorsAntidiagonal.mp hd
    have hd1 : 0<d.1 := by
      apply Nat.pos_of_ne_zero
      intro hz
      apply hanti.2
      rw [← hanti.1,hz,zero_mul]
    refine ⟨by simpa using congrArg Nat.succ hlen, ?_, ?_⟩
    · simpa only [List.prod_cons,hprod] using hanti.1
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hd1
      · exact hpos p hp

private theorem factor_fibres_disjoint (r n : ℕ) :
    Set.PairwiseDisjoint (n.divisorsAntidiagonal : Set (ℕ×ℕ))
      (fun d => (factorTuples r d.2).image (List.cons d.1)) := by
  intro d hd e he hde
  apply Finset.disjoint_left.mpr
  intro ps hdp hep
  obtain ⟨xs,hxs,hx⟩ := Finset.mem_image.mp hdp
  obtain ⟨ys,hys,hy⟩ := Finset.mem_image.mp hep
  have hc : d.1::xs=e.1::ys := hx.trans hy.symm
  have hc' := List.cons.inj hc
  have hsecond : d.2=e.2 := by
    calc
      d.2 = xs.prod := (factorTuples_spec r d.2 xs hxs).2.1.symm
      _ = ys.prod := congrArg List.prod hc'.2
      _ = e.2 := (factorTuples_spec r e.2 ys hys).2.1
  exact hde (Prod.ext hc'.1 hsecond)

def tupleWeight : List (ArithmeticFunction ℝ) → List ℕ → ℝ
  | [],[] => 1
  | f::fs,n::ns => f n * tupleWeight fs ns
  | _,_ => 0

/-- Exact finite Dirichlet-product coefficient, with each ordered
occurrence present once and no positivity assumption on its value. -/
theorem list_product_coefficient (fs : List (ArithmeticFunction ℝ)) :
    ∀ n : ℕ, fs.prod n = ∑ ps ∈ factorTuples fs.length n, tupleWeight fs ps := by
  induction fs with
  | nil =>
    intro n
    by_cases hn : n=1
    · subst n; simp [factorTuples,tupleWeight]
    · simp [factorTuples,tupleWeight,ArithmeticFunction.one_apply,hn]
  | cons f fs ih =>
    intro n
    rw [List.prod_cons,ArithmeticFunction.mul_apply]
    change (∑ d ∈ n.divisorsAntidiagonal, f d.1*fs.prod d.2) =
      ∑ ps ∈ n.divisorsAntidiagonal.biUnion
        (fun d => (factorTuples fs.length d.2).image (List.cons d.1)), tupleWeight (f::fs) ps
    rw [Finset.sum_biUnion (factor_fibres_disjoint fs.length n)]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_image]
    · rw [ih,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ps hps
      rfl
    · intro xs hxs ys hys hxy
      exact (List.cons.inj hxy).2

def hbWord (y : ℝ) (j : ℕ) : List (ArithmeticFunction ℝ) :=
  List.replicate (j+1) (muTrunc y) ++
    List.replicate j (ζ : ArithmeticFunction ℝ) ++ [ArithmeticFunction.log]

theorem hbWord_length (y : ℝ) (j : ℕ) : (hbWord y j).length=2*(j+1) := by
  simp only [hbWord,List.length_append,List.length_replicate,List.length_singleton]
  omega

theorem hbWord_length_le_six (y : ℝ) {j : ℕ} (hj : j∈Finset.range 3) :
    (hbWord y j).length≤6 := by
  rw [hbWord_length]
  have := Finset.mem_range.mp hj
  omega

theorem hbWord_product (y : ℝ) (j : ℕ) : (hbWord y j).prod=term y j := by
  simp only [hbWord,List.prod_append,List.prod_replicate,List.prod_singleton,term]
  ring

private theorem mobius_prefix_cutoff (y : ℝ) (tail : List (ArithmeticFunction ℝ)) :
    ∀ k : ℕ, ∀ ps : List ℕ,
      tupleWeight (List.replicate k (muTrunc y)++tail) ps≠0 →
        ∀ p∈ps.take k, (p : ℝ)≤y := by
  intro k
  induction k with
  | zero => intro ps hn p hp; simp at hp
  | succ k ih =>
    intro ps hn
    cases ps with
    | nil => simp [List.replicate_succ,tupleWeight] at hn
    | cons a ps =>
      have hne : muTrunc y a * tupleWeight (List.replicate k (muTrunc y)++tail) ps≠0 := by
        simpa only [List.replicate_succ,List.cons_append,tupleWeight] using hn
      have hparts := mul_ne_zero_iff.mp hne
      have ha : (a : ℝ)≤y := by
        by_contra h
        exact hparts.1 (muTrunc_of_gt (lt_of_not_ge h))
      intro p hp
      have hp' : p∈a::ps.take k := by simpa using hp
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact ha
      · exact ih ps hparts.2 p hp'

/-- Every actually active Mobius occurrence obeys the SAME REAL cutoff.
No integer-floor cube or assumed factor-length certificate is introduced. -/
theorem hbWord_nonzero_mobius_cutoff (y : ℝ) (j : ℕ) (ps : List ℕ)
    (hn : tupleWeight (hbWord y j) ps≠0) :
    ∀ p∈ps.take (j+1), (p : ℝ)≤y := by
  apply mobius_prefix_cutoff y
    (List.replicate j (ζ : ArithmeticFunction ℝ)++[ArithmeticFunction.log]) (j+1) ps
  simpa only [hbWord,List.append_assoc] using hn

/-- Literal finite six-or-fewer-slot original HB source coefficient.
Repeated values do not merge occurrences; signs and the one log-slot
remain in tupleWeight. Valid at the CLOSED original REAL cube range. -/
theorem literal_order_three_identity {y : ℝ} (hy : 0≤y) {n : ℕ}
    (hn : (n : ℝ)≤y^3) :
    ArithmeticFunction.vonMangoldt n =
      ∑ j ∈ Finset.range 3, (-1 : ℝ)^j*(Nat.choose 3 (j+1) : ℝ)*
        ∑ ps ∈ factorTuples (2*(j+1)) n, tupleWeight (hbWord y j) ps := by
  rw [order_three_identity hy hn]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  rw [← hbWord_product y j,list_product_coefficient,hbWord_length]

end
end ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
