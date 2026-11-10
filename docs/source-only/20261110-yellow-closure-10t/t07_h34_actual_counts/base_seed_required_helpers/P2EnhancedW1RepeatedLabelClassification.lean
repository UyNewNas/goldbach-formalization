import ImbalancedChen.P2EnhancedW1SquareExceptionPower
import ImbalancedChen.P2EnhancedLowerFinitePhysicalGraph
import ImbalancedChen.P2EnhancedLowerPrimeChildGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

One selected original W1 action (i,j).  Its actual old integer word,
common Q, and physical parent node are aligned by their logarithmic
coordinates, so a fixed positive residual exponent gamma gives the
literal anchor cutoff y=(Q/B)^(1/W1Anchor j) >= N^(gamma/5).
The finite physical graph supplies a positive residual after any fixed
depth by its proved 101-per-step bound; no cutoff bound is inserted as
an opaque event hypothesis.

For an ordered W1 triple a<b<q in the actual old quotient, failure of
the old-mask switched quotient carrier implies the first-prime square
event from Phase8.  It is mapped into the physical Phase9 squareEvent
at the proved cutoff.  The implication is also expressed with the
original sigma(B) on each labelled receiver, without erasing the label
or changing the old E predicate.  Full summation of all graph labels
and all repeated-prime types remains a separate interface.

Source: manuscript-body.tex 790--875;
same-new-level-double-sieve-route.tex 92--105, 147--165.
-/

namespace ImbalancedChen.P2EnhancedW1RepeatedLabelClassification

noncomputable section
open Set Finset
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalNode
open P2EnhancedLowerPhysicalTransition (StepShape LocalDomain)
open P2EnhancedLowerFinitePhysicalGraph (TypedNode Program Coordinates Member realize
  realize_residual_bound)
open P2EnhancedLowerPrimeChildCarriers
open P2EnhancedLowerPrimeChildGeometry
open P2EnhancedW1R2ActualCarrierBranch (eligiblePrimes)
open P2EnhancedW1TripleActualCarrierBranch
open P2EnhancedW1SquareExceptionPower
open P2LargerSActualPositiveCounts (historyCarrier)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P5OriginalActionMassBound (W1Anchor)

private theorem old_product_pos (old : List ℕ)
    (hprime : ∀ p ∈ old, p.Prime) : 0 < old.prod := by
  revert hprime
  induction old with
  | nil => intro _; simp
  | cons p ps ih =>
      intro hprime
      have hp : p.Prime := hprime p (by simp)
      have hps : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      simpa only [List.prod_cons] using Nat.mul_pos hp.pos (ih hps)

/-- The literal old prime list has exactly its real log product. -/
private theorem old_word_log_sum (N : ℕ) (old : List ℕ)
    (hprime : ∀ p ∈ old, p.Prime) :
    (old.map (physicalPrime N)).sum =
      Real.log (old.prod : ℝ) / Real.log (N : ℝ) := by
  revert hprime
  induction old with
  | nil => intro _; simp [physicalPrime]
  | cons p ps ih =>
      intro hprime
      have hp : p.Prime := hprime p (by simp)
      have hps : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hpsR : (0 : ℝ) < ps.prod := by
        exact_mod_cast old_product_pos ps hps
      simp only [List.map_cons,List.sum_cons,List.prod_cons,Nat.cast_mul]
      rw [Real.log_mul hpR.ne' hpsR.ne', ih hps]
      dsimp [physicalPrime]
      ring

/-- Alignment is proved from the actual old word and total Q, not
assumed as a second residual-level formula. -/
theorem physical_level_eq_parent_residual {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {n : PhysicalNode}
    (hw : parentWindow N Q old chi)
    (hprime : ∀ p ∈ old, p.Prime)
    (hword : word n = old.map (physicalPrime N))
    (htotal : n.total = Real.log Q / Real.log (N : ℝ)) :
    physicalLevel N Q old = residual n := by
  have hB : (0 : ℝ) < old.prod := by
    exact_mod_cast old_product_pos old hprime
  have hQ : 0 < Q := hB.trans hw.2.2.1
  change Real.log (Q / (old.prod : ℝ)) / Real.log (N : ℝ) =
    n.total - (word n).sum
  rw [htotal,hword,old_word_log_sum N old hprime]
  rw [Real.log_div hQ.ne' hB.ne']
  ring

theorem w1_anchor_pos_le_five (j : Fin 10) :
    0 < W1Anchor j ∧ W1Anchor j ≤ 5 := by
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hj9 : (j.val : ℝ) ≤ 9 := by
    exact_mod_cast (show j.val ≤ 9 by omega)
  dsimp [W1Anchor]
  constructor <;> linarith

/-- Exact logarithmic identity at the same total Q and old B. -/
theorem w1_anchor_cutoff_eq_power {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} (hw : parentWindow N Q old chi) (j : Fin 10) :
    cutoff Q old.prod (W1Anchor j) =
      (N : ℝ)^(physicalLevel N Q old / W1Anchor j) := by
  have hlogs := parentWindow_logs hw
  have hNpos : (0 : ℝ) < N :=
    zero_lt_one.trans (by exact_mod_cast hw.1 : (1 : ℝ) < N)
  have hRpos : 0 < residualLevel Q old :=
    zero_lt_one.trans hlogs.2.1
  have hlogN : Real.log (N : ℝ) ≠ 0 := hlogs.1.ne'
  have hlogeq : Real.log (N : ℝ) * physicalLevel N Q old =
      Real.log (residualLevel Q old) := by
    unfold physicalLevel
    field_simp [hlogN] <;> ring
  have hlevel : (N : ℝ)^physicalLevel N Q old =
      residualLevel Q old := by
    rw [Real.rpow_def_of_pos hNpos,hlogeq,Real.exp_log hRpos]
  calc
    cutoff Q old.prod (W1Anchor j) =
        (residualLevel Q old)^(1/W1Anchor j) := rfl
    _ = ((N : ℝ)^physicalLevel N Q old)^(1/W1Anchor j) := by rw [hlevel]
    _ = (N : ℝ)^(physicalLevel N Q old / W1Anchor j) := by
      rw [← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1
      ring

/-- A positive physical residual in a selected W1 box gives a fixed
power cutoff for every first-window prime.  The maximum anchor is 5. -/
theorem w1_anchor_fixed_power {N : ℕ} {Q chi gamma : ℝ}
    {old : List ℕ} (hw : parentWindow N Q old chi)
    (j : Fin 10) (hgamma : 0 < gamma)
    (hlevel : gamma ≤ physicalLevel N Q old) :
    (N : ℝ)^(gamma/5) ≤ cutoff Q old.prod (W1Anchor j) := by
  have hA := w1_anchor_pos_le_five j
  have hExp : gamma/5 ≤ physicalLevel N Q old/W1Anchor j := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5) hA.1).mpr
    have hleft := mul_le_mul_of_nonneg_left hA.2 hgamma.le
    have hright := mul_le_mul_of_nonneg_left hlevel (by norm_num : (0 : ℝ) ≤ 5)
    nlinarith only [hleft,hright]
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast (le_of_lt hw.1)
  rw [w1_anchor_cutoff_eq_power hw j]
  exact Real.rpow_le_rpow_of_exponent_le hbase hExp

/-- The existing finite graph provides a concrete positive exponent
after any fixed itinerary, preserving its action/cell code. -/
theorem graph_w1_fixed_power {N mesh depth : ℕ} {Q chi gamma a b : ℝ}
    {old : List ℕ} {root : TypedNode} {code : Program mesh depth}
    {z : Coordinates depth}
    (hmember : Member a b depth root code z)
    (hroot : gamma ≤ residual root.physical) (hgamma : 0 < gamma)
    (hw : parentWindow N Q old chi)
    (hcoord : physicalLevel N Q old =
      residual (realize depth root code z).physical)
    (j : Fin 10) :
    (N : ℝ)^((gamma/(101:ℝ)^depth)/5) ≤
      cutoff Q old.prod (W1Anchor j) := by
  have hden : 0 < (101:ℝ)^depth := pow_pos (by norm_num) _
  have hlower : gamma/(101:ℝ)^depth ≤ physicalLevel N Q old := by
    rw [hcoord]
    exact (div_le_div_of_nonneg_right hroot hden.le).trans
      (realize_residual_bound hmember)
  exact w1_anchor_fixed_power hw j (div_pos hgamma hden) hlower

/-- One literal W1 (i,j) ordered triple: missing the old-mask switched
quotient carrier forces membership in the physically counted square event
at the graph-derived power cutoff.  No hEvent is supplied by the caller. -/
theorem w1_ordered_triple_oldmask_or_squareEvent
    {N ell : ℕ} {Q chi gamma : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} {E : ℕ → ℕ → Prop} {a b q : ℕ}
    (hw : parentWindow N Q old chi)
    (n : PhysicalNode) (hprime : ∀ p ∈ old, p.Prime)
    (hword : word n = old.map (physicalPrime N))
    (htotal : n.total = Real.log Q / Real.log (N : ℝ))
    (hgamma : 0 < gamma) (hres : gamma ≤ residual n)
    (hcomp : 0 < N-ell)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hq : q ∈ eligiblePrimes N ell Q old i j)
    (hab : a < b) (hbq : b < q)
    (hsecond : ∀ r ∈ eligiblePrimes N ell Q old i j,
      r ≠ a → b ≤ r) :
    ell ∈ oldMaskTripleCarrier N old.prod a b q E ∨
      ell ∈ squareEvent N old.prod E
        (cutoff Q old.prod (W1Anchor j)) ((N : ℝ)^(gamma/5)) := by
  have hB : 0 < old.prod := hw.2.1
  have hlevel : gamma ≤ physicalLevel N Q old := by
    rw [physical_level_eq_parent_residual hw hprime hword htotal]
    exact hres
  have hcut := w1_anchor_fixed_power hw j hgamma hlevel
  rcases triple_oldmask_or_first_square hB hcomp hell ha hb hq hab hbq hsecond with
    hgood | hsq
  · exact Or.inl hgood
  · exact Or.inr (phase8_exception_mem hell hcomp ha hcut hsq)

/-- The W1 action label comes from the actual finite graph program,
and the fixed cutoff comes from its preceding accepted path's residual
bound.  The integer word and total-Q align the realized physical state. -/
theorem graph_selected_w1_triple_exception
    {N mesh depth ell : ℕ} {Q chi gamma lo hi : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {a b q : ℕ}
    {root : TypedNode} {code : Program mesh depth}
    {z : Coordinates depth} {action : Program mesh 1}
    {actionZ : Coordinates 1}
    (hprev : Member lo hi depth root code z)
    (hshape : (action 0).1 = StepShape.w1Singleton i j)
    (haction : Member lo hi 1
      ⟨true,(realize depth root code z).physical⟩ action actionZ)
    (hgamma : 0 < gamma)
    (hroot : gamma ≤ residual root.physical)
    (hw : parentWindow N Q old chi)
    (hprime : ∀ p ∈ old, p.Prime)
    (hword : word (realize depth root code z).physical =
      old.map (physicalPrime N))
    (htotal : (realize depth root code z).physical.total =
      Real.log Q / Real.log (N : ℝ))
    (hcomp : 0 < N-ell)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hq : q ∈ eligiblePrimes N ell Q old i j)
    (hab : a < b) (hbq : b < q)
    (hsecond : ∀ r ∈ eligiblePrimes N ell Q old i j,
      r ≠ a → b ≤ r) :
    LocalDomain (realize depth root code z).physical
      (.w1Singleton i j) (actionZ 0) ∧
    (ell ∈ oldMaskTripleCarrier N old.prod a b q E ∨
      ell ∈ squareEvent N old.prod E
        (cutoff Q old.prod (W1Anchor j))
        ((N : ℝ)^((gamma/(101:ℝ)^depth)/5))) := by
  have hlocal : LocalDomain (realize depth root code z).physical
      (.w1Singleton i j) (actionZ 0) := by
    simpa only [hshape] using haction.2.2.1
  have hden : 0 < (101:ℝ)^depth := pow_pos (by norm_num) _
  have hres : gamma/(101:ℝ)^depth ≤
      residual (realize depth root code z).physical :=
    (div_le_div_of_nonneg_right hroot hden.le).trans
      (realize_residual_bound hprev)
  exact ⟨hlocal,
    w1_ordered_triple_oldmask_or_squareEvent hw
      (realize depth root code z).physical hprime hword htotal
      (div_pos hgamma hden) hres hcomp hell ha hb hq hab hbq hsecond⟩

/-- A noncanonical repeated selected label in a physical triple word
already forces a prime square in the old quotient.  The original ordered
source excludes such words, but this records their exact arithmetic
classification if an intermediate labelled expansion contains them. -/
theorem repeated_triple_word_squareEvent
    {N ell : ℕ} {Q chi gamma : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} {E : ℕ → ℕ → Prop} {a b q : ℕ}
    (hw : parentWindow N Q old chi)
    (n : PhysicalNode) (hprime : ∀ p ∈ old, p.Prime)
    (hword : word n = old.map (physicalPrime N))
    (htotal : n.total = Real.log Q / Real.log (N : ℝ))
    (hgamma : 0 < gamma) (hres : gamma ≤ residual n)
    (hcomp : 0 < N-ell)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hq : q ∈ eligiblePrimes N ell Q old i j)
    (hprod : a*b*q ∣ (N-ell)/old.prod)
    (hrepeat : a=b ∨ a=q ∨ b=q) :
    ell ∈ squareEvent N old.prod E
      (cutoff Q old.prod (W1Anchor j)) ((N : ℝ)^(gamma/5)) := by
  have hlevel : gamma ≤ physicalLevel N Q old := by
    rw [physical_level_eq_parent_residual hw hprime hword htotal]
    exact hres
  have hcut := w1_anchor_fixed_power hw j hgamma hlevel
  rcases hrepeat with hab | haq | hbq
  · subst b
    have hsq : a^2 ∣ (N-ell)/old.prod := by
      have hsqProd : a^2 ∣ a*a*q := by
        refine ⟨q,?_⟩
        ring
      exact hsqProd.trans hprod
    exact phase8_exception_mem hell hcomp ha hcut hsq
  · subst q
    have hsq : a^2 ∣ (N-ell)/old.prod := by
      have hsqProd : a^2 ∣ a*b*a := by
        refine ⟨b,?_⟩
        ring
      exact hsqProd.trans hprod
    exact phase8_exception_mem hell hcomp ha hcut hsq
  · subst q
    have hsq : b^2 ∣ (N-ell)/old.prod := by
      have hsqProd : b^2 ∣ a*b*b := by
        refine ⟨a,?_⟩
        ring
      exact hsqProd.trans hprod
    exact phase8_exception_mem hell hcomp hb hcut hsq

/-- The original marked sigma(B) is retained on this SAME labelled
receiver.  This is a per-label inequality; summing all q labels needs
their finite multiplicity bound. -/
theorem w1_ordered_triple_weighted_exception
    {N ell : ℕ} {Q chi gamma : ℝ} {old : List ℕ}
    {sigma : ℕ → ℝ}
    {i : Fin 7} {j : Fin 10} {E : ℕ → ℕ → Prop} {a b q : ℕ}
    (hw : parentWindow N Q old chi)
    (n : PhysicalNode) (hprime : ∀ p ∈ old, p.Prime)
    (hword : word n = old.map (physicalPrime N))
    (htotal : n.total = Real.log Q / Real.log (N : ℝ))
    (hgamma : 0 < gamma) (hres : gamma ≤ residual n)
    (hcomp : 0 < N-ell)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hq : q ∈ eligiblePrimes N ell Q old i j)
    (hab : a < b) (hbq : b < q)
    (hsecond : ∀ r ∈ eligiblePrimes N ell Q old i j,
      r ≠ a → b ≤ r) (hsigma : 0 ≤ sigma old.prod) :
    sigma old.prod * (if ell ∈ oldMaskTripleCarrier N old.prod a b q E
      then (0 : ℝ) else 1) ≤
      sigma old.prod * (if ell ∈ squareEvent N old.prod E
        (cutoff Q old.prod (W1Anchor j)) ((N : ℝ)^(gamma/5))
        then (1 : ℝ) else 0) := by
  have hclass := w1_ordered_triple_oldmask_or_squareEvent hw n hprime
    hword htotal hgamma hres hcomp hell ha hb hq hab hbq hsecond
  by_cases hgood : ell ∈ oldMaskTripleCarrier N old.prod a b q E
  · simp only [if_pos hgood,mul_zero]
    split_ifs <;> positivity
  · have hbad := hclass.resolve_left hgood
    simp [hgood,hbad]

end
end ImbalancedChen.P2EnhancedW1RepeatedLabelClassification
