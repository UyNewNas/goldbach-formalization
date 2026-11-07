import ImbalancedChen.P5ZU1011OriginalW16NativeInitialization
import ImbalancedChen.ActualDwellSelectedRemainder

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The original four actual W16 primes are attached to the ORIGINAL residual
well vector at its constructed residual level. Full specified squares
are paid from the actual W interior and its64delta source surplus.
Every later square retains the same full-prefix product, and the original
20delta residual-level loss pays the complete D-well vector.

The residual input is its primitive actualDwellSupport at R; it is not a
factorization, global density or final-prefix support premise. Producing
the genuine modified residual sieve atoms with that support remains an
explicit separate task. No rough-slot order, multiplicity or prime label
is changed by attachment. The native first-overflow stopping square is
then derived from the actual run trace, not supplied by a caller.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16AttachedWellSupport
noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank U1011OriginalSixteenArithmeticProducts
open U1011OriginalSixteenInteriorArithmetic U1011OriginalW16NativeInitialization
open P5U1011JointOverlap
open Part3.ActualWThreeCapacityRun
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation
open scoped BigOperators

def specified (t : Four) : List ℕ := [slots t 0,slots t 1,slots t 2,slots t 3]

theorem specified_product (t : Four) : (specified t).prod=fullPrefix t := by
  simp [specified,fullPrefix,Fin.prod_univ_succ]

/-- Primitive residual square support is attached by the exact prefix
product. This proves every indexed full-vector square, including repeated
residual occurrences, by the pinned append-singleton support identity. -/
private theorem attach_square_support (front tail : List ℕ) {D R : ℝ}
    (hf : actualDwellSupport D front) (ht : actualDwellSupport R tail)
    (hbudget : (front.prod:ℝ)*R≤D) : actualDwellSupport D (front++tail) := by
  revert ht
  induction tail using List.reverseRecOn with
  | nil => intro ht; simpa using hf
  | append_singleton tail q ih =>
    intro ht
    obtain ⟨htail,hlast⟩ :=
      (prefixSquareBound_append_singleton_iff (fun n : ℕ => (n:ℝ)) R tail q).1 ht
    rw [←List.append_assoc]
    apply (prefixSquareBound_append_singleton_iff (fun n : ℕ => (n:ℝ)) D (front++tail) q).2
    refine ⟨ih htail,?_⟩
    have hmul := mul_le_mul_of_nonneg_left hlast (Nat.cast_nonneg front.prod : (0:ℝ)≤front.prod)
    calc
      _ = (front.prod:ℝ)*((tail.map (fun n : ℕ => (n:ℝ))).prod*(q:ℝ)^2) := by
        rw [List.map_append,List.prod_append,actualNatList_cast_prod]
        ring
      _ ≤ (front.prod:ℝ)*R := hmul
      _ ≤ D := hbudget

theorem native_specified_squares {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (he : TypedEligible wPolicy (coordinates N t)) :
    ∀ j : Fin 4, (prefixProduct j t:ℝ)*(slots t j:ℝ)^2<
      (N:ℝ)^(theta (coordinates N t)-2*buffer (coordinates N t)) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hb := buffer_bounds (coordinates N t) he
  have hp : ∀ i : Fin 4, (slots t i:ℝ)≤(N:ℝ)^coordinates N t i := fun i =>
    (actualPrimeTupleLog_rpow hN (slots t) (slots_pos ht) i).symm.le
  intro j
  have hg := fullSquare_le_gate (coordinates N t) j
  have hs : fullSquare j (coordinates N t)<
      theta (coordinates N t)-2*buffer (coordinates N t) := by linarith [hb.1,hb.2.2.1]
  rw [fullSquare_eq_generic] at hs
  simpa only [prefixProduct,prefixIndices,Fin.lt_def] using
    prefixSquareExpr_actual_gate (N:ℝ) hn (slots t) (coordinates N t) hp j hs

theorem native_specified_well_support {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (he : TypedEligible wPolicy (coordinates N t)) :
    actualDwellSupport ((N:ℝ)^(theta (coordinates N t)-2*buffer (coordinates N t))) (specified t) := by
  have hs := native_specified_squares hN ht he
  intro i hi
  have hi4 : i<4 := by simpa only [specified,List.length_cons,List.length_nil] using hi
  interval_cases i
  · simpa [specified,prefixProduct,prefixIndices,Finset.prod_filter,Fin.prod_univ_succ] using (hs 0).le
  · simpa [specified,prefixProduct,prefixIndices,Finset.prod_filter,Fin.prod_univ_succ] using (hs 1).le
  · simpa [specified,prefixProduct,prefixIndices,Finset.prod_filter,Fin.prod_univ_succ] using (hs 2).le
  · simpa [specified,prefixProduct,prefixIndices,Finset.prod_filter,Fin.prod_univ_succ] using (hs 3).le

/-- The full ACTUAL integer prefix is multiplied by the original residual
level exactly once. The surviving20delta is stronger than the2delta
level required by the original W capacity run. -/
theorem native_product_level_budget {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (he : TypedEligible wPolicy (coordinates N t)) :
    ((specified t).prod:ℝ)*(N:ℝ)^residualExponent (coordinates N t) =
      (N:ℝ)^(theta (coordinates N t)-20*buffer (coordinates N t)) ∧
    ((specified t).prod:ℝ)*(N:ℝ)^residualExponent (coordinates N t) ≤
      (N:ℝ)^(theta (coordinates N t)-2*buffer (coordinates N t)) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := zero_lt_one.trans hn
  have heq : ((specified t).prod:ℝ)*(N:ℝ)^residualExponent (coordinates N t) =
      (N:ℝ)^(theta (coordinates N t)-20*buffer (coordinates N t)) := by
    rw [specified_product,←fullPrefix_rpow hN ht,←Real.rpow_add hp]
    congr 1
    dsimp [residualExponent]
    ring
  refine ⟨heq,?_⟩
  rw [heq]
  exact Real.rpow_le_rpow_of_exponent_le hn.le (by linarith [(buffer_bounds _ he).1])

/-- Complete original-prefix D-well support is supplied from residual
support at R and the TRUE specified W squares. It is not an input. -/
theorem native_attached_well_support {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (he : TypedEligible wPolicy (coordinates N t))
    (tail : List ℕ)
    (hresidual : actualDwellSupport ((N:ℝ)^residualExponent (coordinates N t)) tail) :
    actualDwellSupport ((N:ℝ)^(theta (coordinates N t)-2*buffer (coordinates N t)))
      (specified t++tail) :=
  attach_square_support (specified t) tail (native_specified_well_support hN ht he)
    hresidual (native_product_level_budget hN ht he).2

/-- A genuine stopping square of the ORIGINAL native four-prime W run.
The exact unread suffix and first-overflow trace come from the run itself;
the stopping-square premise of a later repair is discharged here. -/
theorem native_first_overflow_square {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (he : TypedEligible wPolicy (coordinates N t))
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ)
    (hresidual : actualDwellSupport ((N:ℝ)^residualExponent (coordinates N t)) tail)
    (g : Bins ℕ) (q : ℕ) (rest : List ℕ)
    (hstop : run (fun n : ℕ => (n:ℝ)) A ((N:ℝ)^(2*theta (coordinates N t)-1))
      ((N:ℝ)^(1-theta (coordinates N t)-2*buffer (coordinates N t))/A)
      (initialBins A (firstThree t)) (slots t 2 :: slots t 3 :: tail)=.overflow g q rest) :
    (∃ prefix, slots t 2 :: slots t 3 :: tail=prefix++q::rest ∧
      Trace (initialBins A (firstThree t)) prefix g) ∧
      Bounded (fun n : ℕ => (n:ℝ)) A ((N:ℝ)^(2*theta (coordinates N t)-1))
        ((N:ℝ)^(1-theta (coordinates N t)-2*buffer (coordinates N t))/A) g ∧
      A<wp (fun n : ℕ => (n:ℝ)) g.left*q ∧
      (N:ℝ)^(2*theta (coordinates N t)-1)<wp (fun n : ℕ => (n:ℝ)) g.middle*q ∧
      (N:ℝ)^(1-theta (coordinates N t)-2*buffer (coordinates N t))/A<
        wp (fun n : ℕ => (n:ℝ)) g.right*q ∧
      total (fun n : ℕ => (n:ℝ)) g*(q:ℝ)^2≤
        (N:ℝ)^(theta (coordinates N t)-2*buffer (coordinates N t)) := by
  obtain ⟨hB,hC,hcapacity,hseed,hrun⟩ := actual_W_first_two_and_run hN ht he A hA hAupper tail
  rw [hstop] at hrun
  obtain ⟨prefix,hinput,hbounded,htrace,hleft,hmiddle,hright⟩ := hrun
  have hfull := native_attached_well_support hN ht he tail hresidual
  have hs : total (fun n : ℕ => (n:ℝ)) (initialBins A (firstThree t)) =
      wp (fun n : ℕ => (n:ℝ)) [slots t 0,slots t 1] := by simpa [wp] using hseed
  have hfull' : PrefixSquareBound (fun n : ℕ => (n:ℝ))
      ((N:ℝ)^(theta (coordinates N t)-2*buffer (coordinates N t)))
      ([slots t 0,slots t 1]++(slots t 2 :: slots t 3 :: tail)) := by
    simpa [specified] using hfull
  exact ⟨⟨prefix,hinput,htrace⟩,hbounded,hleft,hmiddle,hright,
    stopping_square _ hs hfull' hinput htrace⟩

end
end ImbalancedChen.P5Z.U1011OriginalW16AttachedWellSupport
