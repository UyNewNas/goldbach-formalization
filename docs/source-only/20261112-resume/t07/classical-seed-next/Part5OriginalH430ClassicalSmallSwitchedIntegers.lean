import ImbalancedChen.Part5OriginalH430ClassicalCausalSeedScale
import ImbalancedChen.Part5OriginalH430SeedPurifiedPrimeFibres

/-! Exact partition of the actual rough tail by its complete integer product.
Both signs keep every prime label, the penultimate cutoff and the same m.
The old additive-prime test acts only after forming d times the whole word. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmallSwitchedIntegers
noncomputable section
open Finset Filter Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedSwitchedUnsiftedSource (labels)
open P2EnhancedNonunitLabelGeometry (label_prod_pos)
open P2EnhancedShortWordUnitBound (reciprocal_labels_eventually)
open P2EnhancedExactExceptionTheta (original_word_arity)
open Part5OriginalH430SeedPurifiedPrimeFibres (fibre wordFibre)
open Part5OriginalH430ClassicalCausalSeedScale (smallProduct)
open scoped Classical BigOperators Topology

def smallIntegers (N D : ℕ) (z X : ℝ) : Finset ℕ :=
  (roughNumbers ((N:ℝ)/D) z).filter (fun m => ((D*m:ℕ):ℝ)≤X)

def largeIntegers (N D : ℕ) (z X : ℝ) : Finset ℕ :=
  (roughNumbers ((N:ℝ)/D) z).filter (fun m => X<((D*m:ℕ):ℝ))

def testWeight (tested : Bool) (N D m : ℕ) : ℝ :=
  if tested then (if D*m<N ∧ (N-D*m).Prime then 1 else 0) else 1

private theorem test_bounds (tested : Bool) (N D m : ℕ) :
    0≤testWeight tested N D m ∧ testWeight tested N D m≤1 := by
  cases tested with
  | false => norm_num [testWeight]
  | true => by_cases h : D*m<N ∧ (N-D*m).Prime <;> norm_num [testWeight,h]

def smallWord (tested : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) (X : ℝ) : ℝ :=
  ∑ qs∈labels N Q d cs, ∑ m∈smallIntegers N (d*qs.prod) (qs.getD (qs.length-2) 0) X,
    testWeight tested N (d*qs.prod) m

def largeWord (tested : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) (X : ℝ) : ℝ :=
  ∑ qs∈labels N Q d cs, ∑ m∈largeIntegers N (d*qs.prod) (qs.getD (qs.length-2) 0) X,
    testWeight tested N (d*qs.prod) m

private theorem fibre_parts (tested : Bool) (N D : ℕ) (z X : ℝ) :
    fibre tested N D z =
      (∑ m∈smallIntegers N D z X,testWeight tested N D m)+
      ∑ m∈largeIntegers N D z X,testWeight tested N D m := by
  have hf : fibre tested N D z=∑ m∈roughNumbers ((N:ℝ)/D) z,testWeight tested N D m := by
    cases tested <;> rfl
  rw [hf,smallIntegers,largeIntegers,sum_filter,sum_filter,←sum_add_distrib]
  apply sum_congr rfl
  intro m _
  by_cases h : ((D*m:ℕ):ℝ)≤X
  · rw [if_pos h,if_neg (not_lt_of_ge h),add_zero]
  · rw [if_neg h,if_pos (lt_of_not_ge h),zero_add]

theorem word_parts (tested : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) (X : ℝ) :
    wordFibre tested N Q d cs=smallWord tested N Q d cs X+largeWord tested N Q d cs X := by
  unfold wordFibre smallWord largeWord
  rw [←sum_add_distrib]
  exact sum_congr rfl (fun qs _ => fibre_parts tested N _ _ X)

theorem small_nonneg (tested : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) (X : ℝ) :
    0≤smallWord tested N Q d cs X :=
  sum_nonneg (fun qs _ => sum_nonneg (fun m _ => (test_bounds tested N _ m).1))

theorem small_tested_le_raw (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) (X : ℝ) :
    smallWord true N Q d cs X≤smallWord false N Q d cs X :=
  sum_le_sum (fun qs _ => sum_le_sum (fun m _ => (test_bounds true N _ m).2))

private theorem small_integer_card {N D : ℕ} {z X : ℝ} (hD : 0<D) (hX : 0≤X) :
    ((smallIntegers N D z X).card:ℝ)≤X/D := by
  have hpos : (0:ℝ)<D := Nat.cast_pos.mpr hD
  have hs : smallIntegers N D z X ⊆ Icc 1 ⌊X/(D:ℝ)⌋₊ := by
    intro m hm
    obtain ⟨hM,hmX⟩ := mem_filter.mp hm
    refine mem_Icc.mpr ⟨(mem_roughNumbers.mp hM).1,Nat.le_floor ?_⟩
    apply (le_div_iff₀ hpos).mpr
    simpa only [Nat.cast_mul,mul_comm] using hmX
  calc
    _ ≤ ((Icc 1 ⌊X/(D:ℝ)⌋₊).card:ℝ) := Nat.cast_le.mpr (card_le_card hs)
    _ = (⌊X/(D:ℝ)⌋₊:ℝ) := by simp [Nat.card_Icc]
    _ ≤ _ := Nat.floor_le (div_nonneg hX hpos.le)

private theorem raw_word_reciprocal {N d : ℕ} (Q X : ℝ) (cs : List ℕ) (hd : 0<d) (hX : 0≤X) :
    smallWord false N Q d cs X≤(X/d)*(∑ qs∈labels N Q d cs,1/(qs.prod:ℝ)) := by
  unfold smallWord
  rw [mul_sum]
  apply sum_le_sum
  intro qs hqs
  have hprod := label_prod_pos hqs
  have h := small_integer_card (N:=N) (z:=(qs.getD (qs.length-2) 0))
    (Nat.mul_pos hd hprod) hX
  calc
    _ = ((smallIntegers N (d*qs.prod) (qs.getD (qs.length-2) 0) X).card:ℝ) := by simp [testWeight]
    _ ≤ _ := h
    _ = _ := by rw [Nat.cast_mul]; ring

def allSmall (tested : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) (X : ℝ) : ℝ :=
  ∑ j : Fin 13,((secondFunctionalMotherGammaWords (9+j.val)).map
    (fun cs => smallWord tested N Q d cs X)).sum

def allLarge (tested : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) (X : ℝ) : ℝ :=
  ∑ j : Fin 13,((secondFunctionalMotherGammaWords (9+j.val)).map
    (fun cs => largeWord tested N Q d cs X)).sum

theorem all_parts (tested : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) (X : ℝ) :
    (∑ j : Fin 13,((secondFunctionalMotherGammaWords (9+j.val)).map
      (wordFibre tested N Q d)).sum)=allSmall tested N Q d X+allLarge tested N Q d X := by
  unfold allSmall allLarge
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro j _
  simp_rw [word_parts tested N Q d _ X]
  rw [List.sum_map_add]

theorem all_small_nonneg (tested : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) (X : ℝ) :
    0≤allSmall tested N Q d X := by
  apply sum_nonneg
  intro j _
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨cs,_,rfl⟩ := List.mem_map.mp hx
    exact small_nonneg tested N Q d cs X)

theorem small_order (N : ℕ) (Q : ℝ) (d : ℕ) (X : ℝ) :
    allSmall true N Q d X≤allSmall false N Q d X :=
  sum_le_sum (fun j _ => secondFunctionalMother_list_sum_mono _ _ _
    (fun cs _ => small_tested_le_raw N Q d cs X))

/-- From the existing complete-label reciprocal bound. The threshold
precedes all 20 occurrences, Q,d,X and the actual prime test. -/
theorem all_small_integer_budget {η : ℝ} (hη : 0<η) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (Q : ℝ) (d : ℕ),0<d →
      (N:ℝ)^η≤Q/d → ∀ X : ℝ,0≤X →
        allSmall false N Q d X≤(20*5^6:ℝ)*X/d := by
  obtain ⟨R0,hrec⟩ := eventually_atTop.mp reciprocal_labels_eventually
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop R0)
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN Q d hd hscale X hX
  have hrec' := hrec (Q/d) ((hT N ((le_max_right 4 T).trans hN)).trans hscale)
  let C : ℝ := (X/d)*5^6
  have hw (j : Fin 13) (cs : List ℕ) (hc : cs∈secondFunctionalMotherGammaWords (9+j.val)) :
      smallWord false N Q d cs X≤C := by
    have hr := original_word_arity (by omega) (by omega) hc
    exact (raw_word_reciprocal Q X cs hd hX).trans (mul_le_mul_of_nonneg_left
      ((hrec' N d cs Q rfl).trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤5) hr))
      (div_nonneg hX (Nat.cast_nonneg d)))
  calc
    _ ≤ ∑ j : Fin 13,((secondFunctionalMotherGammaWords (9+j.val)).map (fun _ => C)).sum :=
      sum_le_sum (fun j _ => secondFunctionalMother_list_sum_mono _ _ _ (hw j))
    _ = _ := by rw [P2EnhancedSwitchedUnsiftedSource.all_switched_multiplicities]; dsimp [C]; ring

end
end ImbalancedChen.Part5OriginalH430ClassicalSmallSwitchedIntegers
