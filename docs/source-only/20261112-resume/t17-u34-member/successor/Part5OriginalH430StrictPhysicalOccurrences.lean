import ImbalancedChen.Part5OriginalH430EnhancedPhysicalGrid

/-! Every actual integer letter is coprime to N. A complete or
selected-remaining prefix square cannot land on a rational frozen level:
after clearing the denominator its last prime would divide N. -/
namespace ImbalancedChen.Part5OriginalH430StrictPhysicalOccurrences
noncomputable section
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RootSourceDictionary Part5OriginalH430StrictSeedCeiling
open Part5OriginalH430EnhancedPhysicalGrid Part5OriginalH430ActualMemberStrictCover

private def Letter (N : ℕ) (t : ℝ) : Prop :=
  ∃ q : ℕ, q.Prime ∧ q.Coprime N ∧ (N:ℝ)^t = (q:ℝ)

private theorem slot_subwords (N : ℕ) (xs : List Slot)
    (hx : ∀ t ∈ xs.map Slot.exponent, Letter N t) :
    (∀ t ∈ selectedWord xs, Letter N t) ∧ (∀ t ∈ remainingWord xs, Letter N t) := by
  induction xs with
  | nil => simp [selectedWord,remainingWord]
  | cons x xs ih =>
    have h := ih (fun t ht => hx t (List.mem_cons_of_mem _ ht))
    have h0 := hx x.exponent (List.mem_cons_self ..)
    cases he : x.selected <;>
      simp only [selectedWord,remainingWord,he,Bool.false_eq_true,if_true,if_false,
        List.mem_cons] <;> aesop

private theorem sum_integer {N : ℕ} (hN : 1<N) (xs : List ℝ)
    (hx : ∀ t∈xs, Letter N t) : ∃ D : ℕ, (N:ℝ)^xs.sum = (D:ℝ) := by
  induction xs with
  | nil => exact ⟨1,by simp⟩
  | cons x xs ih =>
    obtain ⟨q,_,_,hq⟩ := hx x (List.mem_cons_self ..)
    obtain ⟨d,hd⟩ := ih (fun t ht => hx t (List.mem_cons_of_mem _ ht))
    have hpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    exact ⟨q*d,by rw [List.sum_cons,Real.rpow_add hpos,hq,hd,Nat.cast_mul]⟩

private theorem strict_at_grid {N n p : ℕ} {k : Root} {τ L T : ℝ} (hN : 1<N)
    (hL : (N:ℝ)^L=rootQ N n k τ p) (xs : List ℝ)
    (hx : ∀ t∈xs, Letter N t) (hT : ∃ b : ℕ, (N:ℝ)^T=(b:ℝ))
    (hs : SquareGates L T xs) : strictSquares L T xs := by
  induction xs generalizing T with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨q,hq,hc,hxq⟩ := hx x (List.mem_cons_self ..)
    obtain ⟨b,hb⟩ := hT
    have hpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    have hqpow : (N:ℝ)^(T+x)=(b*q:ℕ) := by rw [Real.rpow_add hpos,hb,hxq,Nat.cast_mul]
    refine ⟨lt_of_le_of_ne hs.1 ?_,ih (T:=T+x) (fun t ht => hx t (List.mem_cons_of_mem _ ht))
      ⟨b*q,hqpow⟩ hs.2⟩
    intro he
    have hprod : (N:ℝ)^(T+2*x)=(b*q*q:ℕ) := by
      rw [show T+2*x=(T+x)+x by ring,Real.rpow_add hpos,hqpow,hxq]
      push_cast <;> rfl
    have hne := root_power_ne_coprime_multiple (p:=p) n 1 k τ hq hc (dvd_mul_left q (b*q))
    rw [pow_one] at hne
    rw [he,hL] at hprod
    exact hne hprod

/-- Strict at the physical Q itself, also on the second list starting at
the entire selected product. No uniform separation over primes is claimed. -/
theorem enhanced_history_strict_physical {N n p : ℕ} {k : Root} {τ : ℝ} {o : Occurrence N}
    (hn : 111≤n) (hN : 2≤N) (hτ : 0≤τ) (hτ' : τ≤1/12) (hp : p∈originalBand N k)
    (he : rootSource k (physicalPrime N p)=.enhanced) (ho : o∈rootHistory N n k τ p) :
    let v := o.current.node.physical
    strictSquares v.total 0 (word v) ∧
      strictSquares v.total (selectedWord v.slots).sum (remainingWord v.slots) := by
  let v := o.current.node.physical
  have h1 : 1<N := by omega
  have hh := rootHistory_coherent h1 hτ hτ' (precision_error hn) (original_band_prime hp)
    (original_band_geometry hN hp) ho
  have hx : ∀ t∈word v, Letter N t := by
    intro t ht
    rw [show word v=o.current.old.map (physicalPrime N) from hh.word_eq] at ht
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ht
    obtain ⟨hpr,hc⟩ := hh.letters q hq
    exact ⟨q,hpr,hc,actualPrimeTupleLog_rpow h1 (fun _ : Fin 1 => q) (fun _ => hpr.pos) 0⟩
  have hg := enhanced_history_physical_gates hn hN hτ hτ' hp he ho
  have hsel := slot_subwords N v.slots hx
  exact ⟨strict_at_grid h1 (rootHistory_sameQ ho) (word v) hx ⟨1,by simp⟩ hg.1,
    strict_at_grid h1 (rootHistory_sameQ ho) _ hsel.2 (sum_integer h1 _ hsel.1) hg.2⟩

end
end ImbalancedChen.Part5OriginalH430StrictPhysicalOccurrences
