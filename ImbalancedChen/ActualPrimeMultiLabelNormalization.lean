import ImbalancedChen.ActualPrimeSlotSquarefreeSymmetry

/-!
# The literal Mobius sum on finitely many repeated-label blocks

Each block is the full original Cartesian power of its own prime set.
The finite product-vector sum below retains every block product separately.
The original full-product Mobius function removes every nonsquarefree
block before its repeated-label factorial is cancelled.

Prime supports of different labels may overlap in this finite identity.
Different block-product vectors with the same full product are therefore
still counted separately. Identifying those vectors with the original
ordered fine-label selector requires its disjoint-label dictionary.
No factorial discards an equal-prime diagonal or an arithmetic wall.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

def actualPrimeLabelBlocksWord {ι : Type*} (blocks : List (ι × ℕ)) : List ι :=
  blocks.flatMap (fun b => List.replicate b.2 b.1)

def actualPrimeLabelBlocksFactorial {ι : Type*} (blocks : List (ι × ℕ)) : ℕ :=
  (blocks.map (fun b => b.2.factorial)).prod

/-- This is a finite sum over complete block-product fibres. It is not
a quotient by the full product. -/
def actualPrimeLabelBlockProductSum {ι : Type*} (B : ι → Finset ℕ) :
    List (ι × ℕ) → (ℕ → ℝ) → ℝ
  | [], H => H 1
  | (i, m) :: blocks, H =>
      ∑ n ∈ (actualPrimeSlotBox B (List.replicate m i)).image List.prod,
        actualPrimeLabelBlockProductSum B blocks (fun r => H (n * r))

theorem actualPrimeSlotBox_replicate_label_eq {ι : Type*} (B : ι → Finset ℕ)
    (i : ι) (m : ℕ) :
    actualPrimeSlotBox B (List.replicate m i) =
      actualPrimeSlotBox (fun _ : Unit => B i) (List.replicate m ()) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [List.replicate_succ, actualPrimeSlotBox, ih]

theorem actualPrimeSlotBox_replicate_squarefree_coefficient {ι : Type*}
    (B : ι → Finset ℕ) (i : ι) (m n : ℕ)
    (hprime : ∀ q ∈ B i, Nat.Prime q)
    (hn : n ∈ (actualPrimeSlotBox B (List.replicate m i)).image List.prod)
    (hsquarefree : Squarefree n) :
    actualPrimeTupleCoefficient (actualPrimeSlotBox B (List.replicate m i)) n =
      m.factorial := by
  obtain ⟨ps, hps, rfl⟩ := Finset.mem_image.mp hn
  have hps' : ps ∈ actualPrimeSlotBox (fun _ : Unit => B i) (List.replicate m ()) :=
    (actualPrimeSlotBox_replicate_label_eq B i m) ▸ hps
  obtain ⟨hlen, hmem⟩ := (mem_actualPrimeSlotBox_replicate (B i) m ps).mp hps'
  have hnodup := actualPrimeVector_nodup_of_squarefree ps
    (fun q hq => hprime q (hmem q hq)) hsquarefree
  have hcoef := actualPrimeSlotBox_replicate_coefficient (B i) ps hprime hmem hnodup
  rw [hlen] at hcoef
  simpa only [actualPrimeSlotBox_replicate_label_eq B i m] using hcoef

/-- A nonsquarefree block remains a zero Mobius summand after multiplying
by any other original block products. -/
theorem actualPrimeVector_moebius_mul_eq_zero {n r : ℕ}
    (hn : ¬Squarefree n) : ArithmeticFunction.moebius (r * n) = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro h
  exact hn (Squarefree.squarefree_of_dvd (dvd_mul_left n r) h)

theorem actualPrimeSlotBox_replicate_moebius_sum {ι : Type*}
    (B : ι → Finset ℕ) (i : ι) (m r : ℕ) (H : ℕ → ℝ)
    (hprime : ∀ q ∈ B i, Nat.Prime q) :
    (∑ ps ∈ actualPrimeSlotBox B (List.replicate m i),
      (ArithmeticFunction.moebius (r * ps.prod) : ℝ) * H ps.prod) =
      (m.factorial : ℝ) *
        ∑ n ∈ (actualPrimeSlotBox B (List.replicate m i)).image List.prod,
          (ArithmeticFunction.moebius (r * n) : ℝ) * H n := by
  rw [actualPrimeTuple_sum_by_product, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hsquarefree : Squarefree n
  · rw [actualPrimeSlotBox_replicate_squarefree_coefficient B i m n hprime hn hsquarefree]
  · rw [actualPrimeVector_moebius_mul_eq_zero hsquarefree]
    simp

theorem actualPrimeLabelBlocksFactorial_pos {ι : Type*} (blocks : List (ι × ℕ)) :
    0 < actualPrimeLabelBlocksFactorial blocks := by
  induction blocks with
  | nil => exact Nat.zero_lt_one
  | cons b blocks ih =>
      change 0 < b.2.factorial * actualPrimeLabelBlocksFactorial blocks
      exact Nat.mul_pos (Nat.factorial_pos _) ih

theorem actualPrimeLabelBlockProductSum_const_mul {ι : Type*}
    (B : ι → Finset ℕ) (blocks : List (ι × ℕ)) (c : ℝ) (H : ℕ → ℝ) :
    actualPrimeLabelBlockProductSum B blocks (fun n => c * H n) =
      c * actualPrimeLabelBlockProductSum B blocks H := by
  induction blocks generalizing H with
  | nil => rfl
  | cons b blocks ih =>
      rcases b with ⟨i, m⟩
      simp only [actualPrimeLabelBlockProductSum]
      simp_rw [ih]
      rw [Finset.mul_sum]

theorem actualPrimeLabelBlockProductSum_finsetSum {ι α : Type*}
    (B : ι → Finset ℕ) (blocks : List (ι × ℕ)) (S : Finset α) (F : α → ℕ → ℝ) :
    (∑ a ∈ S, actualPrimeLabelBlockProductSum B blocks (F a)) =
      actualPrimeLabelBlockProductSum B blocks (fun n => ∑ a ∈ S, F a n) := by
  induction blocks generalizing F with
  | nil => rfl
  | cons b blocks ih =>
      rcases b with ⟨i, m⟩
      simp only [actualPrimeLabelBlockProductSum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n _
      exact ih (fun a r => F a (n * r))

/-- Every original repeated-label factorial appears once. The full-product
Mobius sign, the signed product test and every block-product fibre remain
literal. No disjointness of different label supports is needed. -/
theorem actualPrimeLabelBlocks_moebius_sum {ι : Type*} (B : ι → Finset ℕ) :
    ∀ (blocks : List (ι × ℕ)) (r : ℕ) (H : ℕ → ℝ),
      (∀ b ∈ blocks, ∀ q ∈ B b.1, Nat.Prime q) →
      (∑ ps ∈ actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks),
        (ArithmeticFunction.moebius (r * ps.prod) : ℝ) * H ps.prod) =
        (actualPrimeLabelBlocksFactorial blocks : ℝ) *
          actualPrimeLabelBlockProductSum B blocks
            (fun n => (ArithmeticFunction.moebius (r * n) : ℝ) * H n) := by
  intro blocks
  induction blocks with
  | nil =>
      intro r H _hprime
      simp [actualPrimeLabelBlocksWord, actualPrimeLabelBlocksFactorial,
        actualPrimeLabelBlockProductSum, actualPrimeSlotBox]
  | cons b blocks ih =>
      rcases b with ⟨i, m⟩
      intro r H hprime
      have hhead : ∀ q ∈ B i, Nat.Prime q := hprime (i, m) (by simp)
      have htail : ∀ b ∈ blocks, ∀ q ∈ B b.1, Nat.Prime q :=
        fun b hb => hprime b (List.mem_cons_of_mem (i, m) hb)
      let T := actualPrimeSlotBox B (List.replicate m i)
      let f := fun a n : ℕ => (ArithmeticFunction.moebius (r * (a * n)) : ℝ) * H (a * n)
      have hhead_sum (n : ℕ) :
          (∑ ps ∈ T, f ps.prod n) =
            (m.factorial : ℝ) * ∑ a ∈ T.image List.prod, f a n := by
        simpa only [T, f, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          actualPrimeSlotBox_replicate_moebius_sum B i m (r * n) (fun a => H (a * n)) hhead
      change (∑ ps ∈ actualPrimeSlotBox B
          (List.replicate m i ++ actualPrimeLabelBlocksWord blocks),
        (ArithmeticFunction.moebius (r * ps.prod) : ℝ) * H ps.prod) =
        ((m.factorial * actualPrimeLabelBlocksFactorial blocks : ℕ) : ℝ) *
          ∑ a ∈ T.image List.prod, actualPrimeLabelBlockProductSum B blocks (fun n => f a n)
      calc
        _ = ∑ ps ∈ T, ∑ qs ∈ actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks),
            f ps.prod qs.prod := by
          exact actualPrimeSlotBox_product_sum_append B _ _
            (fun n => (ArithmeticFunction.moebius (r * n) : ℝ) * H n)
        _ = ∑ ps ∈ T, (actualPrimeLabelBlocksFactorial blocks : ℝ) *
            actualPrimeLabelBlockProductSum B blocks (fun n => f ps.prod n) := by
          apply Finset.sum_congr rfl
          intro ps _
          simpa only [f, Nat.mul_assoc] using
            ih (r * ps.prod) (fun n => H (ps.prod * n)) htail
        _ = (actualPrimeLabelBlocksFactorial blocks : ℝ) *
            (∑ ps ∈ T, actualPrimeLabelBlockProductSum B blocks (fun n => f ps.prod n)) := by
          rw [Finset.mul_sum]
        _ = (actualPrimeLabelBlocksFactorial blocks : ℝ) *
            actualPrimeLabelBlockProductSum B blocks (fun n => ∑ ps ∈ T, f ps.prod n) := by
          rw [actualPrimeLabelBlockProductSum_finsetSum]
        _ = (actualPrimeLabelBlocksFactorial blocks : ℝ) *
            actualPrimeLabelBlockProductSum B blocks
              (fun n => (m.factorial : ℝ) * ∑ a ∈ T.image List.prod, f a n) := by
          congr 1
          apply congrArg (actualPrimeLabelBlockProductSum B blocks)
          funext n
          exact hhead_sum n
        _ = (actualPrimeLabelBlocksFactorial blocks : ℝ) *
            ((m.factorial : ℝ) * actualPrimeLabelBlockProductSum B blocks
              (fun n => ∑ a ∈ T.image List.prod, f a n)) := by
          rw [actualPrimeLabelBlockProductSum_const_mul]
        _ = _ := by
          rw [← actualPrimeLabelBlockProductSum_finsetSum, Nat.cast_mul]
          ring

/-- This is the original reciprocal repeated-label factorial scalar.
Nothing is divided by a new total-slot or later group factorial. -/
theorem actualPrimeLabelBlocks_moebius_sum_normalized {ι : Type*}
    (B : ι → Finset ℕ) (blocks : List (ι × ℕ)) (r : ℕ) (H : ℕ → ℝ)
    (hprime : ∀ b ∈ blocks, ∀ q ∈ B b.1, Nat.Prime q) :
    (∑ ps ∈ actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks),
        (ArithmeticFunction.moebius (r * ps.prod) : ℝ) * H ps.prod) /
        (actualPrimeLabelBlocksFactorial blocks : ℝ) =
      actualPrimeLabelBlockProductSum B blocks
        (fun n => (ArithmeticFunction.moebius (r * n) : ℝ) * H n) := by
  have hfactor : (actualPrimeLabelBlocksFactorial blocks : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (actualPrimeLabelBlocksFactorial_pos blocks))
  apply (div_eq_iff hfactor).mpr
  simpa only [mul_comm] using actualPrimeLabelBlocks_moebius_sum B blocks r H hprime

/-- The exact full-product fibre retains every block-product vector with
that product. The literal Mobius coefficient, including its zero diagonal,
appears on both sides before any absolute value. -/
theorem actualPrimeLabelBlocks_moebius_fibre_normalized {ι : Type*}
    (B : ι → Finset ℕ) (blocks : List (ι × ℕ)) (r n : ℕ)
    (hprime : ∀ b ∈ blocks, ∀ q ∈ B b.1, Nat.Prime q) :
    ((ArithmeticFunction.moebius (r * n) : ℝ) *
        actualPrimeTupleCoefficient
          (actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)) n) /
        (actualPrimeLabelBlocksFactorial blocks : ℝ) =
      (ArithmeticFunction.moebius (r * n) : ℝ) *
        actualPrimeLabelBlockProductSum B blocks (fun k => if k = n then 1 else 0) := by
  let T := actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)
  have hfibre : (∑ ps ∈ T,
      (ArithmeticFunction.moebius (r * ps.prod) : ℝ) * (if ps.prod = n then 1 else 0)) =
      (ArithmeticFunction.moebius (r * n) : ℝ) * actualPrimeTupleCoefficient T n := by
    calc
      _ = ∑ _ps ∈ T.filter (fun ps => ps.prod = n),
          (ArithmeticFunction.moebius (r * n) : ℝ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro ps _
        by_cases h : ps.prod = n <;> simp [h]
      _ = _ := by
        simp only [actualPrimeTupleCoefficient, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h := actualPrimeLabelBlocks_moebius_sum_normalized B blocks r
    (fun k => if k = n then 1 else 0) hprime
  rw [hfibre] at h
  calc
    _ = actualPrimeLabelBlockProductSum B blocks
        (fun k => (ArithmeticFunction.moebius (r * k) : ℝ) * (if k = n then 1 else 0)) := h
    _ = actualPrimeLabelBlockProductSum B blocks
        (fun k => (ArithmeticFunction.moebius (r * n) : ℝ) * (if k = n then 1 else 0)) := by
      congr 1
      funext k
      by_cases hk : k = n <;> simp [hk]
    _ = _ := actualPrimeLabelBlockProductSum_const_mul B blocks _ _

end

end ImbalancedChen
