-- This lemma is higher priority than later `zero_smul` so that the `simpNF` is happy
@[to_additive (attr := simp high) zero_nsmul]
theorem pow_zero (a : M) : a ^ 0 = 1 :=
  Monoid.npow_zero _

@[to_additive succ_nsmul]
theorem pow_succ (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a :=
  Monoid.npow_succ n a

@[to_additive one_nsmul, simp]
lemma pow_one (a : M) : a ^ 1 = a := by rw [pow_succ, pow_zero, one_mul]

@[to_additive succ_nsmul'] lemma pow_succ' (a : M) : ∀ n, a ^ (n + 1) = a * a ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ _ n, pow_succ, pow_succ', mul_assoc]

@[to_additive] lemma mul_pow_mul (a b : M) (n : ℕ) :
