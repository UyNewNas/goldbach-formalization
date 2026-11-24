import Lean

/-!
The finite arithmetic for the Winner9 mixed moment of degree one. The
four labelled vertices may repeat. Their factorial weight is given by
an equality-partition kernel, whose signed weighted sum is the degree-one
coefficient from the certificate's generating function.
-/

namespace ImbalancedChen.P2Winner9FiniteMomentKernel

abbrev Vertex := Fin 9

def delta (i j : Vertex) : Int := if i = j then 1 else 0

def kernel (a b c d : Vertex) : Int :=
  1 + delta a b + delta a c + delta a d +
    delta b c + delta b d + delta c d +
    delta a b * delta c d +
    delta a c * delta b d +
    delta a d * delta b c +
    2 * (delta a b * delta a c + delta a b * delta a d +
      delta a c * delta a d + delta b c * delta b d) +
    6 * delta a b * delta a c * delta a d

def unitExponent (i r : Vertex) : Nat := if r = i then 1 else 0

def fourExponent (a b c d r : Vertex) : Nat :=
  unitExponent a r + unitExponent b r + unitExponent c r + unitExponent d r

private def finSum {n : Nat} (f : Fin n → Nat) : Nat := (List.ofFn f).sum

private theorem finSum_succ {n : Nat} (f : Fin (n + 1) → Nat) :
    finSum f = f 0 + finSum (fun i => f i.succ) := by
  simp [finSum, List.ofFn_succ]

private theorem finSum_zero {n : Nat} : finSum (fun _ : Fin n => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [finSum_succ, ih, Nat.add_zero]

private theorem finSum_add {n : Nat} (f g : Fin n → Nat) :
    finSum (fun i => f i + g i) = finSum f + finSum g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finSum_succ, finSum_succ f, finSum_succ g, ih]
    omega

private theorem finSum_unit {n : Nat} (i : Fin n) :
    finSum (fun r => if r = i then 1 else 0) = 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [finSum_succ]
      simp [Fin.succ_ne_zero, finSum_zero]
    · rw [finSum_succ]
      have h : (0 : Fin (n + 1)) ≠ j.succ := Ne.symm (Fin.succ_ne_zero j)
      simp [h, ih]

/-- Four labelled vertex factors have total degree four, including repeats. -/
theorem fourExponent_degree (a b c d : Vertex) :
    fourExponent a b c d 0 +
      (List.ofFn (fun q : Fin 8 => fourExponent a b c d q.succ)).sum + 8 = 12 := by
  change fourExponent a b c d 0 +
    finSum (fun q : Fin 8 => fourExponent a b c d q.succ) + 8 = 12
  have hs : finSum (fun r => fourExponent a b c d r) = 4 := by
    simp only [fourExponent, finSum_add, unitExponent, finSum_unit]
  rw [← finSum_succ (fun r => fourExponent a b c d r), hs]

def factorial (n : Nat) : Nat :=
  Nat.rec 1 (fun i previous => (i + 1) * previous) n

def factorialProduct (xs : List Nat) : Nat := (xs.map factorial).prod

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
theorem fourFactorial_kernel : ∀ a b c d : Vertex,
    (Int.ofNat (factorial (fourExponent a b c d 0) *
      factorialProduct (List.ofFn (fun q : Fin 8 => fourExponent a b c d q.succ)))) =
      kernel a b c d := by
  decide +kernel

def sumFin {n : Nat} (f : Fin n → Int) : Int := (List.ofFn f).sum
scoped macro "∑₉ " i:ident ", " r:term : term => `(sumFin fun $i : Fin 9 => $r)

private theorem sumFin_empty (f : Fin 0 → Int) : sumFin f = 0 := by
  simp [sumFin, List.ofFn_zero]

private theorem sumFin_succ {n : Nat} (f : Fin (n + 1) → Int) :
    sumFin f = f 0 + sumFin (fun i => f i.succ) := by
  simp [sumFin, List.ofFn_succ]

private theorem sumFin_add {n : Nat} (f g : Fin n → Int) :
    sumFin (fun i => f i + g i) = sumFin f + sumFin g := by
  induction n with
  | zero => simp [sumFin_empty]
  | succ n ih =>
    simp only [sumFin_succ, ih]
    ac_rfl

private theorem sumFin_mul {n : Nat} (f : Fin n → Int) (k : Int) :
    sumFin f * k = sumFin (fun i => f i * k) := by
  induction n with
  | zero => simp [sumFin_empty]
  | succ n ih => simp [sumFin_succ, Int.add_mul, ih]

private theorem mul_sumFin {n : Nat} (f : Fin n → Int) (k : Int) :
    k * sumFin f = sumFin (fun i => k * f i) := by
  induction n with
  | zero => simp [sumFin_empty]
  | succ n ih => simp [sumFin_succ, Int.mul_add, ih]

private theorem sumFin_zero {n : Nat} : sumFin (n := n) (fun _ => 0) = 0 := by
  induction n with
  | zero => simp [sumFin_empty]
  | succ n ih => simp [sumFin_succ, ih]

private theorem sumFin_eq_single {n : Nat} (a : Fin n) (f : Fin n → Int) :
    sumFin (fun i => if a = i then f i else 0) = f a := by
  induction n with
  | zero => exact a.elim0
  | succ n ih =>
    refine Fin.cases ?baseCase ?stepCase a
    · have h (i : Fin n) : (0 : Fin (n + 1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero i)
      simp [sumFin_succ, h, sumFin_zero]
    · intro a
      simp [sumFin_succ, Fin.succ_ne_zero, ih]

private theorem mul_ite_int (p : Prop) [Decidable p] (a b c : Int) :
    a * (if p then b else c) = if p then a * b else a * c := by
  by_cases hp : p <;> simp [hp]

private theorem sumFin_ite_const_condition (p : Prop) [Decidable p] (f : Fin 9 → Int) :
    (∑₉ i, if p then f i else 0) = if p then (∑₉ i, f i) else 0 := by
  by_cases hp : p <;> simp [hp, sumFin_zero]

private theorem sumFin_mul_pull_right₂ (f g : Fin 9 → Int) (k : Int) :
    (∑₉ i, f i * (g i * k)) = (∑₉ i, f i * g i) * k := by
  simp only [← Int.mul_assoc, sumFin_mul]

private theorem sumFin_mul_pull_right₃ (f g h : Fin 9 → Int) (k : Int) :
    (∑₉ i, f i * (g i * (h i * k))) = (∑₉ i, f i * (g i * h i)) * k := by
  simp only [← Int.mul_assoc, sumFin_mul]

private theorem sumFin_mul_pull_right₄ (f g h l : Fin 9 → Int) (k : Int) :
    (∑₉ i, f i * (g i * (h i * (l i * k)))) = (∑₉ i, f i * (g i * (h i * l i))) * k := by
  simp only [← Int.mul_assoc, sumFin_mul]

private theorem sumFin_mul_pull_middle (f g : Fin 9 → Int) (k : Int) :
    (∑₉ i, f i * (k * g i)) = k * (∑₉ i, f i * g i) := by
  simp only [mul_sumFin, Int.mul_left_comm]

private theorem sumFin_mul_pull_middle₃ (f g h : Fin 9 → Int) (k : Int) :
    (∑₉ i, f i * (g i * (k * h i))) = k * (∑₉ i, f i * (g i * h i)) := by
  simp only [mul_sumFin, Int.mul_left_comm]

/-- Collapse each equality partition to independent sums over its blocks. -/
theorem weighted_kernel_expansion (g y z : Fin 9 → Int) :
    (∑₉ a, ∑₉ b, ∑₉ c, ∑₉ e, g a * y b * z c * z e * kernel a b c e) =
      2 * (3 * ∑₉ i, g i * (z i)^2 * y i) +
      2 * ((∑₉ i, z i) * (2 * ∑₉ i, g i * z i * y i) +
        (∑₉ i, z i * y i) * (∑₉ i, g i * z i)) +
      ((∑₉ i, z i)^2 + (∑₉ i, (z i)^2)) * (∑₉ i, g i * y i) +
      (2 * (∑₉ i, z i) * (∑₉ i, z i * y i) +
        2 * (∑₉ i, (z i)^2 * y i)) * (∑₉ i, g i) +
      (∑₉ i, y i) *
        (2 * (∑₉ i, g i * (z i)^2) +
          2 * ((∑₉ i, z i) * (∑₉ i, g i * z i)) +
          ((∑₉ i, z i) * (∑₉ i, z i) + (∑₉ i, (z i)^2)) * (∑₉ i, g i)) := by
  simp only [kernel, Int.mul_add, sumFin_add]
  -- Substitute tied indices before factoring the remaining independent sums.
  simp only [delta, mul_ite_int, Int.mul_one, Int.mul_zero,
    sumFin_eq_single, sumFin_ite_const_condition]
  simp only [Int.mul_assoc, ← sumFin_mul, ← mul_sumFin, sumFin_mul_pull_right₂,
    sumFin_mul_pull_right₃, sumFin_mul_pull_right₄, sumFin_mul_pull_middle, sumFin_mul_pull_middle₃]
  have hyz (i : Fin 9) : y i * z i = z i * y i := Int.mul_comm _ _
  have hyzz (i : Fin 9) : y i * (z i * z i) = z i * (z i * y i) := by
    ac_rfl
  simp only [Int.pow_succ, Int.pow_zero, Int.one_mul, Int.mul_assoc, hyz, hyzz]
  grind

private def choose (n : Nat) : Nat → Nat :=
  Nat.rec (fun k => if k = 0 then 1 else 0)
    (fun _ previous k =>
      match k with
      | 0 => 1
      | j + 1 => previous j + previous (j + 1)) n

private theorem choose_two_two : choose 2 2 = 1 := rfl

private theorem choose_three_two : choose 3 2 = 3 := rfl

def conv (a b : Nat → Int) (k : Nat) : Int :=
  sumFin (n := k + 1) (fun r => a r * b (k - r))

private theorem conv_zero (a b : Nat → Int) : conv a b 0 = a 0 * b 0 := by
  simp [conv, sumFin_succ, sumFin_empty]

private theorem conv_one (a b : Nat → Int) :
    conv a b 1 = a 0 * b 1 + a 1 * b 0 := by
  simp [conv, sumFin_succ, sumFin_empty]

private def B1 (y z : Fin 9 → Int) (k : Nat) : Int :=
  ∑₉ i, z i * (y i)^k

private def B2 (y z : Fin 9 → Int) (k : Nat) : Int :=
  (k + 1 : Int) * (∑₉ i, (z i)^2 * (y i)^k)

private def W0 (g y : Fin 9 → Int) (k : Nat) : Int :=
  ∑₉ i, g i * (y i)^k

private def W1 (g y z : Fin 9 → Int) (k : Nat) : Int :=
  (k + 1 : Int) * (∑₉ i, g i * z i * (y i)^k)

private def W2 (g y z : Fin 9 → Int) (k : Nat) : Int :=
  (choose (k + 2) 2 : Int) * (∑₉ i, g i * (z i)^2 * (y i)^k)

def doubled (g y z : Fin 9 → Int) (k : Nat) : Int :=
  2 * W2 g y z k +
  2 * conv (B1 y z) (W1 g y z) k +
  conv (fun n => conv (B1 y z) (B1 y z) n + B2 y z n) (W0 g y) k

/-- The weighted kernel is the linear coefficient in the signed generating function. -/
theorem weighted_kernel_linear_coefficient (g y z : Fin 9 → Int) (h : Nat → Int)
    (h0 : h 0 = 1) (h1 : h 1 = ∑₉ i, y i) :
    (∑₉ a, ∑₉ b, ∑₉ c, ∑₉ e, g a * y b * z c * z e * kernel a b c e) =
      conv h (doubled g y z) 1 := by
  rw [weighted_kernel_expansion, conv_one, h0, h1, Int.one_mul]
  simp [doubled, B1, B2, W0, W1, W2, conv_one, conv_zero, choose_two_two, choose_three_two]
  grind

end ImbalancedChen.P2Winner9FiniteMomentKernel
