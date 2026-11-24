by
  classical
  have sep2 (F : Fin 9 → Fin 9 → ℤ)
      (f g : Fin 9 → ℤ) (k : ℤ)
      (hp : ∀ a b, F a b = k * f a * g b) :
      (∑ i : Fin 9, ∑ i : Fin 9, F i i) = k * (∑ i : Fin 9, f i) * (∑ i : Fin 9, g i) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    exact hp a b
  have sep3 (F : Fin 9 → Fin 9 → Fin 9 → ℤ)
      (f g h : Fin 9 → ℤ) (k : ℤ)
      (hp : ∀ a b c, F a b c = k * f a * g b * h c) :
      (∑ i : Fin 9, ∑ i : Fin 9, ∑ i : Fin 9, F i i i) = k * (∑ i : Fin 9, f i) * (∑ i : Fin 9, g i) * (∑ i : Fin 9, h i) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    exact hp a b c
  have sep4 (F : Fin 9 → Fin 9 → Fin 9 → Fin 9 → ℤ)
      (f g h r : Fin 9 → ℤ) (k : ℤ)
      (hp : ∀ a b c e, F a b c e = k * f a * g b * h c * r e) :
      (∑ i : Fin 9, ∑ i : Fin 9, ∑ i : Fin 9, ∑ i : Fin 9, F i i i i) = k * (∑ i : Fin 9, f i) * (∑ i : Fin 9, g i) * (∑ i : Fin 9, h i) * (∑ i : Fin 9, r i) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro e he
    exact hp a b c e
  have hk (g y z : Fin 9 → ℤ) :
      (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9,
        g a * y b * z c * z e * kernel a b c e) =
      (∑ i : Fin 9, g i) * (∑ i : Fin 9, y i) * (∑ i : Fin 9, z i)^2 +
      (∑ i : Fin 9, g i * y i) * (∑ i : Fin 9, z i)^2 +
      2 * (∑ i : Fin 9, g i * z i) * (∑ i : Fin 9, y i) * (∑ i : Fin 9, z i) +
      2 * (∑ i : Fin 9, g i) * (∑ i : Fin 9, z i * y i) * (∑ i : Fin 9, z i) +
      (∑ i : Fin 9, g i) * (∑ i : Fin 9, y i) * (∑ i : Fin 9, z i^2) +
      (∑ i : Fin 9, g i * y i) * (∑ i : Fin 9, z i^2) +
      2 * (∑ i : Fin 9, g i * z i) * (∑ i : Fin 9, z i * y i) +
      4 * (∑ i : Fin 9, g i * z i * y i) * (∑ i : Fin 9, z i) +
      2 * (∑ i : Fin 9, g i * z i^2) * (∑ i : Fin 9, y i) +
      2 * (∑ i : Fin 9, g i) * (∑ i : Fin 9, z i^2 * y i) +
      6 * (∑ i : Fin 9, g i * z i^2 * y i) := by
    have t0 : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9, g a * y b * z c * z e) =
        (∑ i : Fin 9, g i) * (∑ i : Fin 9, y i) * (∑ i : Fin 9, z i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep4
        (fun a b c e => g a * y b * z c * z e)
        g y z z 1 (by intro a b c e; ring)
    have t1 : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, g a * y a * z b * z c) =
        (∑ i : Fin 9, g i * y i) * (∑ i : Fin 9, z i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep3
        (fun a b c => g a * y a * z b * z c)
        (fun a => g a * y a) z z 1 (by intro a b c; ring)
    have t2 : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, g a * y b * z a * z c) =
        (∑ i : Fin 9, g i * z i) * (∑ i : Fin 9, y i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep3
        (fun a b c => g a * y b * z a * z c)
        (fun a => g a * z a) y z 1 (by intro a b c; ring)
    have t3 : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, g a * y b * z c * z a) =
        (∑ i : Fin 9, g i * z i) * (∑ i : Fin 9, y i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep3
        (fun a b c => g a * y b * z c * z a)
        (fun a => g a * z a) y z 1 (by intro a b c; ring)
    have t4 : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, g a * y b * z b * z c) =
        (∑ i : Fin 9, g i) * (∑ i : Fin 9, z i * y i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep3
        (fun a b c => g a * y b * z b * z c)
        g (fun b => z b * y b) z 1 (by intro a b c; ring)
    have t5 : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, g a * y b * z c * z b) =
        (∑ i : Fin 9, g i) * (∑ i : Fin 9, z i * y i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep3
        (fun a b c => g a * y b * z c * z b)
        g (fun b => z b * y b) z 1 (by intro a b c; ring)
    have t6 : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, g a * y b * z c^2) =
        (∑ i : Fin 9, g i) * (∑ i : Fin 9, y i) * (∑ i : Fin 9, z i^2) := by
      simpa only [one_mul] using sep3
        (fun a b c => g a * y b * z c^2)
        g y (fun c => z c^2) 1 (by intro a b c; ring)
    have t7 : (∑ a : Fin 9, ∑ b : Fin 9, g a * y a * z b^2) =
        (∑ i : Fin 9, g i * y i) * (∑ i : Fin 9, z i^2) := by
      simpa only [one_mul] using sep2
        (fun a b => g a * y a * z b^2)
        (fun a => g a * y a) (fun b => z b^2) 1 (by intro a b; ring)
    have t8 : (∑ a : Fin 9, ∑ b : Fin 9, g a * y b * z a * z b) =
        (∑ i : Fin 9, g i * z i) * (∑ i : Fin 9, z i * y i) := by
      simpa only [one_mul] using sep2
        (fun a b => g a * y b * z a * z b)
        (fun a => g a * z a) (fun b => z b * y b) 1 (by intro a b; ring)
    have t9 : (∑ a : Fin 9, ∑ b : Fin 9, g a * y b * z b * z a) =
        (∑ i : Fin 9, g i * z i) * (∑ i : Fin 9, z i * y i) := by
      simpa only [one_mul] using sep2
        (fun a b => g a * y b * z b * z a)
        (fun a => g a * z a) (fun b => z b * y b) 1 (by intro a b; ring)
    have t10 : (∑ a : Fin 9, ∑ b : Fin 9, g a * y a * z a * z b * 2) =
        2 * (∑ i : Fin 9, g i * z i * y i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep2
        (fun a b => g a * y a * z a * z b * 2)
        (fun a => g a * z a * y a) z 2 (by intro a b; ring)
    have t11 : (∑ a : Fin 9, ∑ b : Fin 9, g a * y a * z b * z a * 2) =
        2 * (∑ i : Fin 9, g i * z i * y i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep2
        (fun a b => g a * y a * z b * z a * 2)
        (fun a => g a * z a * y a) z 2 (by intro a b; ring)
    have t12 : (∑ a : Fin 9, ∑ b : Fin 9, g a * y b * z a^2 * 2) =
        2 * (∑ i : Fin 9, g i * z i^2) * (∑ i : Fin 9, y i) := by
      simpa only [one_mul] using sep2
        (fun a b => g a * y b * z a^2 * 2)
        (fun a => g a * z a^2) y 2 (by intro a b; ring)
    have t13 : (∑ a : Fin 9, ∑ b : Fin 9, g a * y b * z b^2 * 2) =
        2 * (∑ i : Fin 9, g i) * (∑ i : Fin 9, z i^2 * y i) := by
      simpa only [one_mul] using sep2
        (fun a b => g a * y b * z b^2 * 2)
        g (fun b => z b^2 * y b) 2 (by intro a b; ring)
    have t14 : (∑ a : Fin 9, g a * y a * z a^2 * 6) =
        6 * (∑ a : Fin 9, g a * z a^2 * y a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    conv_lhs =>
      simp [kernel, delta, Finset.sum_add_distrib, Finset.sum_mul,
        Finset.mul_sum, mul_add, add_mul, mul_ite]
    simp only [mul_assoc, ← pow_two] at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 ⊢
    linear_combination t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14
  rw [hk, mixed_numerator_one, doubled_one, homogeneous_one]
  simp [doubled, conv_zero, B1, B2, W0, W1, W2] <;> ring
