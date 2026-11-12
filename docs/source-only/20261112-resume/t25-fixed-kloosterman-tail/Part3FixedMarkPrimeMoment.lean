import ImbalancedChen.Part3CenteredFourier
import ImbalancedChen.Part3CoprimeKloostermanCRT
import ImbalancedChen.P3FiniteKloostermanUnitScaling
import Mathlib.Tactic

/-! Uncompiled source. Double-character orthogonality and the two branches of
the inverse-graph additive energy. No estimate is supplied as a hypothesis. -/

noncomputable section
namespace ImbalancedChen.Part3.FixedMarkTail
open Classical Finset
open scoped BigOperators ComplexConjugate
open OriginalSmoothPoissonTail
attribute [local instance] Classical.propDecidable

private theorem star_phase {p : ℕ} [NeZero p] (v : ZMod p) :
    star (ZMod.stdAddChar v) = ZMod.stdAddChar (-v) := by
  have h : ‖ZMod.stdAddChar v‖ = 1 := by
    simpa only [ZMod.stdAddChar_apply] using Circle.norm_coe (ZMod.toCircle v)
  have h₁ : ZMod.stdAddChar v * star (ZMod.stdAddChar v) = 1 := by
    change ZMod.stdAddChar v * conj (ZMod.stdAddChar v) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h, one_pow, Complex.ofReal_one]
  have h₂ : ZMod.stdAddChar v * ZMod.stdAddChar (-v) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  exact (eq_inv_of_mul_eq_one_right h₁).trans (eq_inv_of_mul_eq_one_right h₂).symm

private def phase {p : ℕ} [NeZero p] (a b : ZMod p) (v : ZMod p × ZMod p) : ℂ :=
  ZMod.stdAddChar (a * v.1 + b * v.2)

private theorem phase_ortho {p : ℕ} [NeZero p] (x y : ZMod p × ZMod p) :
    (∑ a, ∑ b, phase a b x * star (phase a b y)) =
      if x = y then (p : ℂ)^2 else 0 := by
  have h (a b : ZMod p) :
      phase a b x * star (phase a b y) =
        ZMod.stdAddChar (a * (x.1 - y.1)) * ZMod.stdAddChar (b * (x.2 - y.2)) := by
    unfold phase
    rw [star_phase, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [h, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simp_rw [ImbalancedChen.Part3.sum_stdAddChar_mul_eq]
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  by_cases h₁ : x₁ = y₁ <;> by_cases h₂ : x₂ = y₂ <;>
    simp [sub_eq_zero, h₁, h₂, pow_two]

/-- The square-norm transform of an actual finite point multiset in the
two-dimensional frequency plane, with all multiplicities retained. -/
theorem plane_energy {p : ℕ} [NeZero p] {I : Type*} [Fintype I]
    (k : I → ZMod p × ZMod p) :
    (∑ a, ∑ b, ‖∑ x, phase a b (k x)‖^2) =
      (p : ℝ)^2 * ∑ x, ∑ y, (if k x = k y then (1 : ℝ) else 0) := by
  have term (a b : ZMod p) :
      ((‖∑ x, phase a b (k x)‖^2 : ℝ) : ℂ) =
        ∑ x, ∑ y, phase a b (k x) * star (phase a b (k y)) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    change (∑ x, phase a b (k x)) * star (∑ y, phase a b (k y)) = _
    rw [star_sum, Finset.sum_mul_sum]
  apply Complex.ofReal_injective
  calc
    _ = ∑ a, ∑ b, ∑ x, ∑ y, phase a b (k x) * star (phase a b (k y)) := by
      simp only [Complex.ofReal_sum, term]
    _ = ∑ x, ∑ y, ∑ a, ∑ b, phase a b (k x) * star (phase a b (k y)) := by
      let F (a b : ZMod p) (x y : I) := phase a b (k x) * star (phase a b (k y))
      change (∑ a, ∑ b, ∑ x, ∑ y, F a b x y) = ∑ x, ∑ y, ∑ a, ∑ b, F a b x y
      calc
        _ = ∑ a, ∑ x, ∑ b, ∑ y, F a b x y :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        _ = ∑ x, ∑ a, ∑ b, ∑ y, F a b x y := Finset.sum_comm
        _ = ∑ x, ∑ a, ∑ y, ∑ b, F a b x y :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
        _ = _ := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := by
      simp only [phase_ortho, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_natCast, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp

private abbrev U (p : ℕ) := (ZMod p)ˣ

private def point {p : ℕ} (x : U p) : ZMod p × ZMod p :=
  (x, (↑(x⁻¹) : ZMod p))
private def key {p : ℕ} (v : U p × U p) : ZMod p × ZMod p :=
  point v.1 + point v.2

private theorem inverse_graph_cases {p : ℕ} [Fact p.Prime]
    (x y v w : U p) (he : key (x,y) = key (v,w)) :
    ((x,y) = (v,w)) ∨ ((x,y) = (w,v)) ∨ (y = -x ∧ w = -v) := by
  have hs : (x : ZMod p) + y = (v : ZMod p) + w := congrArg Prod.fst he
  have hi : (↑(x⁻¹) : ZMod p) + ↑(y⁻¹) =
      (↑(v⁻¹) : ZMod p) + ↑(w⁻¹) := congrArg Prod.snd he
  by_cases hz : (x : ZMod p) + y = 0
  · right; right
    constructor
    · apply Units.ext
      simp only [Units.val_neg]
      linear_combination hz
    · apply Units.ext
      simp only [Units.val_neg]
      linear_combination hz - hs
  · have invs (s t : U p) :
        ((↑(s⁻¹) : ZMod p) + ↑(t⁻¹)) * ((s : ZMod p) * t) = (s : ZMod p) + t := by
      simp only [Units.val_inv_eq_inv_val]
      field_simp [s.ne_zero, t.ne_zero] <;> ring
    have hprod : (x : ZMod p) * y = (v : ZMod p) * w := by
      apply mul_left_cancel₀ hz
      calc
        ((x : ZMod p) + y) * (↑x * ↑y) =
            ((↑(v⁻¹) + ↑(w⁻¹)) * (↑v * ↑w)) * (↑x * ↑y) := by rw [invs, hs]
        _ = ((↑(x⁻¹) + ↑(y⁻¹)) * (↑x * ↑y)) * (↑v * ↑w) := by rw [hi]; ring
        _ = _ := by rw [invs]
    have hzero : ((v : ZMod p) - x) * ((v : ZMod p) - y) = 0 := by
      linear_combination -(v : ZMod p) * hs + hprod
    rcases mul_eq_zero.mp hzero with h | h
    · have hx : v = x := Units.ext (sub_eq_zero.mp h)
      subst v
      have hy : y = w := Units.ext (add_left_cancel hs)
      simp [hy]
    · have hy : v = y := Units.ext (sub_eq_zero.mp h)
      subst v
      have hx : x = w := Units.ext (by linear_combination hs)
      simp [hx]

private theorem collision_bound {p : ℕ} [Fact p.Prime] :
    (∑ s : U p × U p, ∑ t : U p × U p,
      (if key s = key t then (1 : ℝ) else 0)) ≤ 3 * (Fintype.card (U p) : ℝ)^2 := by
  have H (s t : U p × U p) :
      (if key s = key t then (1 : ℝ) else 0) ≤
      (if s = t then 1 else 0) + (if s.swap = t then 1 else 0) +
      (if s.2 = -s.1 ∧ t.2 = -t.1 then 1 else 0) := by
    rcases s with ⟨x,y⟩
    rcases t with ⟨v,w⟩
    by_cases h : key (x,y) = key (v,w)
    · rcases inverse_graph_cases x y v w h with h₁|h₂|h₃
      · simp only [h, h₁, if_true]
        split_ifs <;> norm_num
      · have h' := congrArg Prod.swap h₂
        simp only [Prod.swap_prod_mk] at h'
        simp only [h, Prod.swap_prod_mk, h', if_true]
        split_ifs <;> norm_num
      · simp only [h, h₃, and_self, if_true]
        split_ifs <;> norm_num
    · simp only [if_neg h]
      split_ifs <;> norm_num
  calc
    _ ≤ _ := Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun t _ => H s t))
    _ = _ := by
      have hfix (s : U p × U p) : (∑ t : U p × U p,
          (if s = t then (1:ℝ) else 0)) = 1 := by simp
      simp only [Finset.sum_add_distrib, hfix]
      simp [Fintype.sum_prod_type, ite_and, pow_two, Finset.sum_ite_irrel]
      <;> ring

private def K {p : ℕ} [NeZero p] (a b : ZMod p) : ℂ :=
  ∑ u : U p, phase a b (point u)

private theorem K_sq {p : ℕ} [NeZero p] (a b : ZMod p) :
    K a b ^ 2 = ∑ s : U p × U p, phase a b (key s) := by
  rw [pow_two, K, Finset.sum_mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  unfold phase key
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  ring

private theorem K_physical {p : ℕ} [Fact p.Prime] (m n : ℤ) :
    kloosterman p m n = K (m : ZMod p) (n : ZMod p) := by
  rw [Physical.kloosterman_eq_zmod, K, ← Finset.sum_filter]
  apply Finset.sum_bij (fun (x : ZMod p) hx =>
    (Finset.mem_filter.mp hx).2.unit)
  · simp
  · intro x hx y hy he
    simpa using congrArg Units.val he
  · intro u _
    refine ⟨(u : ZMod p), mem_filter.mpr ⟨mem_univ _, u.isUnit⟩, ?_⟩
    apply Units.ext
    simp
  · intro x hx
    simp [phase, point, Units.val_inv_eq_inv_val]

private theorem K_orbit {p : ℕ} [Fact p.Prime] (a b : ZMod p) (t : U p) :
    K (a * t) (b * ↑(t⁻¹)) = K a b := by
  unfold K
  apply Fintype.sum_bijective (fun x : U p => t * x) (Group.mulLeft_bijective t)
  intro x
  unfold phase point
  congr 1
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- A literal pointwise prime bound with a unit first mark, uniform in the
second (including zero). Uses an orbit of size p−1, not an average claim. -/
theorem prime_physical_fourth_le {p : ℕ} (hp : p.Prime) (m n : ℤ)
    (hm : (m : ZMod p) ≠ 0) :
    ‖kloosterman p m n‖^4 ≤ 3 * (p : ℝ)^3 := by
  letI : Fact p.Prime := ⟨hp⟩
  let a : ZMod p := m
  let b : ZMod p := n
  let Φ (v : ZMod p × ZMod p) : ℝ := ‖K v.1 v.2‖^4
  let orb (t : U p) : ZMod p × ZMod p := (a * t, b * ↑(t⁻¹))
  have inj : Function.Injective orb := by
    intro t u he
    exact Units.ext (mul_left_cancel₀ hm (congrArg Prod.fst he))
  have cardU : Fintype.card (U p) = p-1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hcard : (Fintype.card (U p) : ℝ) = (p : ℝ)-1 := by
    rw [cardU, Nat.cast_sub hp.one_le, Nat.cast_one]
  have forall_sq (A B : ZMod p) :
      ‖K A B‖^4 = ‖∑ s : U p × U p, phase A B (key s)‖^2 := by
    rw [← K_sq, norm_pow]
    ring
  have hsum : (p-1 : ℝ) * ‖K a b‖^4 ≤
      (p : ℝ)^2 * (3 * (p-1 : ℝ)^2) := by
    calc
      _ = ∑ t : U p, Φ (orb t) := by simp [Φ, orb, K_orbit, hcard, nsmul_eq_mul]
      _ = ∑ v ∈ Finset.univ.image orb, Φ v := (Finset.sum_image inj.injOn).symm
      _ ≤ ∑ v : ZMod p × ZMod p, Φ v :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => pow_nonneg (norm_nonneg _) _)
      _ = (p : ℝ)^2 * ∑ s, ∑ t, (if key s = key t then (1 : ℝ) else 0) := by
        conv_lhs => rw [Fintype.sum_prod_type]
        simp only [Φ, forall_sq]
        exact plane_energy key
      _ ≤ _ := by
        gcongr
        simpa [hcard] using (collision_bound (p := p))
  have h₁ : ‖K a b‖^4 ≤ 3*(p : ℝ)^2*((p : ℝ)-1) := by
    apply le_of_mul_le_mul_left (a := (p:ℝ)-1) _ (sub_pos.mpr hpR)
    nlinarith [hsum]
  rw [K_physical]
  change ‖K a b‖^4 ≤ _
  nlinarith [sq_nonneg (p : ℝ)]

end ImbalancedChen.Part3.FixedMarkTail
