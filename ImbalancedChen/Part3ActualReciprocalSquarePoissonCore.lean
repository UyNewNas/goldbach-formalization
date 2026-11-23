import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson

/-!
# Actual reciprocal square at a fixed modulus and frequency multiplier

The fixed-modulus expansion reuses the signed inverses and conjugation from
`Part3ActualReciprocalSquarePoisson` of the P3.5 continuation. The carrier is
explicit, so the square argument can be used before any six-cover or Abel
recombination. The Poisson identity retains zero and both frequency signs.
-/

namespace ImbalancedChen.Part3.CanonicalReciprocalPhase

noncomputable section

def wPhaseInverse (n m : ℕ) : ℤ := n.gcdA m

theorem wPhaseInverse_spec {n m : ℕ} (h : n.Coprime m) :
    Int.ModEq m ((n : ℤ) * wPhaseInverse n m) 1 := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨n.gcdB m, ?_⟩
  have hb := Nat.gcd_eq_gcd_ab n m
  rw [h.gcd_eq_one, Nat.cast_one] at hb
  dsimp [wPhaseInverse]
  linarith

/-- Integer congruences give equal normalized phases, also for modulus one. -/
theorem wPhase_circle_eq_of_modEq {m : ℕ} (hm : 0 < m) {x y : ℤ}
    (h : Int.ModEq m x y) :
    (((x : ℝ) / m : ℝ) : UnitAddCircle) = ((y : ℝ) / m : ℝ) := by
  obtain ⟨z, hz⟩ := h.dvd
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨-z, ?_⟩
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hz' : (y : ℝ) - x = m * (z : ℝ) := by exact_mod_cast hz
  simp only [zsmul_eq_mul, Int.cast_neg, mul_one]
  field_simp
  nlinarith

end

end ImbalancedChen.Part3.CanonicalReciprocalPhase

namespace ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly

noncomputable section

open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open OriginalSmoothPoissonTail.Physical
open scoped BigOperators SchwartzMap FourierTransform
attribute [local instance] Classical.propDecidable

private theorem inverse_pair_modEq {m n t t' : ℕ}
    (hn : n.Coprime m) (ht : t.Coprime m) (ht' : t'.Coprime m)
    (h h' : ℤ) :
    Int.ModEq m
      (h * CanonicalReciprocalPhase.wPhaseInverse (n * t) m -
        h' * CanonicalReciprocalPhase.wPhaseInverse (n * t') m)
      ((h * (t' : ℤ) - h' * (t : ℤ)) *
        CanonicalReciprocalPhase.wPhaseInverse (n * (t * t')) m) := by
  let x := CanonicalReciprocalPhase.wPhaseInverse (n * t) m
  let x' := CanonicalReciprocalPhase.wPhaseInverse (n * t') m
  let j := CanonicalReciprocalPhase.wPhaseInverse (n * (t * t')) m
  have hx : Int.ModEq m (((n * t : ℕ) : ℤ) * x) 1 :=
    CanonicalReciprocalPhase.wPhaseInverse_spec (hn.mul_left ht)
  have hx' : Int.ModEq m (((n * t' : ℕ) : ℤ) * x') 1 :=
    CanonicalReciprocalPhase.wPhaseInverse_spec (hn.mul_left ht')
  have hj : Int.ModEq m (((n * (t * t') : ℕ) : ℤ) * j) 1 :=
    CanonicalReciprocalPhase.wPhaseInverse_spec (hn.mul_left (ht.mul_left ht'))
  have hleft : Int.ModEq m x ((t' : ℤ) * j) := by
    calc
      x ≡ x * (((n * (t * t') : ℕ) : ℤ) * j) [ZMOD m] := by
        simpa only [mul_one] using (hj.mul_left x).symm
      _ = ((t' : ℤ) * j) * (((n * t : ℕ) : ℤ) * x) := by
        push_cast
        ring
      _ ≡ (t' : ℤ) * j [ZMOD m] := by
        simpa only [mul_one] using hx.mul_left ((t' : ℤ) * j)
  have hright : Int.ModEq m x' ((t : ℤ) * j) := by
    calc
      x' ≡ x' * (((n * (t * t') : ℕ) : ℤ) * j) [ZMOD m] := by
        simpa only [mul_one] using (hj.mul_left x').symm
      _ = ((t : ℤ) * j) * (((n * t' : ℕ) : ℤ) * x') := by
        push_cast
        ring
      _ ≡ (t : ℤ) * j [ZMOD m] := by
        simpa only [mul_one] using hx'.mul_left ((t : ℤ) * j)
  have hdifference := (hleft.mul_left h).sub (hright.mul_left h')
  convert hdifference using 1; ring

private theorem fourier_pair_real (h h' : ℤ) (x x' : ℝ) :
    fourier h (x : UnitAddCircle) * star (fourier h' (x' : UnitAddCircle)) =
      fourier 1 ((((h : ℝ) * x - (h' : ℝ) * x') : ℝ) : UnitAddCircle) := by
  simp only [Complex.star_def]
  rw [← fourier_neg]
  simp only [fourier_coe_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Canonical Bezout inverse and least residue inverse are congruent.
The actual reciprocal phase can therefore consume the actual Poisson primitive. -/
theorem canonical_inverse_modEq {c n : ℕ} [NeZero c] (hn : n.Coprime c) :
    Int.ModEq c (CanonicalReciprocalPhase.wPhaseInverse n c) (inverseResidue c n) := by
  have hu : IsUnit (n : ZMod c) := (ZMod.isUnit_iff_coprime n c).mpr hn
  have hx : (n : ZMod c) * (CanonicalReciprocalPhase.wPhaseInverse n c : ZMod c) = 1 := by
    have hh := (ZMod.intCast_eq_intCast_iff _ _ c).mpr
      (CanonicalReciprocalPhase.wPhaseInverse_spec hn)
    simpa only [Int.cast_mul, Int.cast_natCast, Int.cast_one] using hh
  have hi : (CanonicalReciprocalPhase.wPhaseInverse n c : ZMod c) = (n : ZMod c)⁻¹ := by
    calc
      _ = ((n : ZMod c)⁻¹ * (n : ZMod c)) *
          (CanonicalReciprocalPhase.wPhaseInverse n c : ZMod c) := by
        rw [ZMod.inv_mul_of_unit _ hu, one_mul]
      _ = (n : ZMod c)⁻¹ * ((n : ZMod c) *
          (CanonicalReciprocalPhase.wPhaseInverse n c : ZMod c)) := mul_assoc _ _ _
      _ = _ := by rw [hx, mul_one]
  apply (ZMod.intCast_eq_intCast_iff _ _ c).mp
  simpa only [inverseResidue, Int.cast_natCast, ZMod.natCast_zmod_val] using hi

theorem canonical_character_eq_residuePhase {c b z : ℕ} [NeZero c]
    (hb : b.Coprime c) (hz : z.Coprime c) (a y : ℤ) :
    fourier 1 (((a*y*CanonicalReciprocalPhase.wPhaseInverse (b*z) c : ℤ) : ℝ) /
      (c : ℝ) : UnitAddCircle) = residuePhase a y (z : ℤ) (b : ZMod c) := by
  have hp := residuePhase_integer_fourier (c := c) a y (z : ℤ) (b : ℤ)
  simp only [Int.cast_natCast] at hp
  rw [hp]
  simp only [Int.natAbs_natCast, if_pos hb]
  have hh := CanonicalReciprocalPhase.wPhase_circle_eq_of_modEq (NeZero.pos c)
    ((canonical_inverse_modEq (c := c) (n := b*z) (hb.mul_left hz)).mul_left (a*y))
  simpa only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast] using congrArg (fourier 1) hh

abbrev Inner := ℕ × ℤ

def fixedUnit (A : ℕ) (a : ℤ) (t : ℕ) : Prop := t.Coprime A ∧ t.Coprime a.natAbs

def atomCoeff (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (u : Inner) : ℂ := lambda u.1 * omega u.2

def phase (a f : ℤ) (b c : ℕ) (u : Inner) : ℂ :=
  fourier (a*u.2*f)
    (((CanonicalReciprocalPhase.wPhaseInverse (b*u.1) c : ℝ)/(c : ℝ) : ℝ) : UnitAddCircle)

def atom (A : ℕ) (a f : ℤ) (b c : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (u : Inner) : ℂ :=
  if fixedUnit A a u.1 ∧ u.1.Coprime c then atomCoeff lambda omega u * phase a f b c u else 0

def level (u v : Inner) : ℕ := u.1*v.1

def difference (u v : Inner) : ℤ := u.2*(v.1 : ℤ)-v.2*(u.1 : ℤ)

def outputY (f : ℤ) (u v : Inner) : ℤ := f*difference u v

/-- The original reciprocal row on an explicit finite set of ordered
inner labels. A product set gives the separated modulus/frequency source. -/
def reciprocalRow (A : ℕ) (a f : ℤ) (b c : ℕ) (I : Finset Inner)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) : ℂ :=
  ∑ u ∈ I, atom A a f b c lambda omega u

/-- Expanding the inner product carrier gives the original separated row,
with the same individual coprime conditions and Bézout inverse. -/
theorem reciprocalRow_eq_separated (A : ℕ) (a f : ℤ) (b c : ℕ)
    (T : Finset ℕ) (K : Finset ℤ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) :
    reciprocalRow A a f b c (T ×ˢ K) lambda omega =
      ∑ t ∈ T, if t.Coprime (A * c) ∧ t.Coprime (a.natAbs * c) then
        lambda t * ∑ h ∈ K, omega h * fourier (a * h * f)
          (((CanonicalReciprocalPhase.wPhaseInverse (b * t) c : ℝ) /
            (c : ℝ)) : UnitAddCircle)
      else 0 := by
  have hgate (t : ℕ) : (t.Coprime (A * c) ∧ t.Coprime (a.natAbs * c)) ↔
      fixedUnit A a t ∧ t.Coprime c := by
    simp only [Nat.coprime_mul_iff_right, fixedUnit]
    tauto
  simp only [reciprocalRow, sum_product, hgate]
  apply sum_congr rfl
  intro t _
  by_cases ht : fixedUnit A a t ∧ t.Coprime c
  · simp only [atom, if_pos ht, atomCoeff, phase, mul_sum, mul_assoc]
  · simp only [atom, if_neg ht, sum_const_zero]

/-- Signed output y=f(h*t'-h'*t), z=t*t'. There is no absolute-value
replacement and no discarded k0 branch. -/
theorem phase_pair {c b : ℕ} [NeZero c] (hb : b.Coprime c)
    {u v : Inner} (hu : u.1.Coprime c) (hv : v.1.Coprime c) (a f : ℤ) :
    phase a f b c u * star (phase a f b c v) =
      residuePhase a (outputY f u v) (level u v : ℤ) (b : ZMod c) := by
  have hc := NeZero.pos c
  have hg := inverse_pair_modEq (m := c) (n := b) hb hu hv (a*u.2*f) (a*v.2*f)
  have hclean : Int.ModEq c
      ((a*u.2*f)*CanonicalReciprocalPhase.wPhaseInverse (b*u.1) c -
        (a*v.2*f)*CanonicalReciprocalPhase.wPhaseInverse (b*v.1) c)
      (a*outputY f u v*CanonicalReciprocalPhase.wPhaseInverse (b*level u v) c) := by
    convert hg using 1; dsimp [outputY,difference,level]; ring
  have hcircle := CanonicalReciprocalPhase.wPhase_circle_eq_of_modEq hc hclean
  simp only [phase]
  rw [fourier_pair_real]
  rw [show ((a*u.2*f : ℤ) : ℝ) * ((CanonicalReciprocalPhase.wPhaseInverse (b*u.1) c : ℝ)/c) -
      ((a*v.2*f : ℤ) : ℝ) * ((CanonicalReciprocalPhase.wPhaseInverse (b*v.1) c : ℝ)/c) =
      (((a*u.2*f)*CanonicalReciprocalPhase.wPhaseInverse (b*u.1) c -
        (a*v.2*f)*CanonicalReciprocalPhase.wPhaseInverse (b*v.1) c : ℤ) : ℝ)/c by push_cast; ring]
  exact (congrArg (fourier 1) hcircle).trans
    (canonical_character_eq_residuePhase (c := c) hb (hu.mul_left hv) a (outputY f u v))
private theorem atom_pair {c b : ℕ} [NeZero c] (hb : b.Coprime c)
    (A : ℕ) (a f : ℤ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (u v : Inner) :
    atom A a f b c lambda omega u * star (atom A a f b c lambda omega v) =
      if fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v) then
        (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
          residuePhase a (outputY f u v) (level u v : ℤ) (b : ZMod c) else 0 := by
  by_cases hg : fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v)
  · have huc : u.1.Coprime c := (Nat.coprime_mul_iff_right.mp hg.2.2).1.symm
    have hvc : v.1.Coprime c := (Nat.coprime_mul_iff_right.mp hg.2.2).2.symm
    have hgu : fixedUnit A a u.1 ∧ u.1.Coprime c := ⟨hg.1,huc⟩
    have hgv : fixedUnit A a v.1 ∧ v.1.Coprime c := ⟨hg.2.1,hvc⟩
    simp only [atom, if_pos hgu, if_pos hgv, if_pos hg, star_mul]
    calc
      _ = (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
          (phase a f b c u * star (phase a f b c v)) := by ring
      _ = _ := by rw [phase_pair (c := c) hb huc hvc]
  · rw [if_neg hg]
    by_cases hu : fixedUnit A a u.1 ∧ u.1.Coprime c
    · by_cases hv : fixedUnit A a v.1 ∧ v.1.Coprime c
      · exact False.elim (hg ⟨hu.1,hv.1,(hu.2.mul_left hv.2).symm⟩)
      · simp only [atom, if_neg hv, star_zero, mul_zero]
    · simp only [atom, if_neg hu, zero_mul]

/-- ACTUAL reciprocal square, with c-unit restrictions moved outside the
inner coefficient. Coefficients now depend only on fixed t,h,f labels. -/
theorem gated_square_eq_pairs {c : ℕ} [NeZero c] (A : ℕ) (a : ℤ)
    (I : Finset Inner) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (b : ℕ) (f : ℤ) :
    (if b.Coprime c then ((‖reciprocalRow A a f b c I lambda omega‖^2 : ℝ) : ℂ) else 0) =
      ∑ u ∈ I, ∑ v ∈ I,
        if fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v) then
          (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
            residuePhase a (outputY f u v) (level u v : ℤ) (b : ZMod c) else 0 := by
  by_cases hb : b.Coprime c
  · rw [if_pos hb, reciprocalRow, complex_norm_sq_sum_eq_double_star]
    exact sum_congr rfl (fun u hu => sum_congr rfl (fun v hv => atom_pair (c := c) hb A a f lambda omega u v))
  · simp only [if_neg hb, residuePhase_nat (c := c), mul_zero, ite_self, sum_const_zero]

/-- Genuine b-Poisson of the literal reciprocal SQUARE at fixed c,f.
This closes an algebraic/Poisson frontier before any spectral integral.
It includes y=0 (the k0 diagonal), all signed h and both signs of f. -/
theorem reciprocal_square_b_poisson {c : ℕ} [NeZero c]
    {M : ℝ} (hM : 0 < M) (B : Finset ℕ)
    (hB : ∀ b : ℕ, scaledDyadicCutoff M b ≠ 0 → b ∈ B)
    (A : ℕ) (a : ℤ) (I : Finset Inner) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (f : ℤ) :
    (∑ b ∈ B, (scaledDyadicCutoff M b : ℂ) *
      (if b.Coprime c then ((‖reciprocalRow A a f b c I lambda omega‖^2 : ℝ) : ℂ) else 0)) =
      ∑ u ∈ I, ∑ v ∈ I,
        if fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v) then
          (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
            ∑' m : ℤ, frequency M c a (outputY f u v) (level u v : ℤ) m else 0 := by
  simp_rw [gated_square_eq_pairs (c := c)]
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  by_cases hg : fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v)
  · simp only [if_pos hg]
    have hz : IsUnit ((level u v : ℤ) : ZMod c) :=
      ((isUnit_intCast_iff_natAbs_coprime (c := c) (level u v : ℤ)).mpr (by simpa only [Int.natAbs_natCast] using hg.2.2.symm))
    calc
      _ = (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
          finiteKernel (c := c) M B a (outputY f u v) (level u v : ℤ) := by
        simp only [finiteKernel, mul_sum]
        apply sum_congr rfl
        intro b hb
        ring
      _ = _ := by
        rw [finiteKernel_poisson (c := c) hM B
          hB a (outputY f u v) (level u v : ℤ) hz]
  · simp only [if_neg hg, mul_zero, sum_const_zero]

end

end ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly
