import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
import ImbalancedChen.Part3ActualPositiveLatticeSmoothCover

/-!
SOURCEONLY / UNCOMPILED / ONE minimal P2 candidate.
Proposed module: ImbalancedChen.Part3ActualReciprocalSquarePoisson.
Both direct imports have genuine actual source files. P0 ac0a81a4 is pending
compile2; P1 1c301ccd has been installed by ROOT and is pending compilation.
Their source presence is not a claim that either parent or this P2 is accepted.
The following 382LF namespace body is copied BYTE-FOR-BYTE from bodypack
1e6ad5c9ceb7b13964ade78742e1d760e87180b77fe5acfb8d82d113c67aef73.
Its 21 proof bodies and five local private helpers stay together. No owned
P0/P1/M1/M2 prefix or optional actual07/Gram373/spectral branch is recopied.
Only ROOT controls actual installation, compilation and subsequent acceptance.
-/

namespace ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly
noncomputable section
open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open OriginalSmoothPoissonTail.Physical ActualFixedFeaturePacketPushforwardSourceOnly
open ActualPositiveLatticeSmoothCoverSourceOnly
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

def innerCarrier (S : ℝ) (H : ℕ) : Finset Inner := factorCarrier S ×ˢ poissonNonzeroFrequencyWindow H

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

private theorem inner_gate_iff (A : ℕ) (a : ℤ) (c t : ℕ) :
    (t.Coprime (A*c) ∧ t.Coprime (a.natAbs*c)) ↔ fixedUnit A a t ∧ t.Coprime c := by
  simp only [Nat.coprime_mul_iff_right, fixedUnit]
  tauto

/-- An exact finite t carrier, needed for the actual quotient image. No
claim that that image equals a full dyadic factorCarrier is required. -/
def finiteInnerCarrier (T : Finset ℕ) (H : ℕ) : Finset Inner := T ×ˢ poissonNonzeroFrequencyWindow H

def finiteReciprocalRow (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (k : Packet) : ℂ :=
  ∑ t ∈ T,
    if t.Coprime (A*k.1.2) ∧ t.Coprime (a.natAbs*k.1.2) then
      lambda t * ∑ h ∈ poissonNonzeroFrequencyWindow H,
        omega h * fourier (a*h*k.2)
          (((CanonicalReciprocalPhase.wPhaseInverse (k.1.1*t) k.1.2 : ℝ) /
            (k.1.2 : ℝ) : ℝ) : UnitAddCircle)
    else 0

theorem literalRow_eq_finiteRow (A : ℕ) (a : ℤ) (S : ℝ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) :
    reciprocalPacketRow A a S H lambda omega = finiteReciprocalRow A a (factorCarrier S) H lambda omega := by
  rfl

/-- Exact flattening for EVERY finite actual t carrier. -/
theorem finiteRow_eq_atoms (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (b c : ℕ) (f : ℤ) :
    finiteReciprocalRow A a T H lambda omega ((b,c),f) =
      ∑ u ∈ finiteInnerCarrier T H, atom A a f b c lambda omega u := by
  simp only [finiteReciprocalRow, finiteInnerCarrier, sum_product]
  apply sum_congr rfl
  intro t ht
  simp only [inner_gate_iff]
  by_cases hu : fixedUnit A a t ∧ t.Coprime c
  · simp only [if_pos hu, atom, atomCoeff, phase, mul_sum, mul_assoc]
  · simp only [if_neg hu, atom, sum_const_zero]

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
    (T : Finset ℕ) (H : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (b : ℕ) (f : ℤ) :
    (if b.Coprime c then ((‖finiteReciprocalRow A a T H lambda omega ((b,c),f)‖^2 : ℝ) : ℂ) else 0) =
      ∑ u ∈ finiteInnerCarrier T H, ∑ v ∈ finiteInnerCarrier T H,
        if fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v) then
          (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
            residuePhase a (outputY f u v) (level u v : ℤ) (b : ZMod c) else 0 := by
  by_cases hb : b.Coprime c
  · rw [if_pos hb, finiteRow_eq_atoms, complex_norm_sq_sum_eq_double_star]
    exact sum_congr rfl (fun u hu => sum_congr rfl (fun v hv => atom_pair (c := c) hb A a f lambda omega u v))
  · simp only [if_neg hb, residuePhase_nat (c := c), mul_zero, ite_self, sum_const_zero]

private theorem full_b_support {M B : ℝ} (_hM : 0 < M) (hMB : M ≤ 2*B)
    (b : ℕ) (hb : scaledDyadicCutoff M b ≠ 0) : b ∈ Ioc 0 (Nat.floor (5*B)) := by
  have hp : dyadicCutoffSchwartz ((b : ℝ)/M) ≠ 0 := by
    simpa only [scaledDyadicCutoff, dyadicCutoffSchwartz_apply, ne_eq, Complex.ofReal_eq_zero] using hb
  obtain ⟨_, hbp, _, hhi⟩ := physical_cutoff_nonzero_nat_modulus hp
  exact mem_Ioc.mpr ⟨hbp, Nat.le_floor (by linarith)⟩

/-- Genuine b-Poisson of the literal reciprocal SQUARE at fixed c,f.
This closes an algebraic/Poisson frontier before any spectral integral.
It includes y=0 (the k0 diagonal), all signed h and both signs of f. -/
theorem reciprocal_square_b_poisson {c : ℕ} [NeZero c]
    {M B : ℝ} (hM : 0 < M) (hMB : M ≤ 2*B)
    (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (f : ℤ) :
    (∑ b ∈ Ioc 0 (Nat.floor (5*B)), (scaledDyadicCutoff M b : ℂ) *
      (if b.Coprime c then ((‖finiteReciprocalRow A a T H lambda omega ((b,c),f)‖^2 : ℝ) : ℂ) else 0)) =
      ∑ u ∈ finiteInnerCarrier T H, ∑ v ∈ finiteInnerCarrier T H,
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
          finiteKernel (c := c) M (Ioc 0 (Nat.floor (5*B))) a (outputY f u v) (level u v : ℤ) := by
        simp only [finiteKernel, mul_sum]
        apply sum_congr rfl
        intro b hb
        ring
      _ = _ := by
        rw [finiteKernel_poisson (c := c) hM (Ioc 0 (Nat.floor (5*B)))
          (full_b_support hM hMB) a (outputY f u v) (level u v : ℤ) hz]
  · simp only [if_neg hg, mul_zero, sum_const_zero]

/-- Exact cast/reordering of a six-cover smooth square. The SAME lambda,
omega,H,f and b,c gates are retained; no termwise positivity is invented. -/
theorem smoothMass_eq_gated_squares (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N B C F : ℝ) :
    (smoothMass M N (packetBox B C F) (finiteReciprocalRow A a T H lambda omega) : ℂ) =
      ∑ c ∈ Ioc 0 (Nat.floor (10*C)), ∑ f ∈ Icc (Int.ceil (-F)) (Int.floor F),
        if f ≠ 0 then (scaledDyadicCutoff N c : ℂ) *
          (∑ b ∈ Ioc 0 (Nat.floor (5*B)), (scaledDyadicCutoff M b : ℂ) *
            (if b.Coprime c then
              ((‖finiteReciprocalRow A a T H lambda omega ((b,c),f)‖^2 : ℝ) : ℂ) else 0)) else 0 := by
  rw [smoothMass_lattice]
  simp only [Complex.ofReal_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro c hc
  rw [sum_comm]
  apply sum_congr rfl
  intro f hf
  by_cases hfn : f ≠ 0
  · rw [if_pos hfn, mul_sum]
    apply sum_congr rfl
    intro b hb
    by_cases hbc : b.Coprime c
    · have hgate : b.Coprime c ∧ f ≠ 0 := ⟨hbc,hfn⟩
      simp only [if_pos hgate, if_pos hbc, Complex.ofReal_mul]
      ring
    · have hgate : ¬ (b.Coprime c ∧ f ≠ 0) := fun h => hbc h.1
      simp only [if_neg hgate, if_neg hbc, Complex.ofReal_zero, mul_zero]
  · simp [hfn]

/-- One COMPLETE actual smooth piece is now an explicit finite c,f,t,h
family of absolutely summable completed Kloosterman series. The sum still
includes y=0, so no tau(0) or nonzero-frequency convention has been used. -/
theorem smoothMass_eq_completed_pairs (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {M B : ℝ} (hM : 0 < M) (hMB : M ≤ 2*B)
    (N C F : ℝ) :
    (smoothMass M N (packetBox B C F) (finiteReciprocalRow A a T H lambda omega) : ℂ) =
      ∑ c ∈ Ioc 0 (Nat.floor (10*C)), ∑ f ∈ Icc (Int.ceil (-F)) (Int.floor F),
        if f ≠ 0 then (scaledDyadicCutoff N c : ℂ) *
          (∑ u ∈ finiteInnerCarrier T H, ∑ v ∈ finiteInnerCarrier T H,
            if fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v) then
              (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
                ∑' m : ℤ, frequency M c a (outputY f u v) (level u v : ℤ) m else 0) else 0 := by
  rw [smoothMass_eq_gated_squares]
  apply sum_congr rfl
  intro c hc
  let : NeZero c := ⟨(mem_Ioc.mp hc).1.ne'⟩
  apply sum_congr rfl
  intro f hf
  by_cases hfn : f ≠ 0
  · rw [if_pos hfn, if_pos hfn, reciprocal_square_b_poisson (c := c) hM hMB]
  · rw [if_neg hfn, if_neg hfn]

/-- The completed family of ONE positive smooth piece; every tuple and
all original fixed coefficients remain literal. -/
def completedPiece (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N _B C F : ℝ) : ℂ :=
  ∑ c ∈ Ioc 0 (Nat.floor (10*C)), ∑ f ∈ Icc (Int.ceil (-F)) (Int.floor F),
    if f ≠ 0 then (scaledDyadicCutoff N c : ℂ) *
      (∑ u ∈ finiteInnerCarrier T H, ∑ v ∈ finiteInnerCarrier T H,
        if fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v) then
          (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
            ∑' m : ℤ, frequency M c a (outputY f u v) (level u v : ℤ) m else 0) else 0

/-- All six actual psi-scale pairs are completed EXACTLY, with their
same common h/f carriers and no extra Cauchy or mode-counting factor. -/
theorem sixSmoothMass_eq_completed (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {B : ℝ} (hB : 0 < B) (C F : ℝ) :
    (sixSmoothMass B C (packetBox B C F) (finiteReciprocalRow A a T H lambda omega) : ℂ) =
      completedPiece A a T H lambda omega B C B C F +
      completedPiece A a T H lambda omega B (2*C) B C F +
      completedPiece A a T H lambda omega B (4*C) B C F +
      completedPiece A a T H lambda omega (2*B) C B C F +
      completedPiece A a T H lambda omega (2*B) (2*C) B C F +
      completedPiece A a T H lambda omega (2*B) (4*C) B C F := by
  have hp (M N : ℝ) (hM : 0 < M) (hMB : M ≤ 2*B) :
      (smoothMass M N (packetBox B C F) (finiteReciprocalRow A a T H lambda omega) : ℂ) =
        completedPiece A a T H lambda omega M N B C F :=
    smoothMass_eq_completed_pairs A a T H lambda omega hM hMB N C F
  have hb : B ≤ 2*B := by linarith
  have hb2 : 0 < 2*B := by positivity
  simp only [sixSmoothMass, Complex.ofReal_add]
  rw [hp B C hB hb, hp B (2*C) hB hb, hp B (4*C) hB hb,
    hp (2*B) C hb2 le_rfl, hp (2*B) (2*C) hb2 le_rfl, hp (2*B) (4*C) hb2 le_rfl]
/-- Summability is supplied by the actual physical Poisson theorem, not
silently inferred from a finite tuple index. -/
theorem completed_pair_summable {c : ℕ} [NeZero c] {M : ℝ} (hM : 0 < M)
    (a f : ℤ) (u v : Inner) (hcz : c.Coprime (level u v)) :
    Summable (fun m : ℤ => ‖frequency M c a (outputY f u v) (level u v : ℤ) m‖) := by
  exact completed_summable_norm (c := c) hM a (outputY f u v) (level u v : ℤ)
    ((isUnit_intCast_iff_natAbs_coprime (c := c) (level u v : ℤ)).mpr
      (by simpa only [Int.natAbs_natCast] using hcz.symm))

/-- The actual a-unit level licence follows from both retained t gates.
This is the CoprimePacket gate required after y,z grouping, including |a|=0. -/
theorem output_level_residue_coprime (A : ℕ) (a : ℤ) {u v : Inner}
    (hu : fixedUnit A a u.1) (hv : fixedUnit A a v.1) :
    a.natAbs.Coprime (level u v) := (hu.2.mul_left hv.2).symm

/-- Positive level comes from actual t>0; no fictitious positive level0. -/
theorem output_level_pos {u v : Inner} (hu : 0 < u.1) (hv : 0 < v.1) : 0 < level u v :=
  Nat.mul_pos hu hv

/-- Exact completed-frequency sign conversion by u -> -u on ALL residues,
valid also at modulus1. It does not conjugate or replace any coefficient. -/
theorem kloosterman_both_negative {c : ℕ} [NeZero c] (m n : ℤ) :
    kloosterman c (-m) (-n) = kloosterman c m n := by
  rw [kloosterman_eq_zmod (c := c), kloosterman_eq_zmod (c := c)]
  have hbij : Function.Bijective (fun u : ZMod c => -u) :=
    ⟨fun u v h => neg_injective h, fun u => ⟨-u,neg_neg u⟩⟩
  apply Fintype.sum_bijective (fun u : ZMod c => -u) hbij
  intro u
  by_cases hu : IsUnit u
  · have hnu : IsUnit (-u) := hu.neg
    have hi : (-u)⁻¹ = -u⁻¹ := ZMod.inv_eq_of_mul_eq_one c (-u) (-u⁻¹)
      (by simpa only [neg_mul_neg] using ZMod.mul_inv_of_unit u hu)
    simp only [if_pos hu, if_pos hnu, Int.cast_neg, hi]
    congr 1
    ring
  · have hnu : ¬IsUnit (-u) := fun h => hu (by simpa only [neg_neg] using h.neg)
    simp only [if_neg hu, if_neg hnu]

theorem kloosterman_negative_linear {c : ℕ} [NeZero c] (m n : ℤ) :
    kloosterman c (-m) n = kloosterman c m (-n) := by
  simpa only [neg_neg] using kloosterman_both_negative (c := c) m (-n)

/-- A negative original m keeps the NEGATIVE Fourier argument; the complete
sum has positive |m| and residue -a*y. This is the opposite-sign chart. -/
theorem frequency_negative {c : ℕ} [NeZero c] (M : ℝ) (a y z p : ℤ) :
    frequency M c a y z (-p) =
      (M/(c : ℝ)) • (𝓕 dyadicCutoffSchwartz) (-(M/(c : ℝ))*(p : ℝ)) *
        kloosterman c (p*inverseResidue c z) (-(a*y)) := by
  unfold frequency
  rw [show (-p)*inverseResidue c z = -(p*inverseResidue c z) by ring,
    kloosterman_negative_linear (c := c)]
  simp only [Int.cast_neg, mul_neg, neg_mul]

end
end ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly
