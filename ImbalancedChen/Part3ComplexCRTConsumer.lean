import ImbalancedChen.Part3ComplexDispersion
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq

/-!
# The actual complex W row pair becomes a constructed CRT progression

The finite CRT construction below is extracted, with names isolated, from
the fixed goldbach dependency at commit 09b97db5764ade1246bfb77206baa1b124760958:
MathlibNt/AnalyticNumberTheory/LargeSieve/LiLiuPrereqFouvryWZeroMode.lean,
theorems product_modEq_iff_of_coprime, product_congruences_compatible,
exists_product_crt_residue, productCRTResidue_spec and the finite progression
identity. That source's SHA256 is
2b1fc6b2dc6772243e09cf2af55f3d7c421543a8673eeea1e99b5c4cec980088.
Only Mathlib's finite CRT and Bezout suppliers are imported here; the
upstream module's Poisson analytic import closure is not needed.

The consumer is the actual complex medium-atom W component. All three
factor labels, their complete modulus, the beta label, complex gamma and
the common S,w remain unchanged. Inactive gamma terms vanish on the
original carrier. Incompatible product-congruence pairs vanish exactly;
compatible pairs use a constructed residue modulo the lcm, without any
pairwise-coprime-modulus hypothesis.

The final identity retains V and U from the actual primitive centre.
No caller supplies a progression/completion identity or an inverse phase.
Poisson completion, identification with the external reciprocal phase,
and every analytic distribution estimate remain separate obligations.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators
open Classical

namespace ComplexCRT

private theorem product_modEq_iff_of_coprime {q n : ℕ} (hn : n.Coprime q)
    {a b m : ℤ} (hb : Int.ModEq q (b * n) a) :
    Int.ModEq q (m * n) a ↔ Int.ModEq q m b := by
  obtain ⟨v, hv⟩ := Int.mod_coprime hn
  constructor
  · intro h
    have hm' : Int.ModEq q (m * n * v) m := by
      simpa only [mul_assoc, mul_one] using hv.mul_left m
    have hb' : Int.ModEq q (b * n * v) b := by
      simpa only [mul_assoc, mul_one] using hv.mul_left b
    exact hm'.symm.trans (((h.trans hb.symm).mul_right v).trans hb')
  · intro h
    exact (h.mul_right n).trans hb

private theorem product_congruences_compatible {q r m1 m2 : ℕ}
    (hq : 0 < q) {a n : ℤ} (ha : Int.gcd a q = 1)
    (h1 : Int.ModEq q (n * m1) a) (h2 : Int.ModEq r (n * m2) a) :
    Nat.ModEq (q.gcd r) m1 m2 := by
  have hdq : (q.gcd r : ℤ) ∣ q := by exact_mod_cast Nat.gcd_dvd_left q r
  have hdr : (q.gcd r : ℤ) ∣ r := by exact_mod_cast Nat.gcd_dvd_right q r
  have hag : Int.gcd a (q.gcd r) = 1 :=
    Nat.dvd_one.mp (ha ▸ Int.gcd_dvd_gcd_of_dvd_right a hdq)
  have hcross : Int.ModEq (q.gcd r) (a * m1) (a * m2) := by
    have hleft := (h2.of_dvd hdr).mul_right (m1 : ℤ)
    have hright := (h1.of_dvd hdq).mul_right (m2 : ℤ)
    exact hleft.symm.trans (by simpa [mul_assoc, mul_comm, mul_left_comm] using hright)
  have hgpos : (0 : ℤ) < q.gcd r := by
    exact_mod_cast Nat.gcd_pos_of_pos_left r hq
  apply Int.natCast_modEq_iff.mp
  simpa only [Int.gcd_comm (q.gcd r : ℤ) a, hag, Nat.cast_one, Int.ediv_one]
    using hcross.cancel_left_div_gcd hgpos

private theorem coprime_of_product_congruent {a : ℤ} {q n m : ℕ}
    (ha : Int.gcd a q = 1) (h : Int.ModEq q ((n : ℤ) * m) a) :
    n.Coprime q ∧ m.Coprime q := by
  have hg : Int.gcd ((n : ℤ) * m) q = 1 := by
    rw [← Int.gcd_emod ((n : ℤ) * m) q, h.eq, Int.gcd_emod, ha]
  have hnm : (n * m).Coprime q := by
    simpa [Int.gcd, Int.natAbs_mul] using hg
  exact Nat.coprime_mul_iff_left.mp hnm

def Compatible (q r m1 m2 : ℕ) : Prop :=
  m1.Coprime q ∧ m2.Coprime r ∧ Nat.ModEq (q.gcd r) m1 m2

private theorem exists_product_crt_residue {q r m1 m2 : ℕ}
    (h1 : m1.Coprime q) (h2 : m2.Coprime r)
    (hc : Nat.ModEq (q.gcd r) m1 m2) (a : ℤ) :
    ∃ b : ℤ, Int.ModEq q (b * m1) a ∧ Int.ModEq r (b * m2) a ∧
      ∀ n : ℤ, (Int.ModEq q (n * m1) a ∧ Int.ModEq r (n * m2) a) ↔
        Int.ModEq (q.lcm r) n b := by
  let t := Nat.chineseRemainder' hc
  have htq : t.val.Coprime q := by
    change t.val.gcd q = 1
    rw [t.property.1.gcd_eq, h1.gcd_eq_one]
  have htr : t.val.Coprime r := by
    change t.val.gcd r = 1
    rw [t.property.2.gcd_eq, h2.gcd_eq_one]
  obtain ⟨v, hv⟩ := Int.mod_coprime
    ((htq.mul_right htr).of_dvd_right (Nat.lcm_dvd_mul q r))
  let b : ℤ := a * v
  have hb : Int.ModEq (q.lcm r) (b * t.val) a := by
    simpa only [b, mul_assoc, mul_comm, mul_left_comm, mul_one, one_mul]
      using hv.mul_left a
  have hbq : Int.ModEq q (b * m1) a :=
    ((Int.natCast_modEq_iff.mpr t.property.1).symm.mul_left b).trans
      (hb.of_dvd (by exact_mod_cast Nat.dvd_lcm_left q r))
  have hbr : Int.ModEq r (b * m2) a :=
    ((Int.natCast_modEq_iff.mpr t.property.2).symm.mul_left b).trans
      (hb.of_dvd (by exact_mod_cast Nat.dvd_lcm_right q r))
  refine ⟨b, hbq, hbr, fun n ↦ ?_⟩
  rw [product_modEq_iff_of_coprime h1 hbq, product_modEq_iff_of_coprime h2 hbr]
  simpa only [Int.lcm, Int.natAbs_natCast] using
    (Int.modEq_and_modEq_iff_modEq_lcm (a := n) (b := b) (m := q) (n := r))

/-- This representative comes from a proved construction, not a supplied
phase or progression identity. Its incompatible value is never used. -/
def residue (q r m1 m2 : ℕ) (a : ℤ) : ℤ :=
  if h : Compatible q r m1 m2 then
    Classical.choose (exists_product_crt_residue h.1 h.2.1 h.2.2 a)
  else 0

theorem residue_spec {q r m1 m2 : ℕ} (a : ℤ) (hc : Compatible q r m1 m2) :
    Int.ModEq q (residue q r m1 m2 a * m1) a ∧
      Int.ModEq r (residue q r m1 m2 a * m2) a ∧
        ∀ n : ℤ, (Int.ModEq q (n * m1) a ∧ Int.ModEq r (n * m2) a) ↔
          Int.ModEq (q.lcm r) n (residue q r m1 m2 a) := by
  simpa only [residue, dif_pos hc] using
    Classical.choose_spec (exists_product_crt_residue hc.1 hc.2.1 hc.2.2 a)

def productProgressionWeight (S : Finset ℕ) (w : ℕ → ℝ) (a : ℤ)
    (q r m1 m2 : ℕ) : ℝ :=
  ∑ n ∈ S, if Int.ModEq q ((n : ℤ) * m1) a ∧
    Int.ModEq r ((n : ℤ) * m2) a then w n else 0

def constructedProgressionWeight (S : Finset ℕ) (w : ℕ → ℝ) (a : ℤ)
    (q r m1 m2 : ℕ) : ℝ :=
  if Compatible q r m1 m2 then
    ∑ n ∈ S, if Int.ModEq (q.lcm r) (n : ℤ) (residue q r m1 m2 a)
      then w n else 0
  else 0

/-- Noncoprime moduli use their lcm. An incompatible pair has no source
points because the original moving residue is primitive for both moduli. -/
theorem productProgressionWeight_eq_constructed (S : Finset ℕ)
    (w : ℕ → ℝ) {a : ℤ} {q r m1 m2 : ℕ}
    (hq : 0 < q) (haq : Int.gcd a q = 1) (har : Int.gcd a r = 1) :
    productProgressionWeight S w a q r m1 m2 =
      constructedProgressionWeight S w a q r m1 m2 := by
  unfold productProgressionWeight constructedProgressionWeight
  by_cases hc : Compatible q r m1 m2
  · rw [if_pos hc]
    simp_rw [(residue_spec a hc).2.2]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro n _
    apply if_neg
    intro h
    exact hc ⟨(coprime_of_product_congruent haq h.1).2,
      (coprime_of_product_congruent har h.2).2,
      product_congruences_compatible hq haq h.1 h.2⟩

end ComplexCRT

/-- The original complex coefficient on one complete modulus/beta label. -/
def MediumAtom.complexBetaCoefficient (d : MediumAtom)
    (l : (ℕ × ℕ × ℕ) × ℕ) : ℂ := d.complexFactorGamma l.1 * d.beta l.2

private theorem row_factor_mem {d : MediumAtom} {l : (ℕ × ℕ × ℕ) × ℕ}
    (hl : l ∈ d.complexRowLabels) :
    l.1.1 ∈ factorCarrier d.Q1 ∧ l.1.2.1 ∈ factorCarrier d.Q2 ∧
      l.1.2.2 ∈ factorCarrier d.Q3 := by
  have hr := (Finset.mem_product.mp hl).1
  have h1 := (Finset.mem_product.mp hr).1
  have h23 := (Finset.mem_product.mp hr).2
  exact ⟨h1, (Finset.mem_product.mp h23).1, (Finset.mem_product.mp h23).2⟩

private theorem factor_pos {Q : ℝ} (hQ : 1 ≤ Q) {q : ℕ}
    (hq : q ∈ factorCarrier Q) : 0 < q := by
  have hlo := (Finset.mem_Icc.mp hq).1
  have hceil : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
  omega

private theorem row_modulus_pos {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l : (ℕ × ℕ × ℕ) × ℕ} (hl : l ∈ d.complexRowLabels) :
    0 < complexFactorModulus l.1 := by
  obtain ⟨_, _, h1, h2, h3, _⟩ := hd
  obtain ⟨hl1, hl2, hl3⟩ := row_factor_mem hl
  exact Nat.mul_pos (Nat.mul_pos (factor_pos h1 hl1) (factor_pos h2 hl2))
    (factor_pos h3 hl3)

private theorem row_active_residue_gcd {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l : (ℕ × ℕ × ℕ) × ℕ} (hl : l ∈ d.complexRowLabels)
    (hgamma : d.complexFactorGamma l.1 ≠ 0) :
    Int.gcd d.residue (complexFactorModulus l.1) = 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩ := hd
  obtain ⟨hl1, hl2, hl3⟩ := row_factor_mem hl
  have hg : d.gamma1 l.1.1 * d.gamma2 l.1.2.1 * d.gamma3 l.1.2.2 ≠ 0 := hgamma
  obtain ⟨hg12, hg3⟩ := mul_ne_zero_iff.mp hg
  obtain ⟨hg1, hg2⟩ := mul_ne_zero_iff.mp hg12
  have hcop : (complexFactorModulus l.1).Coprime d.residue.natAbs :=
    (((h1 l.1.1 hl1).2 hg1).mul_left ((h2 l.1.2.1 hl2).2 hg2)).mul_left
      ((h3 l.1.2.2 hl3).2 hg3)
  simpa only [Int.gcd, Int.natAbs_natCast, Nat.gcd_comm] using hcop.gcd_eq_one

private theorem complexProgressionPair_sum (S : Finset ℕ) (w : ℕ → ℝ)
    (a : ℤ) (q r m1 m2 : ℕ) (c1 c2 : ℂ) :
    (∑ n ∈ S, (w n : ℂ) *
      ((c1 * (if Int.ModEq q ((n : ℤ) * m1) a then 1 else 0)) *
        star (c2 * (if Int.ModEq r ((n : ℤ) * m2) a then 1 else 0)))) =
      c1 * star c2 * (ComplexCRT.productProgressionWeight S w a q r m1 m2 : ℂ) := by
  unfold ComplexCRT.productProgressionWeight
  rw [Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hq : Int.ModEq q ((n : ℤ) * m1) a <;>
    by_cases hr : Int.ModEq r ((n : ℤ) * m2) a <;>
      simp [hq, hr]; ring

private theorem sum_common_variable_inside_pair {iota : Type*}
    (S : Finset ℕ) (L : Finset iota) (F : ℕ → iota → iota → ℂ) :
    (∑ n ∈ S, ∑ l ∈ L, ∑ l' ∈ L, F n l l') =
      ∑ l ∈ L, ∑ l' ∈ L, ∑ n ∈ S, F n l l' := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  exact Finset.sum_comm

/-- The actual W component first expands to two complete labelled
product-congruence sources, with the original complex coefficients. -/
theorem MediumAtom.complexDispersionW_eq_productProgressions (d : MediumAtom)
    (S : Finset ℕ) (w : ℕ → ℝ) :
    (d.complexDispersionW S w : ℂ) =
      ∑ l ∈ d.complexRowLabels, ∑ l' ∈ d.complexRowLabels,
        d.complexBetaCoefficient l * star (d.complexBetaCoefficient l') *
          (ComplexCRT.productProgressionWeight S w d.residue
            (complexFactorModulus l.1) (complexFactorModulus l'.1) l.2 l'.2 : ℂ) := by
  unfold MediumAtom.complexDispersionW
  rw [Complex.ofReal_sum]
  simp_rw [Complex.ofReal_mul, MediumAtom.complexProgressionRow,
    complex_norm_sq_sum_eq_double_star, Finset.mul_sum]
  rw [sum_common_variable_inside_pair]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro l' _
  calc
    _ = ∑ n ∈ S, (w n : ℂ) *
        ((d.complexBetaCoefficient l *
          (if Int.ModEq (complexFactorModulus l.1) ((n : ℤ) * l.2) d.residue
            then 1 else 0)) *
          star (d.complexBetaCoefficient l' *
            (if Int.ModEq (complexFactorModulus l'.1) ((n : ℤ) * l'.2) d.residue
              then 1 else 0))) := by
      apply Finset.sum_congr rfl
      intro n _
      have hq :
          (((n * l.2 : ℕ) : ℤ) % (complexFactorModulus l.1 : ℤ) =
            d.residue % (complexFactorModulus l.1 : ℤ)) ↔
          Int.ModEq (complexFactorModulus l.1) ((n : ℤ) * l.2) d.residue := by
        simp only [Int.ModEq, Nat.cast_mul]
      have hr :
          (((n * l'.2 : ℕ) : ℤ) % (complexFactorModulus l'.1 : ℤ) =
            d.residue % (complexFactorModulus l'.1 : ℤ)) ↔
          Int.ModEq (complexFactorModulus l'.1) ((n : ℤ) * l'.2) d.residue := by
        simp only [Int.ModEq, Nat.cast_mul]
      simp only [MediumAtom.complexBetaCoefficient, hq, hr]
    _ = _ := complexProgressionPair_sum S w d.residue (complexFactorModulus l.1)
        (complexFactorModulus l'.1) l.2 l'.2
        (d.complexBetaCoefficient l) (d.complexBetaCoefficient l')

/-- The actual active gamma gates supply primitive moving residues.
Inactive labels vanish on the original carrier; no new caller premise
asserts either CRT compatibility or a progression representation. -/
theorem MediumAtom.complexDispersionW_eq_constructedCRT
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (S : Finset ℕ) (w : ℕ → ℝ) :
    (d.complexDispersionW S w : ℂ) =
      ∑ l ∈ d.complexRowLabels, ∑ l' ∈ d.complexRowLabels,
        d.complexBetaCoefficient l * star (d.complexBetaCoefficient l') *
          (ComplexCRT.constructedProgressionWeight S w d.residue
            (complexFactorModulus l.1) (complexFactorModulus l'.1) l.2 l'.2 : ℂ) := by
  rw [MediumAtom.complexDispersionW_eq_productProgressions]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro l' hl'
  by_cases hg : d.complexFactorGamma l.1 = 0
  · simp only [MediumAtom.complexBetaCoefficient, hg, zero_mul]
  by_cases hg' : d.complexFactorGamma l'.1 = 0
  · simp only [MediumAtom.complexBetaCoefficient, hg', zero_mul, star_zero, mul_zero]
  rw [ComplexCRT.productProgressionWeight_eq_constructed S w
    (row_modulus_pos hd hl) (row_active_residue_gcd hd hl hg)
    (row_active_residue_gcd hd hl' hg')]

/-- The centered dispersion energy retains the complete V and U terms.
Only the W product-congruence piece has become a constructed progression. -/
theorem MediumAtom.complex_dispersion_identity_with_constructedCRT
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (S : Finset ℕ) (w : ℕ → ℝ) :
    ((∑ n ∈ S, w n * ‖d.complexCenteredRow n‖ ^ 2 : ℝ) : ℂ) =
      (∑ l ∈ d.complexRowLabels, ∑ l' ∈ d.complexRowLabels,
        d.complexBetaCoefficient l * star (d.complexBetaCoefficient l') *
          (ComplexCRT.constructedProgressionWeight S w d.residue
            (complexFactorModulus l.1) (complexFactorModulus l'.1) l.2 l'.2 : ℂ)) -
        2 * (d.complexDispersionV S w : ℂ) + (d.complexDispersionU S w : ℂ) := by
  rw [MediumAtom.complex_dispersion_identity]
  push_cast
  rw [MediumAtom.complexDispersionW_eq_constructedCRT hd]

end

end ImbalancedChen.Part3
