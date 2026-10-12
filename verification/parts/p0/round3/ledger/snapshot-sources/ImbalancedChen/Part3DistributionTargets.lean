import ImbalancedChen.RestrictedResidueScale
import Mathlib.Analysis.Complex.Exponential

/-!
# Literal, deliberately unproved Part 3 distribution obligations

The frozen source is `chen-imbalanced-semiprimes` at
`ba6ec11d800eccc54406490631895e174de85766`, Proposition
`prop:current-medium` and equation `eq:current-PP`.

These definitions record obligations; none is an axiom or a theorem asserting
the missing estimate.  In particular a proof for each fixed atom with its own
constant does not prove `RestrictedMediumTarget`.  Auxiliary SW constants and
the final threshold are chosen before the members of the family.

The interval and coefficient functions belong to one atom, before any modulus
is summed.  They cannot depend on a modulus or a spectral height.  The common
completed interval and additive phase in the spectral proof are a further
missing proof obligation, not a claimed consequence of the ordinary BV API.
The latter has no nonzero additive phase parameter.

The physical integer modulus is the product `q1*q2*q3`.  The three auxiliary
factor lengths are kept separately; their ranges cannot be substituted for a
physical square-root cutoff.  Signs stay inside the one final norm.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators
open Classical

/-- One local convolution, with one interval and fixed coefficients shared
by every term of the modulus sum.  The residue may move with the atom. -/
structure MediumAtom where
  U V Q1 Q2 Q3 : ℝ
  residue : ℤ
  intervalLo intervalHi : ℝ
  alpha beta gamma1 gamma2 gamma3 : ℕ → ℂ

def MediumAtom.scale (d : MediumAtom) : ℝ := d.U * d.V

def MediumAtom.alphaCarrier (d : MediumAtom) : Finset ℕ :=
  (Finset.Icc (Nat.ceil d.U) (Nat.floor (2 * d.U))).filter
    (fun n => d.intervalLo < (n : ℝ) ∧ (n : ℝ) ≤ d.intervalHi)

def MediumAtom.betaCarrier (d : MediumAtom) : Finset ℕ :=
  Finset.Icc (Nat.ceil d.V) (Nat.floor (2 * d.V))

/-- Concrete dyadic support `Q ≤ q ≤ 2Q`, including the trivial factor
`q=1` at `Q=1`. The manuscript writes `q ≍ Q`; the compiler must assign
overlapping endpoints without multiplicity loss when it chooses its atoms. -/
def factorCarrier (Q : ℝ) : Finset ℕ :=
  Finset.Icc (Nat.ceil Q) (Nat.floor (2 * Q))

/-- The returned variable has ONE interval and ONE phase, shared by all
levels. There is deliberately no level-indexed interval or phase field. -/
structure CommonCompletedVariable where
  intervalLo intervalHi : ℕ
  additivePhase : ℝ

def CommonCompletedVariable.weight (d : CommonCompletedVariable) (m : ℕ) : ℂ :=
  if m ∈ Finset.Ico d.intervalLo d.intervalHi then
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d.additivePhase : ℂ) * (m : ℂ))
  else 0

/-- The ABL transformed coefficient has no spectral-height argument.
The coprimality of the packet level and moving residue remains required. -/
structure CoprimePacket where
  residue level multiplier : ℕ
  level_pos : 0 < level
  residue_coprime : Nat.Coprime residue level
  beta : ℕ → ℕ → ℂ

def CoprimePacket.transformedCoefficient (d : CoprimePacket) (n : ℕ) : ℂ :=
  if Nat.Coprime n d.residue then
    d.beta (d.multiplier * n) d.level *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (d.level : ℂ))
  else 0

/-- Auxiliary-coprimality SW error on the *same* alpha interval. -/
def MediumAtom.auxSWError (d : MediumAtom) (k q b : ℕ) : ℂ :=
  (∑ n ∈ d.alphaCarrier,
    if Nat.ModEq q n b ∧ Nat.Coprime n k then d.alpha n else 0) -
  (∑ n ∈ d.alphaCarrier,
    if Nat.Coprime n (k * q) then d.alpha n else 0) / (Nat.totient q : ℂ)

/-- Family constants precede the varying atom, interval, auxiliary factor,
modulus and reduced residue.  The divisor order `C0` is fixed once. -/
def UniformAuxiliarySW {ι : Type*} (F : ι → MediumAtom) (C0 : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
    ∀ i : ι, x0 ≤ (F i).scale → ∀ k q b : ℕ,
      1 ≤ k → 1 ≤ q → Nat.Coprime b q →
      ‖(F i).auxSWError k q b‖ ≤
        C * (F i).U * ((k.divisors.card : ℝ) ^ C0) /
          (Real.log (F i).scale) ^ A

/-- The literal primitive-coprime mean, without replacing it by total mass. -/
def MediumAtom.discrepancy (d : MediumAtom) (q : ℕ) : ℂ :=
  ∑ n ∈ d.alphaCarrier, ∑ m ∈ d.betaCarrier,
    d.alpha n * d.beta m *
      ((if (((n * m : ℕ) : ℤ) % (q : ℤ) = d.residue % (q : ℤ))
          then (1 : ℂ) else 0) -
        (if Nat.Coprime (n * m) q then (1 : ℂ) else 0) / (Nat.totient q : ℂ))

def MediumAtom.signedError (d : MediumAtom) : ℂ :=
  ∑ q1 ∈ factorCarrier d.Q1, ∑ q2 ∈ factorCarrier d.Q2,
    ∑ q3 ∈ factorCarrier d.Q3,
      d.gamma1 q1 * d.gamma2 q2 * d.gamma3 q3 * d.discrepancy (q1 * q2 * q3)

/-- Precisely the geometric and coefficient gates of the frozen restricted
medium proposition.  `scale` is the complete convolution product. -/
def MediumAdmissible (B : ℕ) (σ κ c0 : ℝ) (d : MediumAtom) : Prop :=
  1 ≤ d.U ∧ 1 ≤ d.V ∧ 1 ≤ d.Q1 ∧ 1 ≤ d.Q2 ∧ 1 ≤ d.Q3 ∧
  Real.exp (Real.exp 1) < d.scale ∧
  c0 * d.scale ≤ (d.residue.natAbs : ℝ) ∧
  (d.residue.natAbs : ℝ) ≤ d.scale ^ (1 + κ) ∧
  d.Q1 < d.U * d.scale ^ (-σ) ∧
  d.U ^ 2 * d.Q2 * d.Q3 ^ 2 < d.scale ^ (1 - 8 * σ) ∧
  (d.residue.natAbs : ℝ) ^ (7 / 32 : ℝ) * d.U * d.Q1 * d.Q2 ^ 5 * d.Q3 ^ 2 <
    d.scale ^ (2 - 15 * σ) ∧
  d.U ^ (1 + 2 * (7 / 32 : ℝ)) * d.Q1 *
      d.Q2 ^ (5 - 2 * (7 / 32 : ℝ)) * d.Q3 ^ (2 + 2 * (7 / 32 : ℝ)) <
    d.scale ^ (2 - 15 * σ) ∧
  (∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1) ∧
  (∀ n ∈ d.alphaCarrier, d.alpha n ≠ 0 → ∀ p : ℕ,
    Nat.Prime p → p ∣ n →
      d.scale ^ (1 / (Real.log (Real.log d.scale)) ^ 3) < (p : ℝ)) ∧
  (∀ m ∈ d.betaCarrier, ‖d.beta m‖ ≤ (m.divisors.card : ℝ) ^ B) ∧
  (∀ q ∈ factorCarrier d.Q1, ‖d.gamma1 q‖ ≤ 1 ∧
    (d.gamma1 q ≠ 0 → Nat.Coprime q d.residue.natAbs)) ∧
  (∀ q ∈ factorCarrier d.Q2, ‖d.gamma2 q‖ ≤ 1 ∧
    (d.gamma2 q ≠ 0 → Nat.Coprime q d.residue.natAbs)) ∧
  (∀ q ∈ factorCarrier d.Q3, ‖d.gamma3 q‖ ≤ 1 ∧
    (d.gamma3 q ≠ 0 → Nat.Coprime q d.residue.natAbs))

/-- Missing uniform signed medium estimate.  This proposition is not proved
by the low-rank BV or one-long integer-slot results in this Part. -/
def RestrictedMediumTarget {ι : Type*} (F : ι → MediumAtom) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
    ∀ i : ι, x0 ≤ (F i).scale →
      ‖(F i).signedError‖ ≤ C * (F i).scale / (Real.log (F i).scale) ^ A

/-- Exact unclosed theorem type, including the fixed family SW constants. -/
def RestrictedMediumObligation {ι : Type*} (F : ι → MediumAtom)
    (B C0 : ℕ) (σ κ c0 : ℝ) : Prop :=
  0 < σ → σ < 1 / 100 → 0 < c0 → 0 ≤ κ → κ ≤ σ / 100 →
  (∀ i : ι, MediumAdmissible B σ κ c0 (F i)) →
  UniformAuxiliarySW F C0 → RestrictedMediumTarget F

/-- Labelled prime tuples, retaining repeated primes and their slot order. -/
def labelledPrimeTuples (k P : ℕ) : Finset (Fin k → Fin (P + 1)) :=
  Finset.univ.filter (fun t => ∀ i : Fin k, Nat.Prime (t i).val)

def labelledProduct {k P : ℕ} (t : Fin k → Fin (P + 1)) : ℕ :=
  ∏ i : Fin k, (t i).val

/-- The exact `eq:current-PP` error for a finite labelled source.  Geometric
licensing is not asserted for arbitrary `W`.  There is no additive-prime
filter hidden in its source; that filter is recovered by the physical sieve. -/
def primeProductSignedError (k P N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W : (Fin k → Fin (P + 1)) → ℝ) : ℝ :=
  ∑ q ∈ Q, rho q *
    (∑ t ∈ labelledPrimeTuples k P, W t *
      ((if Nat.ModEq q (labelledProduct t) N then (1 : ℝ) else 0) -
        (if Nat.Coprime (labelledProduct t) q then (1 : ℝ) else 0) /
          (Nat.totient q : ℝ)))

/-- The raw conclusion of the missing actual upper/lower source supplier.
This is NOT a claim that arbitrary `W` is a licensed geometric family.
A concrete caller fixes its
policy, prime rank and licensed geometric family before invoking this type.
One threshold covers every family member at each target. -/
def UniformPrimeProductTarget {ι : Type*} (k : ℕ) (cap : ℕ → ℕ)
    (Q : ℕ → Finset ℕ) (rho : ℕ → ℕ → ℝ)
    (W : (N : ℕ) → ι → (Fin k → Fin (cap N + 1)) → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N → Even N → ∀ i : ι,
      |primeProductSignedError k (cap N) N (Q N) (rho N) (W N i)| ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ A

end

end ImbalancedChen.Part3
