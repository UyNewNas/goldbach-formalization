import ImbalancedChen.Part3MediumActualS3ZeroCentering
import Mathlib.Tactic

/-! Source only; uncompiled; zero formal credit.
Explicit genuine diagonal/gcd/close-pair zero-mode budgets and finite
alpha-pair counts. These finite payments are NOT relabelled as the full
arbitrary-logarithmic deletion estimates; shifted Shiu/gcd averaging and
outer weighted aggregation remain necessary.
-/
namespace ImbalancedChen.Part3.MediumActualDeletionBudgets20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3.MediumActualS3ZeroCentering20261028
open ImbalancedChen.Part3.MediumGenuinePoissonFibre20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.OriginalGevreyFinalPsi20261028
open ImbalancedChen.Part3.OriginalPaperPsiCoprimeCount

def zeroAbsoluteKernel (atom : MediumAtom) (receiver y : ℝ) (k : Key)
    (v : FibreIndex) : ℝ :=
  paperQWeight atom v.1.1 * ‖lambdaTrim atom receiver y k v.1.2 v.2.1.1‖ *
    ‖lambdaTrim atom receiver y k v.1.2 v.2.2.1‖ *
    ‖atom.alpha v.2.1.2‖ * ‖atom.alpha v.2.2.2‖ *
    (atom.V * paperMass / (completeL v : ℝ))

/-- Actual physical inverse-lcm payment; no x^epsilon divisor envelope
is inserted and no compatible/primitive gate is invented. -/
theorem norm_genuine_zero_le_kernel {atom : MediumAtom} {k : Key}
    (hQ : 0 < atom.Q1) (hV : 0 < atom.V) (receiver y : ℝ)
    {v : FibreIndex} (hv : v ∈ fibreCarrier atom k) :
    ‖headCoefficient atom receiver y k v * zeroMode atom v‖ ≤
      zeroAbsoluteKernel atom receiver y k v := by
  have hL : (0 : ℝ) < completeL v := by exact_mod_cast (fibre_moduli_positive hQ hv).2.2
  have hmass := paperMass_nonneg
  have hpsi : 0 ≤ paperQWeight atom v.1.1 := paperPsi_nonneg _
  have hk0 : 0 ≤ zeroAbsoluteKernel atom receiver y k v := by
    unfold zeroAbsoluteKernel
    positivity
  unfold zeroMode
  by_cases hc : compatible v
  · rw [if_pos hc, norm_mul, paperPsi_fourier_zero]
    unfold headCoefficient zeroAbsoluteKernel
    simp only [norm_mul, norm_star, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hpsi, abs_of_pos (div_pos hV hL), abs_of_nonneg hmass]
    ring_nf <;> exact le_rfl
  · simpa [hc] using hk0

def gcdBad (v : FibreIndex) : Prop :=
  ¬v.2.1.1.Coprime v.2.2.1 ∨ ¬v.2.1.2.Coprime v.2.2.2 ∨
    ¬v.2.2.1.Coprime (v.1.1 * v.1.2)

def closePair (T : ℝ) (v : FibreIndex) : Prop :=
  |(v.2.1.2 : ℝ) - v.2.2.2| < T

def gcdBadZero (atom : MediumAtom) (receiver y : ℝ) (k : Key) : ℂ :=
  ∑ v ∈ fibreCarrier atom k, if gcdBad v then
    headCoefficient atom receiver y k v * zeroMode atom v else 0

def gcdBadBudget (atom : MediumAtom) (receiver y : ℝ) (k : Key) : ℝ :=
  ∑ v ∈ fibreCarrier atom k, if gcdBad v then zeroAbsoluteKernel atom receiver y k v else 0

def closeZero (atom : MediumAtom) (receiver y : ℝ) (k : Key) (T : ℝ) : ℂ :=
  ∑ v ∈ fibreCarrier atom k, if closePair T v then
    headCoefficient atom receiver y k v * zeroMode atom v else 0

def closeBudget (atom : MediumAtom) (receiver y : ℝ) (k : Key) (T : ℝ) : ℝ :=
  ∑ v ∈ fibreCarrier atom k, if closePair T v then zeroAbsoluteKernel atom receiver y k v else 0

def diagonalBudget (atom : MediumAtom) (receiver y : ℝ) (k : Key) : ℝ :=
  ∑ v ∈ fibreCarrier atom k, if v.2.1.2 = v.2.2.2 then
    zeroAbsoluteKernel atom receiver y k v else 0

theorem norm_genuineDiagonalZero_le_budget (atom : MediumAtom) (receiver y : ℝ)
    (k : Key) (hQ : 0 < atom.Q1) (hV : 0 < atom.V) :
    ‖genuineDiagonalZero atom receiver y k‖ ≤ diagonalBudget atom receiver y k := by
  unfold genuineDiagonalZero diagonalBudget
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro v hv
  by_cases h : v.2.1.2 = v.2.2.2
  · simpa [h] using norm_genuine_zero_le_kernel hQ hV receiver y hv
  · simp [h]

theorem norm_gcdBadZero_le_budget (atom : MediumAtom) (receiver y : ℝ)
    (k : Key) (hQ : 0 < atom.Q1) (hV : 0 < atom.V) :
    ‖gcdBadZero atom receiver y k‖ ≤ gcdBadBudget atom receiver y k := by
  unfold gcdBadZero gcdBadBudget
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro v hv
  by_cases h : gcdBad v
  · simpa [h] using norm_genuine_zero_le_kernel hQ hV receiver y hv
  · simp [h]

theorem norm_closeZero_le_budget (atom : MediumAtom) (receiver y : ℝ)
    (k : Key) (T : ℝ) (hQ : 0 < atom.Q1) (hV : 0 < atom.V) :
    ‖closeZero atom receiver y k T‖ ≤ closeBudget atom receiver y k T := by
  unfold closeZero closeBudget
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro v hv
  by_cases h : closePair T v
  · simpa [h] using norm_genuine_zero_le_kernel hQ hV receiver y hv
  · simp [h]

def closeAlphaPairs (atom : MediumAtom) (T : ℝ) : Finset (ℕ × ℕ) :=
  (atom.alphaCarrier ×ˢ atom.alphaCarrier).filter
    (fun p => |(p.1 : ℝ) - p.2| < T)

/-- Finite close-pair occupancy of the ACTUAL alpha carrier. The offset
encoding is injective even at 0; no signed difference is truncated away. -/
theorem closeAlphaPairs_card_le (atom : MediumAtom) (T : ℝ) :
    (closeAlphaPairs atom T).card ≤ atom.alphaCarrier.card * (2 * Nat.ceil T + 1) := by
  let K := Nat.ceil T
  let enc (p : ℕ × ℕ) : ℕ × ℕ := (p.1, p.2 + K - p.1)
  have hb {p : ℕ × ℕ} (hp : p ∈ closeAlphaPairs atom T) :
      p.1 ≤ p.2 + K ∧ p.2 ≤ p.1 + K := by
    have habs := (mem_filter.mp hp).2
    have hK : T ≤ (K : ℝ) := Nat.le_ceil T
    have h1 := le_abs_self ((p.1 : ℝ) - p.2)
    have h2 := neg_le_abs ((p.1 : ℝ) - p.2)
    constructor
    · exact_mod_cast (show (p.1 : ℝ) ≤ (p.2 : ℝ) + K by linarith)
    · exact_mod_cast (show (p.2 : ℝ) ≤ (p.1 : ℝ) + K by linarith)
  have hi : Set.InjOn enc (closeAlphaPairs atom T) := by
    intro p hp p' hp' heq
    have hfirst := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    dsimp [enc] at hfirst hsecond
    apply Prod.ext hfirst
    have hbp := hb hp
    have hbp' := hb hp'
    omega
  have hs : (closeAlphaPairs atom T).image enc ⊆ atom.alphaCarrier ×ˢ range (2*K+1) := by
    intro t ht
    obtain ⟨p,hp,rfl⟩ := mem_image.mp ht
    have hbp := hb hp
    apply mem_product.mpr
    refine ⟨(mem_product.mp (mem_filter.mp hp).1).1, mem_range.mpr ?_⟩
    dsimp [enc]
    omega
  calc
    _ = ((closeAlphaPairs atom T).image enc).card := (card_image_iff.mpr hi).symm
    _ ≤ (atom.alphaCarrier ×ˢ range (2*K+1)).card := card_le_card hs
    _ = _ := by simp [K]

def diagonalAlphaPairs (atom : MediumAtom) : Finset (ℕ × ℕ) :=
  (atom.alphaCarrier ×ˢ atom.alphaCarrier).filter (fun p => p.1 = p.2)

theorem diagonalAlphaPairs_card (atom : MediumAtom) :
    (diagonalAlphaPairs atom).card = atom.alphaCarrier.card := by
  have hs : diagonalAlphaPairs atom = atom.alphaCarrier.image (fun n => (n,n)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hmem,heq⟩ := mem_filter.mp hp
      exact mem_image.mpr ⟨p.1,(mem_product.mp hmem).1, by simp [heq]⟩
    · intro hp
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hp
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hn,hn⟩,rfl⟩
  have hi : Function.Injective (fun n : ℕ => (n,n)) := by
    intro n m h
    exact congrArg Prod.fst h
  rw [hs, card_image_of_injective _ hi]

end
end ImbalancedChen.Part3.MediumActualDeletionBudgets20261028
