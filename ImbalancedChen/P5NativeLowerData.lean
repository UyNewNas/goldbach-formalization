import ImbalancedChen.CurrentChenP5CausalRhoFactorization

/-! Existing native lower data, extracted without declaration changes.
Namespace and types are preserved; source only until compiled. -/
namespace ImbalancedChen.P5JointNativeSignedRegroup
noncomputable section
open Classical
open scoped BigOperators
open P5SelectedMaskTransport

structure LowerData where
  policy : (ℕ × ℕ) → List ℕ → Bool
  w : (ℕ × ℕ) → ℝ
  L : (ℕ × ℕ) → ℝ

def lowerRows (N : ℕ) (E : ℕ × ℕ → Prop) : Finset (ℕ × ℕ) :=
  (sixthSupport N).filter (fun t => ¬ E t)

def lowerDivisors (D : LowerData) (N : ℕ) (t : ℕ × ℕ) : Finset ℕ :=
  actualLowerSmallRoughModuli (D.policy t) N
    (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (D.w t)
    (P5CausalRhoQuotientBridge.cutoff N)

def lowerRho (D : LowerData) (N : ℕ) (t : ℕ × ℕ) (d : ℕ) : ℝ :=
  actualLowerSmallRoughRho (D.policy t) N
    (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (D.w t)
    (P5CausalRhoQuotientBridge.cutoff N) (D.L t) d

abbrev LowerMark := Σ _ : ℕ × ℕ, ℕ
def lowerMarks (D : LowerData) (N : ℕ) (E : ℕ × ℕ → Prop) : Finset LowerMark :=
  (lowerRows N E).sigma (lowerDivisors D N)
def lowerModulus (m : LowerMark) : ℕ := (m.1.1 * m.1.2) * m.2
def lowerSupport (D : LowerData) (N : ℕ) (E : ℕ × ℕ → Prop) : Finset ℕ :=
  (lowerMarks D N E).image lowerModulus
def lowerSigma (D : LowerData) (N : ℕ) (E : ℕ × ℕ → Prop) (q : ℕ) : ℝ :=
  ∑ m ∈ (lowerMarks D N E).filter (fun m => lowerModulus m = q), lowerRho D N m.1 m.2

end
end ImbalancedChen.P5JointNativeSignedRegroup
