import ImbalancedChen.Part3ActualMarkedBruhatTest
import ImbalancedChen.Part3OriginalCuspidalPoincareTrace
import Batteries.Tactic.OpenPrivate

/-! Complete positive-modulus arithmetic series of the signed, scaled
spatial packets, before any estimates on their spectral coordinates. -/
namespace ImbalancedChen.Part3.ActualMarkedGeometricSeries20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators MatrixGroups UpperHalfPlane
open ActualCuspOneGeometricPairing20261112 ActualMarkedBruhatTest20261112
open ActualContinuousPoincarePairing20261110 OriginalContinuousPoincarePackets20261110
open OriginalNonzeroCuspOneSource20261102 OriginalSignedTraceInput20261102
open Gamma0QuotientCellPushforward20261025a OriginalCuspidalPoincareTrace20261110
open private seed_memLp from ImbalancedChen.Part3OriginalCuspidalPoincareTrace

/-- The generalized Kloosterman sum is evaluated at the actual class
modulus; its scalar denominator is d sqrt(N), also in the Bessel argument. -/
def geometricTerm (N p : ℕ) (n : ℤ) (ψ φ : ℝ → ℂ) (d : ℕ+) : ℂ :=
  if hd : N.Coprime (d : ℕ) then
    cuspOneMatrixSum N d hd (p : ℤ) n/(traceModulus N d : ℂ) *
      orbitTest n.sign ψ φ (4*Real.pi*Real.sqrt ((p : ℝ)*(n.natAbs : ℝ))/traceModulus N d)
  else 0

private theorem normalized_term (N : ℕ) [NeZero N] {p : ℕ} (hp : 0<p) {n : ℤ} (hn : n≠0)
    (ψ φ : ℝ → ℂ) :
    sourceOrbit N (p : ℤ) n (scaledSeed (p : ℤ) ψ) (scaledSeed n φ)=geometricTerm N p n ψ φ := by
  funext d
  rw [sourceOrbit,orbit_integral N d p hp n hn ψ φ,geometricTerm]
  by_cases hd : N.Coprime (d : ℕ)
  · simp only [dif_pos hd]
    ring
  · simp only [dif_neg hd,zero_mul]

def pairDiagonal (N p : ℕ) (n : ℤ) (ψ φ : ℝ → ℂ) : ℂ :=
  sourceDiagonal N (p : ℤ) n (scaledSeed (p : ℤ) ψ) (scaledSeed n φ)

theorem normalized_pair (N : ℕ) [NeZero N] {p : ℕ} (hp : 0<p) {n : ℤ} (hn : n≠0)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hpψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Summable (geometricTerm N p n ψ φ) ∧
      (∫ q,star (originalPoincare N true n (scaledSeed n φ) q)*
        originalPoincare N false (p : ℤ) (scaledSeed (p : ℤ) ψ) q ∂carrierPushforward N) =
        pairDiagonal N p n ψ φ + ∑' d : ℕ+,geometricTerm N p n ψ φ d := by
  obtain ⟨h₁,h₂,h₃⟩ := scaled_test (p : ℤ) (by exact_mod_cast hp.ne') ψ hψ hcψ hpψ
  obtain ⟨h₄,h₅,h₆⟩ := scaled_test n hn φ hφ hcφ hpφ
  simpa only [normalized_term N hp hn ψ φ,pairDiagonal] using
    signed_geometric_pair N (p : ℤ) n _ _ h₁ h₂ h₃ h₄ h₅ h₆

/-- Original marking convention: w is the unconjugated common positive
frequency coefficient and b the signed cusp-one coefficient. -/
theorem marked_pair (N : ℕ) [NeZero N] (S T : Finset ℕ) (w b : ℕ → ℂ) (ind : ℕ → ℤ)
    (hS : ∀ p ∈ S,0<p) (hT : ∀ n ∈ T,ind n≠0)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hpψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    (∫ q,star (packet N true T b ind φ q)*
      packet N false S (fun p => star (w p)) (fun p => (p : ℤ)) ψ q ∂carrierPushforward N) =
      ∑ n ∈ T,∑ p ∈ S,w p*b n*
        (pairDiagonal N p (ind n) ψ φ+∑' d : ℕ+,geometricTerm N p (ind n) ψ φ d) := by
  let X := fun p : ℕ => originalPoincare N false (p : ℤ) (scaledSeed (p : ℤ) ψ)
  let Y := fun n : ℕ => originalPoincare N true (ind n) (scaledSeed (ind n) φ)
  have hX (p : ℕ) (hp : p∈S) : MemLp (X p) 2 (carrierPushforward N) := by
    obtain ⟨a,c,e⟩ := scaled_test (p : ℤ) (by exact_mod_cast (hS p hp).ne') ψ hψ hcψ hpψ
    exact seed_memLp N false (p : ℤ) _ a c e
  have hY (n : ℕ) (hn : n∈T) : MemLp (Y n) 2 (carrierPushforward N) := by
    obtain ⟨a,c,e⟩ := scaled_test (ind n) (hT n hn) φ hφ hcφ hpφ
    exact seed_memLp N true (ind n) _ a c e
  let Q := fun n p q => w p*b n*(star (Y n q)*X p q)
  have hQ (n : ℕ) (hn : n∈T) (p : ℕ) (hp : p∈S) : Integrable (Q n p) (carrierPushforward N) :=
    ((hY n hn).star.integrable_mul (hX p hp)).const_mul _
  have E (q : Gamma0OrbitSpace N) :
      star (packet N true T b ind φ q)*packet N false S (fun p => star (w p)) (fun p => (p : ℤ)) ψ q =
        ∑ n ∈ T,∑ p ∈ S,Q n p q := by
    simp only [packet,star_sum,star_mul',star_star,Finset.sum_mul,Finset.mul_sum,Q,X,Y]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro p _
    ring
  simp_rw [E]
  rw [integral_finsetSum T (fun n hn => integrable_finsetSum S (hQ n hn))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [integral_finsetSum S (hQ n hn)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [show Q n p=(fun q => w p*b n*(star (Y n q)*X p q)) from rfl,integral_const_mul]
  exact congrArg (fun z => w p*b n*z) (normalized_pair N (hS p hp) (hT n hn) ψ φ hψ hcψ hpψ hφ hcφ hpφ).2

end
end ImbalancedChen.Part3.ActualMarkedGeometricSeries20261112
