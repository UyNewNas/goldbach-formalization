import ImbalancedChen.Part3OriginalHolomorphicFrickePhase
import ImbalancedChen.Part3OriginalHolomorphicInfinityCumulative

/-! The full native holomorphic manuscript large sieve at each of its
two actual observing charts, with one constant and all even weights. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicBothCusps20261113
open Finset
open scoped MatrixGroups UpperHalfPlane InnerProductSpace
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalRegularPacketTest20261113 (Dyadic energy)
open OriginalRegularHolomorphicCumulative20261113 (WeightBasis weights functional shell)
open OriginalHolomorphicInfinityCumulative20261113 (manuscript_holomorphic_infinity)
open OriginalHolomorphicFrickeBasis20261113 (action frickeEquiv)
open OriginalHolomorphicFrickePhase20261113 (phase phase_norm frameR_fricke)
open OriginalHolomorphicCuspFrames20261110 (frameR)
open Gamma0ActualCuspsSourceOnly (cuspOneMatrix)
open ActualContinuousPoincarePairing20261110 (originalFrame)

private def twisted (N : ℕ) (a : ℕ → ℂ) (n : ℕ) := a n*phase N n

private theorem energy_equal (N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) :
    energy S (twisted N a)=energy S a := by simp [energy,twisted,norm_mul,phase_norm]

private theorem shell_equal (N j : ℕ) [NeZero N] (S : Finset ℕ) (a : ℕ → ℂ) (basis : WeightBasis N j) :
    shell N j true S a basis =
      shell N j false S (twisted N a) (basis.map (frickeEquiv N (j+1))) := by
  dsimp only [shell]
  apply congrArg (fun x : ℝ => Real.Gamma (2*(j:ℝ)+2)*x)
  apply sum_congr rfl
  intro i _
  have A : functional N j true S a (basis i) =
    functional N j false S (twisted N a) ((basis.map (frickeEquiv N (j+1))) i) := by
    rw [OrthonormalBasis.map_apply]
    change (∑ n∈S,a n*frameR N (NeZero.pos N) (j+1) (basis i) cuspOneMatrix n)=
      ∑ n∈S,(a n*phase N n)*frameR N (NeZero.pos N) (j+1) (action N (j+1) (basis i)) 1 n
    apply sum_congr rfl
    intro n _
    rw [frameR_fricke]
    ring
  rw [A]

/-- The common ε-dependent price precedes both cusp choices, the level,
the height and length, the finite sequence and each complete basis. -/
theorem manuscript_holomorphic_both_cusps (e : ℝ) (he : 0<e) :
    ∃ C : ℝ,0<C ∧ ∀ (N : ℕ) [NeZero N] (one : Bool) {K L : ℝ},1≤K → 1/2≤L →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ),Dyadic L S → ∀ (bases : ∀ j,WeightBasis N j),
        (∑ j∈weights K,shell N j one S a (bases j))≤
          C*(K^2+L^(1+e)/(N:ℝ))*energy S a := by
  obtain ⟨C,c0,H⟩ := manuscript_holomorphic_infinity e he
  refine ⟨C,c0,?_⟩
  intro N _ one K L hK hL S a band bases
  cases one with
  | false => exact H N hK hL S a band bases
  | true =>
    have T := H N hK hL S (twisted N a) band (fun j => (bases j).map (frickeEquiv N (j+1)))
    simpa only [←shell_equal,energy_equal] using T

end ImbalancedChen.Part3.OriginalHolomorphicBothCusps20261113
end
