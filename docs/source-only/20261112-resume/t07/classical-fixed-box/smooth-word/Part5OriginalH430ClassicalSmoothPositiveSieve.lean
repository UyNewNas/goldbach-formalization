import ImbalancedChen.Part5OriginalH430ClassicalSmoothFamilyLicence
import ImbalancedChen.P5zFiniteFallbackPositiveOuter

/-! Apply the actual finite fallback upper policy to every labelled
occurrence of the new smooth family. The modulus Q, coefficient rho and
target N are common throughout the exact signed sum. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothPositiveSieve
noncomputable section
open Finset Real Wu2008DoubleSieve
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFiniteFallbackPolicy (rho)
open Part5OriginalH430ClassicalSmallSwitchedIntegers (testWeight)
open Part5OriginalH430ClassicalSeedIntegralCap (wordsSum words_mono words_add words_mul)
open Part5OriginalH430ClassicalSmoothRankCoordinates (rank)
open Part5OriginalH430ClassicalSmoothRankSupport (W W_bounds)
open Part5OriginalH430ClassicalSmoothRankAccounting (smoothRank tails)
open Part5OriginalH430ClassicalSmoothMarkedFamily (smoothCount)
open scoped Classical BigOperators

def signedPart (N : ℕ) (ν δ h c : ℝ) (Q : Finset ℕ) (ρ : ℕ → ℝ) (cs : List ℕ) (r : ℕ) :=
  Part3.primeProductSignedError (rank cs.length r) (2*N) N Q ρ (fun t => W cs t ν δ h c)
def coprimePart (N : ℕ) (ν δ h c : ℝ) (Q : Finset ℕ) (ρ : ℕ → ℝ) (cs : List ℕ) (r : ℕ) :=
  p5z_labelledCoprimeCorrection (Part3.labelledPrimeTuples (rank cs.length r) (2*N))
    Part3.labelledProduct (fun t => W cs t ν δ h c) Q ρ
def smallPart (N : ℕ) (ν δ h c : ℝ) (z : ℕ) (cs : List ℕ) (r : ℕ) :=
  p5z_labelledSmallPrimeMass (Part3.labelledPrimeTuples (rank cs.length r) (2*N))
    Part3.labelledProduct (fun t => W cs t ν δ h c) N z

def whole (F : List ℕ → ℕ → ℝ) := wordsSum (fun cs => ∑ r∈tails cs.length,F cs r)

theorem physical_positive_upper (B : Bank) (round n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ)
    (N : ℕ) (τ L ν δ h c : ℝ) (hL : 1<L) (hwL : (N:ℝ)^ω≤L)
    (hwz : (N:ℝ)^ω≤cutoff N) (hz : cutoff N≤(N:ℝ)) :
    let Q := moduli N ((N:ℝ)^ω)
    let ρ := rho B round n e q a ω N τ L
    smoothCount true N ν δ h c≤smoothCount false N ν δ h c*physicalDensitySum Q ρ+
      whole (coprimePart N ν δ h c Q ρ)+whole (signedPart N ν δ h c Q ρ)+
      whole (smallPart N ν δ h c (Nat.ceil (cutoff N))) := by
  let Q := moduli N ((N:ℝ)^ω)
  let ρ := rho B round n e q a ω N τ L
  let D := physicalDensitySum Q ρ
  let F := fun cs r => smoothRank false N ν δ h c cs r
  let C := coprimePart N ν δ h c Q ρ
  let E := signedPart N ν δ h c Q ρ
  let H := smallPart N ν δ h c (Nat.ceil (cutoff N))
  have hrow (cs : List ℕ) (r : ℕ) : smoothRank true N ν δ h c cs r≤
      D*F cs r+C cs r+E cs r+H cs r := by
    let k := rank cs.length r
    let S := Part3.labelledPrimeTuples k (2*N)
    let w := fun t : Fin k → Fin (2*N+1) => W cs t ν δ h c
    have hP : smoothRank true N ν δ h c cs r=p5z_labelledPrimeMass S Part3.labelledProduct w N := by
      apply sum_congr rfl
      intro t _
      change w t*testWeight true N 1 (Part3.labelledProduct t)=_
      simp only [testWeight,if_true,one_mul] <;> split_ifs <;> simp
    have hM : smoothRank false N ν δ h c cs r=p5z_labelledMass S w := by
      simp [smoothRank,testWeight,p5z_labelledMass,S,w,k]
    have hU := P5zFiniteFallbackPositiveOuter.fullPrimeTupleMass_le B round n e q a ω N τ L hL hwL hwz hz
      k (2*N) w (fun t _ => (W_bounds cs t ν δ h c).1)
    change p5z_labelledPrimeMass S Part3.labelledProduct w N≤p5z_labelledMass S w*D+
      C cs r+E cs r+H cs r at hU
    rw [←hP,←hM] at hU
    simpa only [F,mul_comm D] using hU
  have hTotal := words_mono (F:=fun cs => ∑ r∈tails cs.length,smoothRank true N ν δ h c cs r)
    (G:=fun cs => D*(∑ r∈tails cs.length,F cs r)+(∑ r∈tails cs.length,C cs r)+
      (∑ r∈tails cs.length,E cs r)+(∑ r∈tails cs.length,H cs r)) (by
      intro _ cs _
      simpa only [sum_add_distrib,←mul_sum] using sum_le_sum (s:=tails cs.length) (fun r _ => hrow cs r))
  rw [words_add,words_add,words_add,words_mul] at hTotal
  simpa only [smoothCount,whole,F,C,E,H,D,Q,ρ,mul_comm (physicalDensitySum _ _)] using hTotal

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothPositiveSieve

