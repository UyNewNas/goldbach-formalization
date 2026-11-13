import ImbalancedChen.Part3OriginalHolomorphicInfinityProgression
import ImbalancedChen.Part3OriginalRegularHolomorphicCumulative
import ImbalancedChen.Part3OriginalHolomorphicHeightModulusFubini

/-! Finite arbitrary-coefficient Gram of the original same-infinity
Petersson equality, with the full basis in its native Hilbert space. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicInfinityGram20261113
open Finset Complex UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane InnerProductSpace ComplexConjugate
open OriginalPeterssonPretrace20261112 OriginalHolomorphicPeterssonSpace20261112
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalHolomorphicCuspFrames20261110
open OriginalRegularHolomorphicCumulative20261113 (WeightBasis)
open OriginalHolomorphicInfinityProgression20261113 (infSpectrum sameDelta progressionEntry infinity_petersson_progression)
open OriginalAllParameterKloosterman20261113 (dyadEnergy)

def packet (M : ℕ) (a : ℕ → ℂ) (F : ℕ → ℕ → ℂ) : ℂ :=
  ∑ i∈range (M+1),∑ k∈range (M+1),conj (a (M+i))*a (M+k)*F (M+i) (M+k)

def linearPacket (M : ℕ) (a v : ℕ → ℂ) : ℂ := ∑ i∈range (M+1),a (M+i)*v (M+i)

def naturalShell (z M j : ℕ) [NeZero z] (a : ℕ → ℂ) (bases : WeightBasis z j) : ℝ :=
  Real.Gamma (2*(j:ℝ)+2)*∑ i,‖linearPacket M a
    (frameR z (NeZero.pos z) (j+1) (bases i) 1)‖^2

theorem shell_nonnegative (z M j : ℕ) [NeZero z] (a : ℕ → ℂ) (basis : WeightBasis z j) :
    0≤naturalShell z M j a basis :=
  mul_nonneg (Real.Gamma_pos_of_pos (by positivity)).le (sum_nonneg fun _ _ => sq_nonneg _)

private theorem norm_packet (M : ℕ) (a v : ℕ → ℂ) :
    ((‖linearPacket M a v‖^2:ℝ):ℂ)=packet M a (fun m n => conj (v m)*v n) := by
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self,linearPacket,map_sum,sum_mul]
  apply sum_congr rfl
  intro i _
  rw [map_mul,mul_sum]
  exact sum_congr rfl (fun k _ => by ring)

private theorem packet_const (M : ℕ) (a : ℕ → ℂ) (w : ℂ) (F : ℕ → ℕ → ℂ) :
    packet M a (fun m n => w*F m n)=w*packet M a F := by
  simp only [packet,mul_sum]
  exact sum_congr rfl (fun i _ => sum_congr rfl (fun k _ => by ring))

private theorem packet_sum {ι : Type*} [Fintype ι] (M : ℕ) (a : ℕ → ℂ) (F : ι → ℕ → ℕ → ℂ) :
    packet M a (fun m n => ∑ i,F i m n)=∑ i,packet M a (F i) := by
  simp only [packet,mul_sum]
  calc
    _ = ∑ i∈range (M+1),∑ b,∑ k∈range (M+1),
        conj (a (M+i))*a (M+k)*F b (M+i) (M+k) :=
      sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem packet_diagonal (M : ℕ) (a : ℕ → ℂ) :
    packet M a sameDelta=(dyadEnergy M a:ℂ) := by
  simp only [packet,dyadEnergy,Complex.ofReal_sum]
  apply sum_congr rfl
  intro i hi
  have point (k : ℕ) :
      conj (a (M+i))*a (M+k)*sameDelta (M+i) (M+k) =
        if k=i then ((‖a (M+i)‖^2:ℝ):ℂ) else 0 := by
    by_cases p : k=i
    · subst k
      simp only [sameDelta,if_true,mul_one,←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    · simp [sameDelta,p,Ne.symm p]
  simp [point,hi]

private theorem basis_gram (z j : ℕ) [NeZero z] (basis : WeightBasis z j) (m n : ℕ) :
    ∑ i,conj (frameR z (NeZero.pos z) (j+1) (basis i) 1 m)*
      frameR z (NeZero.pos z) (j+1) (basis i) 1 n =
        inner ℂ (Rvector z (j+1) 1 n) (Rvector z (j+1) 1 m) := by
  rw [←basis.sum_inner_mul_inner]
  apply sum_congr rfl
  intro i _
  rw [←Rvector_evaluates z (j+1) 1 m,←Rvector_evaluates z (j+1) 1 n,inner_conj_symm]
  ring

theorem packet_spectrum (z M j : ℕ) [NeZero z] (a : ℕ → ℂ) (basis : WeightBasis z j) :
    packet M a (infSpectrum z j) =
      ((4*Real.pi*Real.Gamma (2*(j:ℝ)+1):ℝ):ℂ) *
        (∑ i,((‖linearPacket M a (frameR z (NeZero.pos z) (j+1) (basis i) 1)‖^2:ℝ):ℂ)) := by
  let R := fun i => frameR z (NeZero.pos z) (j+1) (basis i) 1
  have K (m n : ℕ) : infSpectrum z j m n=
      ((4*Real.pi*Real.Gamma (2*(j:ℝ)+1):ℝ):ℂ)*(∑ i,conj (R i m)*R i n) := by
    rw [infSpectrum,full_basis_product,←basis_gram z j basis m n] <;> rfl
  rw [show infSpectrum z j=fun m n =>
    ((4*Real.pi*Real.Gamma (2*(j:ℝ)+1):ℝ):ℂ)*(∑ i,conj (R i m)*R i n)
    from funext (fun m => funext (K m)),packet_const,packet_sum]
  simp only [←norm_packet,R]

theorem packed_trace {z M : ℕ} [NeZero z] (hM : 0<M) (j : ℕ) (a : ℕ → ℂ) :
    HasSum (fun l => packet M a (fun m n => progressionEntry z j m n l))
      (packet M a (infSpectrum z j)-(dyadEnergy M a:ℂ)) := by
  have each (m n : ℕ) (hm : 0<m) (hn : 0<n) :
      HasSum (progressionEntry z j m n) (infSpectrum z j m n-sameDelta m n) := by
    obtain ⟨S,E⟩ := infinity_petersson_progression z j m n hm hn
    rw [E,add_sub_cancel_left]
    exact S.of_norm.hasSum
  have all := hasSum_sum (s:=range (M+1)) fun i _ => hasSum_sum (s:=range (M+1)) fun k _ =>
    (each (M+i) (M+k) (by omega) (by omega)).mul_left (conj (a (M+i))*a (M+k))
  have difference : packet M a (fun m n => infSpectrum z j m n-sameDelta m n) =
      packet M a (infSpectrum z j)-(dyadEnergy M a:ℂ) := by
    rw [←packet_diagonal]
    simp only [packet,mul_sub,sum_sub_distrib]
  exact difference ▸ all

end ImbalancedChen.Part3.OriginalHolomorphicInfinityGram20261113
end
