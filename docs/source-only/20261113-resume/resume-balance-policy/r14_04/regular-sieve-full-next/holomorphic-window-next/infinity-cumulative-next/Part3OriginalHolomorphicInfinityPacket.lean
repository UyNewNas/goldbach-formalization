import ImbalancedChen.Part3OriginalHolomorphicInfinityWeighted

/-! The real manuscript length and its arbitrary finite complex
coefficient sequence inside the original natural Bessel dyad. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicInfinityPacket20261113
open Finset
open OriginalRegularPacketTest20261113 (Dyadic energy)
open OriginalRegularHolomorphicCumulative20261113 (functional shell WeightBasis)
open OriginalHolomorphicInfinityGram20261113 (linearPacket naturalShell)
open OriginalAllParameterKloosterman20261113 (dyadEnergy)
open ActualContinuousPoincarePairing20261110 (originalFrame)

def start (L : ℝ) : ℕ := ⌊L⌋₊+1

def extension (S : Finset ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ := if n∈S then a n else 0

private theorem contains {L : ℝ} (hL : 1/2≤L) (S : Finset ℕ) (bd : Dyadic L S) :
    S⊆(range (start L+1)).image (fun i => start L+i) := by
  intro n hn
  have lp : 0≤L := by linarith
  obtain ⟨l,u⟩ := bd n hn
  have low : start L≤n := (Nat.floor_lt lp).mpr l
  have A := Nat.lt_floor_add_one L
  have high : n≤2*start L := by
    change n≤2*(⌊L⌋₊+1)
    exact_mod_cast (show (n:ℝ)≤2*((⌊L⌋₊:ℝ)+1) by linarith only [A,u])
  refine mem_image.mpr ⟨n-start L,mem_range.mpr (by omega),?_⟩
  omega

private theorem extend_sum {R : Type*} [AddCommMonoid R] {L : ℝ} (hL : 1/2≤L)
    (S : Finset ℕ) (bd : Dyadic L S) (f : ℕ → R) :
    (∑ i∈range (start L+1),if start L+i∈S then f (start L+i) else 0)=∑ n∈S,f n := by
  let T := (range (start L+1)).image (fun i => start L+i)
  let F := fun n => if n∈S then f n else 0
  have inj : Set.InjOn (fun i => start L+i) ↑(range (start L+1)) :=
    fun _ _ _ _ h => Nat.add_left_cancel h
  calc
    _ = ∑ n∈T,F n := (sum_image inj).symm
    _ = ∑ n∈S,F n := (sum_subset (contains hL S bd) (fun n _ hn => if_neg hn)).symm
    _ = _ := sum_congr rfl (fun n hn => if_pos hn)

theorem extension_energy {L : ℝ} (hL : 1/2≤L) (S : Finset ℕ) (bd : Dyadic L S) (a : ℕ → ℂ) :
    dyadEnergy (start L) (extension S a)=energy S a := by
  have eq (n : ℕ) : ‖extension S a n‖^2=if n∈S then ‖a n‖^2 else 0 := by
    by_cases hn : n∈S <;> simp [extension,hn]
  simp only [dyadEnergy,energy,eq]
  exact extend_sum hL S bd (fun n => ‖a n‖^2)

theorem extension_shell (z j : ℕ) [NeZero z] {L : ℝ} (hL : 1/2≤L)
    (S : Finset ℕ) (bd : Dyadic L S) (a : ℕ → ℂ) (basis : WeightBasis z j) :
    naturalShell z (start L) j (extension S a) basis=shell z j false S a basis := by
  have E (v : ℕ → ℂ) : linearPacket (start L) (extension S a) v=∑ n∈S,a n*v n := by
    have eq (n : ℕ) : extension S a n*v n=if n∈S then a n*v n else 0 := by
      by_cases hn : n∈S <;> simp [extension,hn]
    simp only [linearPacket,eq]
    exact extend_sum hL S bd (fun n => a n*v n)
  simpa [naturalShell,shell,functional,E,originalFrame]

theorem start_rpow {e L : ℝ} (he : 0<e) (hL : 1/2≤L) :
    (start L:ℝ)^(1+e)≤(3:ℝ)^(1+e)*L^(1+e) := by
  have lp : 0≤L := by linarith
  have bound : (start L:ℝ)≤3*L := by
    dsimp only [start]
    rw [Nat.cast_add,Nat.cast_one]
    linarith only [Nat.floor_le lp,hL]
  exact (Real.rpow_le_rpow (Nat.cast_nonneg _) bound (by linarith only [he])).trans_eq
    (Real.mul_rpow (by norm_num) lp)

end ImbalancedChen.Part3.OriginalHolomorphicInfinityPacket20261113
end
