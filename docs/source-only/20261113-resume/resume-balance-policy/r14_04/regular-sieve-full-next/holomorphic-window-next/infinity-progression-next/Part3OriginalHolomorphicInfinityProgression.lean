import ImbalancedChen.Part3OriginalSameInfinityHolomorphicTrace

/-! The original level progression in the published, independently
reviewed same-infinity trace. Each native modulus appears once. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicInfinityProgression20261113
open Complex
open scoped ComplexConjugate MatrixGroups
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalHolomorphicCuspFrames20261110 (frameR)
open OriginalHolomorphicPeterssonSpace20261112 (formsBasis)
open OriginalSameInfinityHolomorphicTrace20261113 (same_infinity_petersson)
open OriginalPeterssonLipschitz20261112 (argument)
open OriginalSmoothPoissonTail (kloosterman)
open ActualGeneralJBesselSourceOnly (generalJ)

private def multiple (N : ℕ) [NeZero N] (l : ℕ) : ℕ+ :=
  ⟨N*(l+1),Nat.mul_pos (NeZero.pos N) (by omega)⟩

private theorem multiple_injective (N : ℕ) [NeZero N] : Function.Injective (multiple N) := by
  intro i j h
  have eq : N*(i+1)=N*(j+1) := congrArg (fun v : ℕ+ => (v:ℕ)) h
  have := Nat.eq_of_mul_eq_mul_left (NeZero.pos N) eq
  omega

def sameDelta (m n : ℕ) : ℂ := if m=n then 1 else 0

def infSpectrum (N j m n : ℕ) [NeZero N] : ℂ :=
  ((4*Real.pi*Real.Gamma (2*(j:ℝ)+1):ℝ):ℂ)*
    ∑ i,conj (frameR N (NeZero.pos N) (j+1) (formsBasis N (j+1) i) 1 m)*
      frameR N (NeZero.pos N) (j+1) (formsBasis N (j+1) i) 1 n

private def entry (j m n c : ℕ) : ℂ :=
  ((2*Real.pi/(c:ℝ):ℝ):ℂ)*(-I)^(2*(j+1))*kloosterman c m n*
    generalJ ((2*j+1:ℕ):ℂ) (argument (Real.sqrt m) (Real.sqrt n) c)

def progressionEntry (N j m n l : ℕ) : ℂ := entry j m n (N*(l+1))

theorem infinity_petersson_progression (N j m n : ℕ) [NeZero N] (hm : 0<m) (hn : 0<n) :
    Summable (fun l => ‖progressionEntry N j m n l‖) ∧
      infSpectrum N j m n=sameDelta m n+∑' l,progressionEntry N j m n l := by
  let geo := fun C : ℕ+ => if N∣C.val then entry j m n C.val else 0
  have H : Summable (fun C : ℕ+ => ‖geo C‖) ∧
      infSpectrum N j m n=sameDelta m n+∑' C : ℕ+,geo C :=
    same_infinity_petersson N j m n hm hn
  have inj := multiple_injective N
  have val (l : ℕ) : geo (multiple N l)=progressionEntry N j m n l := by
    change (if N∣N*(l+1) then entry j m n (N*(l+1)) else 0)=_
    exact if_pos (dvd_mul_right N (l+1))
  have support : Function.support geo⊆Set.range (multiple N) := by
    intro C h
    change geo C≠0 at h
    by_cases d : N∣C.val
    · obtain ⟨k,hk⟩ := d
      cases k with
      | zero =>
        have good := C.property
        simp [hk] at good
      | succ v => exact ⟨v,Subtype.ext hk.symm⟩
    · exact (h (by simp [geo,d])).elim
  have eq := inj.tsum_eq support
  simp only [val] at eq
  exact ⟨by simpa only [Function.comp_apply,val] using H.1.comp_injective inj,
    H.2.trans (by rw [eq])⟩

theorem progressionEntry_eq (N j m n l : ℕ) :
    progressionEntry N j m n l =
      ((2*Real.pi/(N*(l+1):ℕ):ℝ):ℂ)*(-I)^(2*(j+1))*kloosterman (N*(l+1)) m n*
        generalJ ((2*j+1:ℕ):ℂ) (argument (Real.sqrt m) (Real.sqrt n) (N*(l+1):ℕ)) := rfl

end ImbalancedChen.Part3.OriginalHolomorphicInfinityProgression20261113
end
