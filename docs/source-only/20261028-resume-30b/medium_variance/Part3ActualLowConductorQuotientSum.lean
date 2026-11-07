import ImbalancedChen.Part3ActualFilteredPrimitiveSW
import ImbalancedChen.Part3SharedFirstFactorHighConductor
import ImbalancedChen.Part3TransposedPrimitiveUMoment
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original distribution-medium-completion-20261010.txt, (14), low conductors.

The actual full-level character coefficient is grouped by its conductor f
and quotient k=ell/f. The auxiliary cost remains tau(r*k); f and k need
not be coprime. Finite conductor fibres are bounded by the genuine number
phi(f) of full characters at level f. The physical 1/phi(ell) then leaves
1/phi(k). A fixed divisor moment pays the remaining quotient sum.

The final uniform theorem instantiates the coefficient bounds from the
original UniformAuxiliarySW, not from a BDH or medium-output premise.
The high-conductor sieve and the positive Gram insertion remain separate.
-/

namespace ImbalancedChen.Part3.ActualLowConductorQuotientSumSourceOnly

noncomputable section
open Classical Finset
open scoped BigOperators Pointwise
open ActualFilteredPrimitiveSWSourceOnly
open ActualFilteredPrincipalCharacterVarianceSourceOnly
open SharedFirstFactorCharacterDictionary
open TransposedPrimitiveUMoment
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def tau (n : ℕ) : ℝ := (n.divisors.card : ℝ)

theorem tau_nonneg (n : ℕ) : 0 ≤ tau n := Nat.cast_nonneg _

theorem tau_mul_le (r k : ℕ) : tau (r*k) ≤ tau r * tau k := by
  unfold tau
  exact_mod_cast card_divisors_mul_le r k

def lowCharacters (ell R : ℕ) : Finset (DirichletCharacter ℂ ell) :=
  (Finset.univ.erase 1).filter (fun chi => chi.conductor ≤ R)

def conductorFibre (ell f : ℕ) : Finset (DirichletCharacter ℂ ell) :=
  (Finset.univ.erase 1).filter (fun chi => chi.conductor = f)

/-- The exact reduced-class Parseval contribution at the selected conductors. -/
def lowEnergy (d : MediumAtom) (Q R r : ℕ) : ℝ :=
  ∑ ell ∈ Finset.Icc 1 Q,
    (∑ chi ∈ lowCharacters ell R, ‖filteredCharacterSum d r ell chi‖^2) /
      (ell.totient : ℝ)

/-- A conductor fibre is an image of actual characters at its conductor.
Only an upper bound is needed; no unproved multiplicity-one assumption is used. -/
theorem card_conductorFibre_le {ell f : ℕ} (hell : 0 < ell) (hfd : f ∣ ell) :
    (conductorFibre ell f).card ≤ f.totient := by
  let : NeZero ell := ⟨hell.ne'⟩
  have hf : 0 < f := Nat.pos_of_dvd_of_pos hfd hell
  let : NeZero f := ⟨hf.ne'⟩
  let lifted : Finset (DirichletCharacter ℂ ell) :=
    (Finset.univ : Finset (DirichletCharacter ℂ f)).image
      (fun psi => DirichletCharacter.changeLevel hfd psi)
  have hsub : conductorFibre ell f ⊆ lifted := by
    intro chi hchi
    have hcf : chi.conductor = f := (Finset.mem_filter.mp hchi).2
    subst f
    exact Finset.mem_image.mpr
      ⟨chi.primitiveCharacter, Finset.mem_univ _, chi.changeLevel_primitiveCharacter⟩
  calc
    _ ≤ lifted.card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (DirichletCharacter ℂ f)).card := Finset.card_image_le
    _ = Nat.card (DirichletCharacter ℂ f) := by
      rw [Finset.card_univ, Nat.card_eq_fintype_card]
    _ = f.totient := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ f

/-- Every low character appears in exactly its actual conductor fibre. -/
theorem sum_lowCharacters_by_conductor {ell : ℕ} (hell : 0 < ell) (R : ℕ)
    (F : DirichletCharacter ℂ ell → ℝ) :
    (∑ chi ∈ lowCharacters ell R, F chi) =
      ∑ f ∈ ell.divisors.filter (fun f => f ≤ R),
        ∑ chi ∈ conductorFibre ell f, F chi := by
  have hmaps : Set.MapsTo (fun chi : DirichletCharacter ℂ ell => chi.conductor)
      (lowCharacters ell R) (ell.divisors.filter (fun f => f ≤ R)) := by
    intro chi hchi
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨chi.conductor_dvd_level, hell.ne'⟩,
        (Finset.mem_filter.mp hchi).2⟩
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := lowCharacters ell R) (t := ell.divisors.filter (fun f => f ≤ R))
    (g := fun chi => chi.conductor) hmaps F
  calc
    _ = ∑ f ∈ ell.divisors.filter (fun f => f ≤ R),
        ∑ chi ∈ (lowCharacters ell R).filter (fun chi => chi.conductor = f),
          F chi := hf
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f hf
      have hfR : f ≤ R := (Finset.mem_filter.mp hf).2
      have hset : (lowCharacters ell R).filter (fun chi => chi.conductor = f) =
          conductorFibre ell f := by
        ext chi
        simp only [lowCharacters, conductorFibre, Finset.mem_filter]
        constructor
        · exact fun h => ⟨h.1.1,h.2⟩
        · rintro ⟨hc,hcf⟩
          exact ⟨⟨hc,by simpa only [hcf] using hfR⟩,hcf⟩
      rw [hset]

/-- The totient comparison is valid for overlapping conductor/quotient primes. -/
theorem conductor_totient_ratio_le {ell f : ℕ}
    (hell : 0 < ell) (hfd : f ∣ ell) :
    (f.totient : ℝ) / (ell.totient : ℝ) ≤
      1 / ((ell / f).totient : ℝ) := by
  have hf : 0 < f := Nat.pos_of_dvd_of_pos hfd hell
  have hk : 0 < ell/f := Nat.div_pos (Nat.le_of_dvd hell hfd) hf
  have hfk : f * (ell/f) = ell := Nat.mul_div_cancel' hfd
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hpe : (0 : ℝ) < ell.totient := by exact_mod_cast Nat.totient_pos.mpr hell
  have hpf : (0 : ℝ) < f.totient := by exact_mod_cast Nat.totient_pos.mpr hf
  have hpk : (0 : ℝ) < (ell/f).totient := by exact_mod_cast Nat.totient_pos.mpr hk
  have hratio := multiple_totient_ratio_le_product f (ell/f) hf hk
  rw [div_mul_div_comm] at hratio
  have hr : (ell : ℝ) / (ell.totient : ℝ) ≤
      (ell : ℝ) / ((f.totient : ℝ) * ((ell/f).totient : ℝ)) := by
    simpa only [hfk, Nat.cast_mul] using hratio
  have hcross := (div_le_div_iff₀ hpe (mul_pos hpf hpk)).mp hr
  have hp : (f.totient : ℝ) * ((ell/f).totient : ℝ) ≤ ell.totient :=
    (mul_le_mul_left hellR).mp hcross
  exact (div_le_div_iff₀ hpe hpk).mpr (by simpa using hp)

/-- Literal multiples reindex the quotient without losing repeated conductor primes. -/
theorem sum_quotients_over_multiples (Q f : ℕ) (hf : 0 < f) (F : ℕ → ℝ) :
    (∑ ell ∈ (Finset.Icc 1 Q).filter (fun ell => f ∣ ell), F (ell/f)) =
      ∑ k ∈ Finset.Icc 1 (Q/f), F k := by
  symm
  refine Finset.sum_bij (fun k _ => f*k) ?_ ?_ ?_ ?_
  · intro k hk
    obtain ⟨hk1,hkQ⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hf hk1,
        (Nat.mul_le_mul_left f hkQ).trans (Nat.mul_div_le Q f)⟩, dvd_mul_right f k⟩
  · intro k hk k' hk' heq
    exact Nat.eq_of_mul_eq_mul_left hf heq
  · intro ell hell
    obtain ⟨hell,hfell⟩ := Finset.mem_filter.mp hell
    refine ⟨ell/f, Finset.mem_Icc.mpr ⟨?_,?_⟩, Nat.mul_div_cancel' hfell⟩
    · exact Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hell).1 hfell) hf
    · exact Nat.div_le_div_right (Finset.mem_Icc.mp hell).2
  · intro k hk
    rw [Nat.mul_div_cancel_left k hf]

/-- Finite conductor/quotient summation, with the exact product cutoff first.
Extending Q/f to Q is used only after the quotient has been recovered. -/
theorem sum_conductor_quotient_le (Q R : ℕ) (F : ℕ → ℝ)
    (hF : ∀ k, 0 ≤ F k) :
    (∑ ell ∈ Finset.Icc 1 Q,
      ∑ f ∈ ell.divisors.filter (fun f => f ≤ R), F (ell/f)) ≤
      (R : ℝ) * ∑ k ∈ Finset.Icc 1 Q, F k := by
  have hset (ell : ℕ) (hell : ell ∈ Finset.Icc 1 Q) :
      ell.divisors.filter (fun f => f ≤ R) =
        (Finset.Icc 1 R).filter (fun f => f ∣ ell) := by
    have hell0 : 0 < ell := (Finset.mem_Icc.mp hell).1
    ext f
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hfd,_⟩,hfR⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hfd hell0,hfR⟩,hfd⟩
    · rintro ⟨⟨_,hfR⟩,hfd⟩
      exact ⟨⟨hfd,hell0.ne'⟩,hfR⟩
  calc
    _ = ∑ ell ∈ Finset.Icc 1 Q, ∑ f ∈ Finset.Icc 1 R,
        if f ∣ ell then F (ell/f) else 0 := by
      apply Finset.sum_congr rfl
      intro ell hell
      rw [hset ell hell, Finset.sum_filter]
    _ = ∑ f ∈ Finset.Icc 1 R,
        ∑ ell ∈ (Finset.Icc 1 Q).filter (fun ell => f ∣ ell), F (ell/f) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ = ∑ f ∈ Finset.Icc 1 R, ∑ k ∈ Finset.Icc 1 (Q/f), F k := by
      apply Finset.sum_congr rfl
      intro f hf
      exact sum_quotients_over_multiples Q f (Finset.mem_Icc.mp hf).1 F
    _ ≤ ∑ _f ∈ Finset.Icc 1 R, ∑ k ∈ Finset.Icc 1 Q, F k := by
      apply Finset.sum_le_sum
      intro f hf
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        obtain ⟨hk1,hkQ⟩ := Finset.mem_Icc.mp hk
        exact Finset.mem_Icc.mpr ⟨hk1,hkQ.trans (Nat.div_le_self Q f)⟩
      · intro k _ _
        exact hF k
    _ = _ := by simp

/-- Reuse the pinned native fixed-order divisor moment, with order fixed
before all varying moduli. There is no Q^epsilon loss on the log saving. -/
theorem sum_tau_pow_div_totient_le (Q s : ℕ) (hQ : 1 ≤ Q) :
    (∑ k ∈ Finset.Icc 1 Q, tau k ^ s / (k.totient : ℝ)) ≤
      (1 + Real.log (Q : ℝ)) ^ (2 * (2 ^ s)) := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hI : Finset.Icc 1 Q = Finset.Ioc 0 Q := by
    ext k
    simp only [Finset.mem_Icc,Finset.mem_Ioc]
    omega
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 Q, (fouvryTau (2^s) k : ℝ) / (k.totient : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      have hk0 : k ≠ 0 := by
        have hk1 := (Finset.mem_Icc.mp hk).1
        omega
      have hp := fouvryTau_pow_le 2 s hk0
      rw [fouvryTau_two] at hp
      exact_mod_cast hp
    _ ≤ _ := by
      rw [hI]
      simpa only [Nat.floor_natCast] using
        sum_fouvryTau_div_totient_le_real (2^s) hQR

/-- The complete finite low-conductor sum of the actual r-filtered alpha.
The local bound is instantiated from original SW in the following theorem. -/
theorem lowEnergy_le_fixed_divisor_moment
    (d : MediumAtom) (Q R r C0 : ℕ) (hQ : 1 ≤ Q)
    {E : ℝ} (hE : 0 ≤ E)
    (hbound : ∀ ell ∈ Finset.Icc 1 Q, ∀ chi ∈ lowCharacters ell R,
      ‖filteredCharacterSum d r ell chi‖ ≤
        E * tau (r * (ell / chi.conductor)) ^ C0) :
    lowEnergy d Q R r ≤
      E^2 * tau r ^ (2*C0) * (R : ℝ) *
        (1 + Real.log (Q : ℝ)) ^ (2 * (2 ^ (2*C0))) := by
  let G : ℕ → ℝ := fun k => tau k ^ (2*C0) / (k.totient : ℝ)
  have hG (k : ℕ) : 0 ≤ G k := div_nonneg
    (pow_nonneg (tau_nonneg k) _) (Nat.cast_nonneg _)
  have hlocal (ell : ℕ) (hell : ell ∈ Finset.Icc 1 Q)
      (f : ℕ) (hf : f ∈ ell.divisors.filter (fun f => f ≤ R)) :
      (∑ chi ∈ conductorFibre ell f, ‖filteredCharacterSum d r ell chi‖^2) /
        (ell.totient : ℝ) ≤ E^2 * tau r ^ (2*C0) * G (ell/f) := by
    have hell0 : 0 < ell := (Finset.mem_Icc.mp hell).1
    have hfd : f ∣ ell := (Nat.mem_divisors.mp (Finset.mem_filter.mp hf).1).1
    have hfR : f ≤ R := (Finset.mem_filter.mp hf).2
    have hcoeff : ∀ chi ∈ conductorFibre ell f,
        ‖filteredCharacterSum d r ell chi‖^2 ≤ (E * tau (r*(ell/f))^C0)^2 := by
      intro chi hchi
      obtain ⟨hchi,hcf⟩ := Finset.mem_filter.mp hchi
      have hlow : chi ∈ lowCharacters ell R :=
        Finset.mem_filter.mpr ⟨hchi, by simpa only [hcf] using hfR⟩
      have hb := hbound ell hell chi hlow
      rw [hcf] at hb
      exact pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hsum : (∑ chi ∈ conductorFibre ell f,
        ‖filteredCharacterSum d r ell chi‖^2) ≤
        (f.totient : ℝ) * (E * tau (r*(ell/f))^C0)^2 := by
      calc
        _ ≤ ∑ _chi ∈ conductorFibre ell f, (E * tau (r*(ell/f))^C0)^2 :=
          Finset.sum_le_sum hcoeff
        _ = ((conductorFibre ell f).card : ℝ) * (E * tau (r*(ell/f))^C0)^2 := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (by exact_mod_cast card_conductorFibre_le hell0 hfd) (sq_nonneg _)
    have htau : (E * tau (r*(ell/f))^C0)^2 ≤
        E^2 * tau r ^ (2*C0) * tau (ell/f) ^ (2*C0) := by
      have ht := pow_le_pow_left₀ (tau_nonneg _) (tau_mul_le r (ell/f)) (2*C0)
      have ht' := mul_le_mul_of_nonneg_left ht (sq_nonneg E)
      simpa only [mul_pow,← pow_mul,Nat.mul_comm,mul_assoc] using ht'
    calc
      _ ≤ ((f.totient : ℝ) / (ell.totient : ℝ)) *
          (E * tau (r*(ell/f))^C0)^2 := by
        simpa only [div_mul_eq_mul_div] using
          div_le_div_of_nonneg_right hsum (Nat.cast_nonneg ell.totient)
      _ ≤ (1 / ((ell/f).totient : ℝ)) *
          (E^2 * tau r ^ (2*C0) * tau (ell/f) ^ (2*C0)) :=
        mul_le_mul (conductor_totient_ratio_le hell0 hfd) htau
          (sq_nonneg _) (div_nonneg zero_le_one (Nat.cast_nonneg _))
      _ = _ := by dsimp only [G]; ring
  calc
    lowEnergy d Q R r = ∑ ell ∈ Finset.Icc 1 Q,
        ∑ f ∈ ell.divisors.filter (fun f => f ≤ R),
          (∑ chi ∈ conductorFibre ell f, ‖filteredCharacterSum d r ell chi‖^2) /
            (ell.totient : ℝ) := by
      unfold lowEnergy
      apply Finset.sum_congr rfl
      intro ell hell
      rw [sum_lowCharacters_by_conductor (Finset.mem_Icc.mp hell).1 R,
        Finset.sum_div]
    _ ≤ ∑ ell ∈ Finset.Icc 1 Q,
        ∑ f ∈ ell.divisors.filter (fun f => f ≤ R),
          E^2 * tau r ^ (2*C0) * G (ell/f) :=
      Finset.sum_le_sum (fun ell hell => Finset.sum_le_sum (hlocal ell hell))
    _ = E^2 * tau r ^ (2*C0) *
        (∑ ell ∈ Finset.Icc 1 Q,
          ∑ f ∈ ell.divisors.filter (fun f => f ≤ R), G (ell/f)) := by
      simp only [Finset.mul_sum]
    _ ≤ E^2 * tau r ^ (2*C0) * ((R : ℝ) * ∑ k ∈ Finset.Icc 1 Q, G k) :=
      mul_le_mul_of_nonneg_left (sum_conductor_quotient_le Q R G hG)
        (mul_nonneg (sq_nonneg _) (pow_nonneg (tau_nonneg r) _))
    _ ≤ _ := by
      have hm := sum_tau_pow_div_totient_le Q (2*C0) hQ
      have hc : 0 ≤ E^2 * tau r ^ (2*C0) * (R : ℝ) := by positivity
      simpa only [G, mul_assoc] using mul_le_mul_of_nonneg_left hm hc

/-- Original SW now supplies the entire finite low-conductor contribution
with fixed quotient divisor moments. R may vary below log(scale)^L; one
common C,x0 is chosen first. The high-conductor sum is not assumed here. -/
theorem uniformAuxiliarySW_lowEnergy
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∀ A L : ℝ, 0 < A → 0 ≤ L →
      ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
        ∀ i, x0 ≤ (F i).scale → ∀ Q R r : ℕ,
          1 ≤ Q → 1 ≤ r → (R : ℝ) ≤ (Real.log (F i).scale)^L →
          lowEnergy (F i) Q R r ≤
            (C*(F i).U / (Real.log (F i).scale)^A)^2 *
              tau r ^ (2*C0) * (R : ℝ) *
              (1 + Real.log (Q : ℝ)) ^ (2 * (2 ^ (2*C0))) := by
  intro A L hA hL
  obtain ⟨C,hC,x0,hx0,hbound⟩ :=
    uniformAuxiliarySW_lowConductor_filteredCharacterSum F B C0 sigma kappa c0
      hadmissible hSW A L hA hL
  refine ⟨C,hC,x0,hx0,?_⟩
  intro i hx Q R r hQ hr hR
  have hlog : 0 < Real.log (F i).scale := Real.log_pos (hx0.trans_le hx)
  have hE : 0 ≤ C*(F i).U / (Real.log (F i).scale)^A :=
    div_nonneg (mul_nonneg hC.le (by linarith [(hadmissible i).1]))
      (Real.rpow_pos_of_pos hlog A).le
  apply lowEnergy_le_fixed_divisor_moment (F i) Q R r C0 hQ hE
  intro ell hell chi hchi
  have hchi' := Finset.mem_filter.mp hchi
  have hne : chi ≠ 1 := (Finset.mem_erase.mp hchi'.1).1
  have hcond : (chi.conductor : ℝ) ≤ (Real.log (F i).scale)^L :=
    (by exact_mod_cast hchi'.2 : (chi.conductor : ℝ) ≤ R).trans hR
  have hb := hbound i hx r ell hr (Finset.mem_Icc.mp hell).1 chi hne hcond
  simpa only [tau, div_mul_eq_mul_div, mul_assoc, mul_comm, mul_left_comm] using hb

end
end ImbalancedChen.Part3.ActualLowConductorQuotientSumSourceOnly
