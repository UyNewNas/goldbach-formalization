import ImbalancedChen.Part3ActualLowConductorQuotientSum
import ImbalancedChen.Part3SharedFirstFactorHighConductor
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Original medium appendix (14): the imprimitive quotient k is fixed BEFORE
the primitive large sieve in f. The actual alpha carrier and r*k mask are
retained in every primitive polynomial. The native sharp primitive cell
bound, already used by the production high-conductor source, is applied
at spectral parameter zero. No whole variance bound is a premise.

The complete finite conductor/quotient sum is then paid with an explicit
finite doubling-window count and the native reciprocal-totient moment.
This deliberately keeps a fixed logarithmic factor on the N*Q term; it
introduces no Q^epsilon factor. The paper's strict Q<=N*x^(-delta) margin
can pay that fixed logarithm when the final arbitrary-log-saving (14) is
assembled. That asymptotic interpolation is not claimed in this module.
-/

namespace ImbalancedChen.Part3.ActualHighConductorFixedQuotientSourceOnly

noncomputable section
open Classical Finset
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open SharedFirstFactorCharacterDictionary
open ActualFilteredPrimitiveSWSourceOnly
open ActualFilteredPrincipalCharacterVarianceSourceOnly
open ActualLowConductorQuotientSumSourceOnly

/-- One actual auxiliary mask, independent of the primitive conductor f. -/
def primitiveSum (d : MediumAtom) (r k f : ℕ) (psi : PrimitiveCharacter f) : ℂ :=
  auxiliaryCharacterSum d.alphaCarrier d.alpha (r*k) f psi.1

def primitiveEnergy (d : MediumAtom) (r k f : ℕ) : ℝ :=
  (∑ psi : PrimitiveCharacter f, ‖primitiveSum d r k f psi‖^2) /
    (f.totient : ℝ)

theorem primitiveEnergy_nonneg (d : MediumAtom) (r k f : ℕ) :
    0 ≤ primitiveEnergy d r k f := by
  unfold primitiveEnergy
  positivity

def highCharacters (ell R : ℕ) : Finset (DirichletCharacter ℂ ell) :=
  (Finset.univ.erase 1).filter (fun chi => R < chi.conductor)

def highEnergy (d : MediumAtom) (Q R r : ℕ) : ℝ :=
  ∑ ell ∈ Finset.Icc 1 Q,
    (∑ chi ∈ highCharacters ell R, ‖filteredCharacterSum d r ell chi‖^2) /
      (ell.totient : ℝ)

def fixedHighEnergy (d : MediumAtom) (r k R T : ℕ) : ℝ :=
  ∑ f ∈ (Finset.Icc 1 T).filter (fun f => R < f), primitiveEnergy d r k f

/-- The actual alpha interval is contained in the original positive prefix. -/
theorem alpha_subset_prefix {d : MediumAtom} (hU : 1 ≤ d.U) :
    d.alphaCarrier ⊆ Finset.Icc 1 (Nat.floor (2*d.U)) := by
  intro n hn
  obtain ⟨hn,_⟩ := Finset.mem_filter.mp hn
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hn
  have hc : 1 ≤ Nat.ceil d.U := by exact_mod_cast hU.trans (Nat.le_ceil d.U)
  exact Finset.mem_Icc.mpr ⟨hc.trans hlo,hhi⟩

/-- Native polynomial convention uses psi rather than conjugate psi.
Conjugating the original alpha gives precisely the original coefficient norm. -/
theorem primitiveSum_star_bridge (d : MediumAtom) (r k f : ℕ)
    (psi : PrimitiveCharacter f) :
    primitiveSum d r k f psi =
      star (∑ n ∈ d.alphaCarrier,
        (if n.Coprime (r*k) then star (d.alpha n) else 0) * psi.1 (n : ZMod f)) := by
  unfold primitiveSum auxiliaryCharacterSum
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Coprime (r*k) <;> simp [hn]

theorem actual_masked_energy_le_prefix {d : MediumAtom}
    (hU : 1 ≤ d.U) (halpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1)
    (r k : ℕ) :
    (∑ n ∈ d.alphaCarrier,
      ‖if n.Coprime (r*k) then star (d.alpha n) else 0‖^2) ≤
      (Nat.floor (2*d.U) : ℝ) := by
  calc
    _ ≤ ∑ _n ∈ d.alphaCarrier, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hg : n.Coprime (r*k)
      · rw [if_pos hg,norm_star]
        simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (halpha n hn) 2
      · simp [hg]
    _ = (d.alphaCarrier.card : ℝ) := by simp
    _ ≤ (Nat.floor (2*d.U) : ℝ) := by
      have hc := Finset.card_le_card (alpha_subset_prefix hU)
      simpa only [Nat.card_Icc,Nat.add_sub_cancel] using
        (show (d.alphaCarrier.card : ℝ) ≤ ((Finset.Icc 1 (Nat.floor (2*d.U))).card : ℝ)
          by exact_mod_cast hc)

/-- Actual fixed-k primitive cell from the named native sharp large sieve.
The r*k filter is chosen once for the whole f cell, without a stability
assumption for a conductor-varying or final discrepancy coefficient. -/
theorem actual_primitive_cell_le {d : MediumAtom}
    (hU : 1 ≤ d.U) (halpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1)
    (r k D : ℕ) (hD : 0 < D) :
    (∑ f ∈ Finset.Ioc D (2*D), primitiveEnergy d r k f) ≤
      (2*chen1973Lemma6Eq19SharpConstant) *
        ((D : ℝ) + (Nat.floor (2*d.U) : ℝ)/(D : ℝ)) *
          (Nat.floor (2*d.U) : ℝ) := by
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h := ChenLiuCoprimeProducer.polynomial_second_moment_energy
    d.alphaCarrier (fun n => if n.Coprime (r*k) then star (d.alpha n) else 0)
    (Nat.floor (2*d.U)) (alpha_subset_prefix hU) hDR (0 : ℂ)
  have hcell : ChenLiuCoprimeProducer.conductorCell (D : ℝ) = Finset.Ioc D (2*D) := by
    have hcast : (2 : ℝ)*(D : ℝ) = ((2*D : ℕ) : ℝ) := by norm_cast
    simp only [ChenLiuCoprimeProducer.conductorCell,hcast,Nat.floor_natCast]
  simp only [hcell,ChenLiuCoprimeProducer.polynomial,Complex.cpow_zero,div_one] at h
  have hs : (∑ f ∈ Finset.Ioc D (2*D), primitiveEnergy d r k f) =
      ∑ f ∈ Finset.Ioc D (2*D), (f.totient : ℝ)⁻¹ *
        ∑ psi : PrimitiveCharacter f,
          ‖∑ n ∈ d.alphaCarrier,
            (if n.Coprime (r*k) then star (d.alpha n) else 0) *
              psi.1 (n : ZMod f)‖^2 := by
    unfold primitiveEnergy
    simp_rw [primitiveSum_star_bridge,norm_star]
    simp only [div_eq_mul_inv,mul_comm]
  rw [hs]
  exact h.trans (mul_le_mul_of_nonneg_left (actual_masked_energy_le_prefix hU halpha r k)
    (by have hC := chen1973Lemma6_eq19SharpConstant_pos; positivity))

/-- Exact native conductor regrouping, extracted from the private helper
of Part3SharedFirstFactorHighConductor without its later Mobius losses. -/
theorem sum_high_by_conductor {ell : ℕ} (hell : 0 < ell)
    (R : ℕ) (hR : 0 < R) (F : (f : ℕ) → PrimitiveCharacter f → ℝ) :
    (∑ chi ∈ highCharacters ell R,
      F chi.conductor (conductorPrimitiveCharacter chi)) =
      ∑ f ∈ ell.divisors.filter (fun f => R < f), ∑ psi : PrimitiveCharacter f, F f psi := by
  let : NeZero ell := ⟨hell.ne'⟩
  have hset : highCharacters ell R =
      (nonprincipalCharacters ell).filter (fun chi => R < chi.conductor) := rfl
  rw [hset,Finset.sum_filter,
    sum_nonprincipal_by_conductor hell (fun f psi => if R < f then F f psi else 0)]
  simp only [nonprincipalConductors,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hRf : R < f
  · have hf2 : 2 ≤ f := by omega
    simp only [if_pos hf2,hRf,if_true]
  · simp only [if_neg hRf,Finset.sum_const_zero,ite_self]

/-- Exact triangular conductor/quotient rearrangement. -/
theorem sum_divisor_quotient_triangle (Q : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ ell ∈ Finset.Icc 1 Q, ∑ f ∈ ell.divisors, F f (ell/f)) =
      ∑ k ∈ Finset.Icc 1 Q, ∑ f ∈ Finset.Icc 1 (Q/k), F f k := by
  have hdiv (ell : ℕ) (hell : ell ∈ Finset.Icc 1 Q) :
      ell.divisors = (Finset.Icc 1 Q).filter (fun f => f ∣ ell) := by
    have hell0 := (Finset.mem_Icc.mp hell).1
    ext f
    simp only [Nat.mem_divisors,Finset.mem_filter,Finset.mem_Icc]
    constructor
    · rintro ⟨hfd,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hfd hell0,
        (Nat.le_of_dvd hell0 hfd).trans (Finset.mem_Icc.mp hell).2⟩,hfd⟩
    · exact fun h => ⟨h.2,by omega⟩
  have htriangle (f : ℕ) (hf : f ∈ Finset.Icc 1 Q) :
      Finset.Icc 1 (Q/f) = (Finset.Icc 1 Q).filter (fun k => f*k ≤ Q) := by
    have hf0 := (Finset.mem_Icc.mp hf).1
    ext k
    simp only [Finset.mem_Icc,Finset.mem_filter]
    constructor
    · rintro ⟨hk1,hkQ⟩
      refine ⟨⟨hk1,hkQ.trans (Nat.div_le_self Q f)⟩,?_⟩
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hf0).mp hkQ
    · rintro ⟨⟨hk1,_⟩,hkQ⟩
      exact ⟨hk1,(Nat.le_div_iff_mul_le hf0).mpr (by simpa only [Nat.mul_comm] using hkQ)⟩
  calc
    _ = ∑ ell ∈ Finset.Icc 1 Q, ∑ f ∈ Finset.Icc 1 Q,
        if f ∣ ell then F f (ell/f) else 0 := by
      apply Finset.sum_congr rfl
      intro ell hell
      rw [hdiv ell hell,Finset.sum_filter]
    _ = ∑ f ∈ Finset.Icc 1 Q,
        ∑ ell ∈ (Finset.Icc 1 Q).filter (fun ell => f ∣ ell), F f (ell/f) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ = ∑ f ∈ Finset.Icc 1 Q, ∑ k ∈ Finset.Icc 1 (Q/f), F f k := by
      apply Finset.sum_congr rfl
      intro f hf
      exact sum_quotients_over_multiples Q f (Finset.mem_Icc.mp hf).1 (F f)
    _ = ∑ f ∈ Finset.Icc 1 Q, ∑ k ∈ Finset.Icc 1 Q,
        if f*k ≤ Q then F f k else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [htriangle f hf,Finset.sum_filter]
    _ = ∑ k ∈ Finset.Icc 1 Q, ∑ f ∈ Finset.Icc 1 Q,
        if k*f ≤ Q then F f k else 0 := by
      rw [Finset.sum_comm]
      simp only [Nat.mul_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [htriangle k hk,Finset.sum_filter]

/-- The true imprimitive energy is bounded by fixed-quotient primitive
families with their original product cutoff Q/k. -/
theorem highEnergy_le_fixed_quotients (d : MediumAtom) (Q R r : ℕ) (hR : 0 < R) :
    highEnergy d Q R r ≤
      ∑ k ∈ Finset.Icc 1 Q, fixedHighEnergy d r k R (Q/k) / (k.totient : ℝ) := by
  have hlocal (ell : ℕ) (hell : ell ∈ Finset.Icc 1 Q) :
      (∑ chi ∈ highCharacters ell R, ‖filteredCharacterSum d r ell chi‖^2) /
        (ell.totient : ℝ) =
      ∑ f ∈ ell.divisors.filter (fun f => R < f),
        (∑ psi : PrimitiveCharacter f, ‖primitiveSum d r (ell/f) f psi‖^2) /
          (ell.totient : ℝ) := by
    have he0 := (Finset.mem_Icc.mp hell).1
    have hs : (∑ chi ∈ highCharacters ell R, ‖filteredCharacterSum d r ell chi‖^2) =
        ∑ chi ∈ highCharacters ell R,
          ‖primitiveSum d r (ell/chi.conductor) chi.conductor
            (conductorPrimitiveCharacter chi)‖^2 := by
      apply Finset.sum_congr rfl
      intro chi _
      rw [filteredCharacterSum_eq_primitive_quotient d he0 r chi]
      rfl
    rw [hs,sum_high_by_conductor he0 R hR,Finset.sum_div]
  calc
    highEnergy d Q R r = ∑ ell ∈ Finset.Icc 1 Q,
        ∑ f ∈ ell.divisors.filter (fun f => R < f),
          (∑ psi : PrimitiveCharacter f, ‖primitiveSum d r (ell/f) f psi‖^2) /
            (ell.totient : ℝ) := Finset.sum_congr rfl hlocal
    _ ≤ ∑ ell ∈ Finset.Icc 1 Q, ∑ f ∈ ell.divisors.filter (fun f => R < f),
        primitiveEnergy d r (ell/f) f / ((ell/f).totient : ℝ) := by
      apply Finset.sum_le_sum
      intro ell hell
      apply Finset.sum_le_sum
      intro f hf
      have he0 := (Finset.mem_Icc.mp hell).1
      have hfd : f ∣ ell := (Nat.mem_divisors.mp (Finset.mem_filter.mp hf).1).1
      have hf0 : 0 < f := Nat.pos_of_dvd_of_pos hfd he0
      have hk0 : 0 < ell/f := Nat.div_pos (Nat.le_of_dvd he0 hfd) hf0
      have hpe : (0 : ℝ) < ell.totient := by exact_mod_cast Nat.totient_pos.mpr he0
      have hpf : (0 : ℝ) < f.totient := by exact_mod_cast Nat.totient_pos.mpr hf0
      have hpk : (0 : ℝ) < (ell/f).totient := by exact_mod_cast Nat.totient_pos.mpr hk0
      have hp : (f.totient : ℝ) * ((ell/f).totient : ℝ) ≤ ell.totient := by
        have h := (div_le_div_iff₀ hpe hpk).mp (conductor_totient_ratio_le he0 hfd)
        simpa only [one_mul] using h
      unfold primitiveEnergy
      rw [div_div]
      exact div_le_div_of_nonneg_left (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (mul_pos hpf hpk) hp
    _ = ∑ k ∈ Finset.Icc 1 Q, fixedHighEnergy d r k R (Q/k) / (k.totient : ℝ) := by
      simp only [Finset.sum_filter]
      rw [sum_divisor_quotient_triangle Q
        (fun f k => if R < f then primitiveEnergy d r k f / (k.totient : ℝ) else 0)]
      unfold fixedHighEnergy
      simp only [Finset.sum_filter,Finset.sum_div,ite_div,zero_div]

/-- The finite doubling windows are chosen after k and the actual cutoff T. -/
def windows (R Q T : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log2 Q+1)).filter (fun j => R*2^j < T)

/-- Every strict high conductor under T<=Q belongs to an actual positive cell. -/
theorem windows_cover (R Q T : ℕ) (hR : 0 < R) (hQ : 0 < Q) (hTQ : T ≤ Q)
    (f : ℕ) (hRf : R < f) (hfT : f ≤ T) :
    ∃ j ∈ windows R Q T, f ∈ Finset.Ioc (R*2^j) (2*(R*2^j)) := by
  let m := (f-1)/R
  have hmpos : 0 < m := Nat.div_pos (by omega) hR
  let j := Nat.log2 m
  have hlo : 2^j ≤ m := Nat.log2_self_le hmpos.ne'
  have hhi : m < 2^(j+1) := Nat.lt_log2_self
  have hmul : R*m ≤ f-1 := Nat.mul_div_le (f-1) R
  have hlow : R*2^j < f := by
    have h := Nat.mul_le_mul_left R hlo
    omega
  have hdiv : f-1 < R*(m+1) := by
    simpa only [mul_comm] using
      (Nat.div_lt_iff_lt_mul hR).mp (by omega : (f-1)/R < m+1)
  have hhigh : f ≤ 2*(R*2^j) := by
    calc
      f ≤ R*(m+1) := by omega
      _ ≤ R*2^(j+1) := Nat.mul_le_mul_left R (by omega)
      _ = _ := by rw [Nat.pow_succ]; ring
  have hmQ : m ≤ Q := (Nat.div_le_self (f-1) R).trans (by omega)
  have hj : j ≤ Nat.log2 Q := (Nat.le_log2 hQ.ne').mpr (hlo.trans hmQ)
  exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega⟩,
    Finset.mem_Ioc.mpr ⟨hlow,hhigh⟩⟩

/-- Overlap costs at most the explicit finite sum over windows. -/
theorem sum_le_window_cover (S J : Finset ℕ) (block : ℕ → Finset ℕ)
    (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (hcover : ∀ n ∈ S, ∃ j ∈ J, n ∈ block j) :
    (∑ n ∈ S, F n) ≤ ∑ j ∈ J, ∑ n ∈ block j, F n := by
  calc
    _ ≤ ∑ n ∈ S, ∑ j ∈ J, if n ∈ block j then F n else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨j,hj,hnj⟩ := hcover n hn
      simpa only [if_pos hnj] using
        (Finset.single_le_sum (f := fun i => if n ∈ block i then F n else 0)
          (fun i _ => by
            by_cases hni : n ∈ block i
            · rw [if_pos hni]
              exact hF n
            · rw [if_neg hni]
              exact le_rfl) hj)
    _ = ∑ j ∈ J, ∑ n ∈ S with n ∈ block j, F n := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun n hn => (Finset.mem_filter.mp hn).2) (fun n _ _ => hF n)

/-- Fixed quotient, complete high-conductor sum; all cells use the same
original masked sequence. A finite logarithmic window factor is explicit. -/
theorem fixedHighEnergy_le {d : MediumAtom}
    (hU : 1 ≤ d.U) (halpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1)
    (r k R Q T : ℕ) (hR : 0 < R) (hQ : 0 < Q) (hTQ : T ≤ Q) :
    fixedHighEnergy d r k R T ≤
      (2*chen1973Lemma6Eq19SharpConstant) * (Nat.floor (2*d.U) : ℝ) *
        ((T : ℝ) + (Nat.floor (2*d.U) : ℝ)/(R : ℝ)) *
          ((Nat.log2 Q+1 : ℕ) : ℝ) := by
  let N : ℝ := Nat.floor (2*d.U)
  let A : ℝ := (2*chen1973Lemma6Eq19SharpConstant)*N*((T : ℝ)+N/(R : ℝ))
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hA : 0 ≤ A := by dsimp only [A]; have hC := chen1973Lemma6_eq19SharpConstant_pos; positivity
  have hcell (j : ℕ) (hj : j ∈ windows R Q T) :
      (∑ f ∈ Finset.Ioc (R*2^j) (2*(R*2^j)), primitiveEnergy d r k f) ≤ A := by
    let D := R*2^j
    have hRD : R ≤ D := Nat.le_mul_of_pos_right R (Nat.pow_pos (by decide))
    have hD : 0 < D := hR.trans_le hRD
    have hDT : D ≤ T := (Finset.mem_filter.mp hj).2.le
    have hRR : (0 : ℝ) < R := by exact_mod_cast hR
    have hRD' : (R : ℝ) ≤ D := by exact_mod_cast hRD
    have hi : N/(D : ℝ) ≤ N/(R : ℝ) :=
      div_le_div_of_nonneg_left hN hRR hRD'
    have hs : (D : ℝ)+N/(D : ℝ) ≤ (T : ℝ)+N/(R : ℝ) :=
      add_le_add (by exact_mod_cast hDT) hi
    refine (actual_primitive_cell_le hU halpha r k D hD).trans ?_
    change (2*chen1973Lemma6Eq19SharpConstant) *
      ((D : ℝ)+N/(D : ℝ))*N ≤ A
    have hC := chen1973Lemma6_eq19SharpConstant_pos
    calc
      _ = ((2*chen1973Lemma6Eq19SharpConstant)*N)*((D : ℝ)+N/(D : ℝ)) := by ring
      _ ≤ ((2*chen1973Lemma6Eq19SharpConstant)*N)*((T : ℝ)+N/(R : ℝ)) :=
        mul_le_mul_of_nonneg_left hs
          (mul_nonneg (by linarith : 0 ≤ 2*chen1973Lemma6Eq19SharpConstant) hN)
      _ = A := rfl
  have hcover : ∀ f ∈ (Finset.Icc 1 T).filter (fun f => R < f),
      ∃ j ∈ windows R Q T, f ∈ Finset.Ioc (R*2^j) (2*(R*2^j)) := by
    intro f hf
    obtain ⟨hf,hRf⟩ := Finset.mem_filter.mp hf
    exact windows_cover R Q T hR hQ hTQ f hRf (Finset.mem_Icc.mp hf).2
  calc
    _ ≤ ∑ j ∈ windows R Q T,
        ∑ f ∈ Finset.Ioc (R*2^j) (2*(R*2^j)), primitiveEnergy d r k f :=
      sum_le_window_cover _ _ _ _ (primitiveEnergy_nonneg d r k) hcover
    _ ≤ ∑ _j ∈ windows R Q T, A := Finset.sum_le_sum hcell
    _ = ((windows R Q T).card : ℝ)*A := by simp
    _ ≤ ((Nat.log2 Q+1 : ℕ) : ℝ)*A := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (by simp : (Finset.range (Nat.log2 Q+1)).card = Nat.log2 Q+1)
    _ = _ := by dsimp only [A,N]; ring

/-- Complete actual high-conductor energy from native primitive large sieve,
conductor/quotient reindexing and a fixed reciprocal-totient moment. -/
theorem actual_highEnergy_le_native_sieve {d : MediumAtom}
    (hU : 1 ≤ d.U) (halpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1)
    (Q R r : ℕ) (hQ : 1 ≤ Q) (hR : 0 < R) :
    highEnergy d Q R r ≤
      (2*chen1973Lemma6Eq19SharpConstant) * (Nat.floor (2*d.U) : ℝ) *
        ((Q : ℝ)+(Nat.floor (2*d.U) : ℝ)/(R : ℝ)) *
          ((Nat.log2 Q+1 : ℕ) : ℝ) * (1+Real.log (Q : ℝ))^2 := by
  let A : ℝ := (2*chen1973Lemma6Eq19SharpConstant) * (Nat.floor (2*d.U) : ℝ) *
    ((Q : ℝ)+(Nat.floor (2*d.U) : ℝ)/(R : ℝ)) * ((Nat.log2 Q+1 : ℕ) : ℝ)
  have hA : 0 ≤ A := by dsimp only [A]; have hC := chen1973Lemma6_eq19SharpConstant_pos; positivity
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 Q, fixedHighEnergy d r k R (Q/k)/(k.totient : ℝ) :=
      highEnergy_le_fixed_quotients d Q R r hR
    _ ≤ ∑ k ∈ Finset.Icc 1 Q, A/(k.totient : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      refine (fixedHighEnergy_le hU halpha r k R Q (Q/k) hR (by omega)
        (Nat.div_le_self Q k)).trans ?_
      have hT : ((Q/k : ℕ) : ℝ) ≤ Q := by exact_mod_cast Nat.div_le_self Q k
      have hC := chen1973Lemma6_eq19SharpConstant_pos
      dsimp only [A]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add_right hT _)
          (by positivity : 0 ≤ (2*chen1973Lemma6Eq19SharpConstant) *
            (Nat.floor (2*d.U) : ℝ))) (Nat.cast_nonneg _)
    _ = A * ∑ k ∈ Finset.Icc 1 Q, 1/(k.totient : ℝ) := by
      simp only [Finset.mul_sum,mul_one_div]
    _ ≤ _ := by
      have hm := sum_tau_pow_div_totient_le Q 0 hQ
      simp only [pow_zero,show 2*(2^0)=2 by decide] at hm
      exact mul_le_mul_of_nonneg_left hm hA

/-- Actual admissibility supplies all alpha gates for the high return. -/
theorem admissible_highEnergy_le_native_sieve
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Q R r : ℕ)
    (hQ : 1 ≤ Q) (hR : 0 < R) :
    highEnergy d Q R r ≤
      (2*chen1973Lemma6Eq19SharpConstant) * (Nat.floor (2*d.U) : ℝ) *
        ((Q : ℝ)+(Nat.floor (2*d.U) : ℝ)/(R : ℝ)) *
          ((Nat.log2 Q+1 : ℕ) : ℝ) * (1+Real.log (Q : ℝ))^2 := by
  obtain ⟨hU,_,_,_,_,_,_,_,_,_,_,_,halpha,_⟩ := hd
  exact actual_highEnergy_le_native_sieve hU halpha Q R r hQ hR

/-- The low and high sums are precisely the complementary pieces of the
original reduced-class variance, with the same actual r-filtered alpha. -/
theorem low_add_high_eq_actual_variance (d : MediumAtom) (Q R r : ℕ) :
    lowEnergy d Q R r + highEnergy d Q R r =
      ∑ ell ∈ Finset.Icc 1 Q, filteredVariance d ell r := by
  unfold lowEnergy highEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell hell
  have he0 := (Finset.mem_Icc.mp hell).1
  have hp := filteredVariance_eq_primitive_quotient_energy (d := d) (r := r) he0
  simp_rw [← filteredCharacterSum_eq_primitive_quotient d he0 r] at hp
  rw [hp,← add_div]
  congr 1
  simp only [lowCharacters,highCharacters,Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro chi hchi
  by_cases hc : chi.conductor ≤ R
  · have hnot : ¬ R < chi.conductor := by omega
    simp only [if_pos hc,if_neg hnot,add_zero]
  · have hgt : R < chi.conductor := by omega
    simp only [if_neg hc,if_pos hgt,zero_add]

end
end ImbalancedChen.Part3.ActualHighConductorFixedQuotientSourceOnly
