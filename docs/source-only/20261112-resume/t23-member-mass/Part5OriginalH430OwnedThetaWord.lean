import ImbalancedChen.Part5OriginalH430OwnedMemberMass
import ImbalancedChen.Part5OriginalH430RootIntervalTheta

/-! Exact outer arithmetic measure for the entire ordered active prime word.
No assumption that the product is squarefree; repeated prime factors are
inserted with their actual multipliers. No padded coordinates contribute. -/
namespace ImbalancedChen.Part5OriginalH430OwnedThetaWord
noncomputable section
open scoped Classical BigOperators
open Wu2008DoubleSieve
open P2OriginalChildPhysicalNormalization
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalH430OwnedMemberMass Part5OriginalH430OwnedRootCounts
open Part5OriginalH430IntegerItineraries Part5OriginalH430SameQHistoryCells
open Part5OriginalH430PhysicalRoots Part5OriginalH430SelectedBankCarrierSupply
open Part5OriginalH430RootIntervalTheta (literalScale)
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418 (logarithmicIntegral)

def wordFactor (d : ℕ) : List ℕ → ℝ
  | [] => 1
  | p :: ps => localPrimeFactor d p * wordFactor (d*p) ps

private theorem prime_ratio {A : ℝ} (d p : ℕ) (hA : 4 ≤ A) (hp : A ≤ (p:ℝ)) :
    1 ≤ localPrimeFactor d p * (p:ℝ) ∧
      localPrimeFactor d p * (p:ℝ) ≤ 1 + 4/A := by
  have hAp : 0 < A := by linarith
  have hpp : (0:ℝ) < p := by linarith
  have hsub : (0:ℝ) < (p:ℝ)-2 := by linarith
  unfold localPrimeFactor
  split_ifs
  · rw [one_div, inv_mul_cancel₀ hpp.ne']
    constructor
    · exact le_rfl
    · have : 0 ≤ 4/A := by positivity
      linarith
  · have h : 1/((p:ℝ)-2)*(p:ℝ) = 1+2/((p:ℝ)-2) := by
      field_simp [hsub.ne'] <;> ring
    rw [h]
    constructor
    · have : (0:ℝ) ≤ 2/((p:ℝ)-2) := by positivity
      linarith
    · apply add_le_add_left
      apply (div_le_div_iff₀ hsub hAp).mpr
      linarith

/-- Uniform for the entire ordered word, including repeated and equal
products. The right factor tends to 1 at fixed depth when A is the
common physical prime floor. -/
theorem word_to_harmonic {A : ℝ} (hA : 4 ≤ A) (ps : List ℕ)
    (hs : ∀ p ∈ ps, A ≤ (p:ℝ)) (d : ℕ) :
    1 ≤ wordFactor d ps * (ps.prod:ℝ) ∧
      wordFactor d ps * (ps.prod:ℝ) ≤ (1+4/A)^ps.length := by
  induction ps generalizing d with
  | nil => simp [wordFactor]
  | cons p ps ih =>
    have h := prime_ratio d p hA (hs p (List.mem_cons_self ..))
    have t := ih (fun q hq => hs q (List.mem_cons_of_mem _ hq)) (d*p)
    have hfac : wordFactor d (p::ps) * ((p::ps).prod:ℝ) =
        (localPrimeFactor d p*(p:ℝ)) * (wordFactor (d*p) ps*(ps.prod:ℝ)) := by
      simp only [wordFactor,List.prod_cons,Nat.cast_mul]; ring
    rw [hfac,List.length_cons,pow_succ]
    exact ⟨one_le_mul_of_one_le_of_one_le h.1 t.1,
      (mul_le_mul h.2 t.2 (zero_le_one.trans t.1)
        ((zero_le_one.trans h.1).trans h.2)).trans_eq (mul_comm _ _)⟩

theorem inserted_word {N : ℕ} (hN : 0 < N) (ps : List ℕ)
    (hs : ∀ p ∈ ps, p.Prime ∧ 2 < p ∧ p.Coprime N) {d : ℕ} (hd : 0 < d) :
    wuSingularSeries ((d*ps.prod)*N) / (Nat.totient (d*ps.prod):ℝ) =
      (wuSingularSeries (d*N) / (Nat.totient d:ℝ)) * wordFactor d ps := by
  induction ps generalizing d with
  | nil => simp [wordFactor]
  | cons p ps ih =>
    obtain ⟨hp,h2,hcop⟩ := hs p (List.mem_cons_self ..)
    have ht := ih (fun q hq => hs q (List.mem_cons_of_mem _ hq)) (Nat.mul_pos hd hp.pos)
    have ha : wuSingularSeries ((d*p)*N)/(Nat.totient (d*p):ℝ) =
        (wuSingularSeries (d*N)/(Nat.totient d:ℝ))*localPrimeFactor d p := by
      simpa only [localPrimeFactor] using wu_inserted_arithmetic_weight hN hd hp h2 hcop
    simp only [List.prod_cons, ← Nat.mul_assoc d p ps.prod, wordFactor]
    rw [ht,ha,mul_assoc]

private theorem owned_letters {N n m mesh : ℕ} {k : Root} {tau : ℝ}
    {c : RootKey n m} {h : Label N mesh} (he : Even N)
    (hh : h ∈ ownedMembers N n m mesh k tau c) :
    ∀ p ∈ labelWord h, p.Prime ∧ 2 < p ∧ p.Coprime N := by
  have v := (mem_ownedMembers.mp hh).1
  have hall := integerWord_letters [h.2.2.1.val] h.2.2.2.1 (labelPrimes h)
    (fun p hp => (List.mem_singleton.mp hp).symm ▸ v.1) v.2.2.1
  intro p hp
  obtain ⟨hpr,hcop⟩ := hall p hp
  refine ⟨hpr,?_,hcop⟩
  have hp2 := hpr.two_le
  by_contra! hn
  have heq : p = 2 := by omega
  subst p
  have hd := Nat.dvd_gcd (dvd_refl 2) (even_iff_two_dvd.mp he)
  rw [hcop.gcd_eq_one] at hd
  norm_num at hd

/-- Per original fibre, not a root-independent fictitious common Q.
This density identity uses the real arithmetic normalizer, before
passing to a prime-box limit or to the selected receiver counts. -/
theorem owned_theta_density {N n m mesh : ℕ} {k : Root} {tau : ℝ} {c : RootKey n m}
    {h : Label N mesh} (hN : 2 ≤ N) (he : Even N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hh : h ∈ ownedMembers N n m mesh k tau c) :
    thetaAtom N (cellQ N n c.1) (labelPrefix h) / singularNormalization N =
      literalScale N * (4 * wordFactor 1 (labelWord h) / Lkey c h) := by
  have hN0 : 0 < N := by omega
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have s := owned_support hN ht ht' hn hh
  dsimp only at s
  have hL := Part5OriginalH430FrozenIntegerSupport.frozenResidualFloor_pos.trans_le s.2.2.1.1
  have hden : Real.log (cellQ N n c.1 / (labelPrefix h:ℝ)) = Lkey c h * Real.log N := by
    change _ = (Real.log (cellQ N n c.1 / (labelPrefix h:ℝ)) / Real.log N) * Real.log N
    field_simp [hlog.ne']
  have har : wuSingularSeries (labelPrefix h*N)/(Nat.totient (labelPrefix h):ℝ) =
      singularSeries N * wordFactor 1 (labelWord h) := by
    simpa only [one_mul, Nat.totient_one, Nat.cast_one, div_one, wuSingularSeries_eq_liu N hN0,
      ← currentChen_singularSeries_eq_liuSingularSeries N] using
      (inserted_word hN0 (labelWord h) (owned_letters he hh) (d := 1) (by decide))
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN0
  unfold thetaAtom
  rw [← div_div, har, hden]
  unfold singularNormalization literalScale
  field_simp [hlog.ne', hL.ne', (singularSeries_pos N).ne', hNr.ne'] <;> ring

/-- This bound is for literal path coefficients, not the number of source
positions over a given label or for arbitrary externally chosen marks. -/
theorem history_mark_le_one {N : ℕ} (o : Part5OriginalH430RequestedHistory.Occurrence N) :
    Part5OriginalH430RequestedHistory.mark o ≤ 1 := by
  have hweight (e : Part5OriginalH430RequestedBranches.Edge N) :
      Part5OriginalH430RequestedBranches.edgeWeight e ≤ 1 := by
    cases e with
    | w2Fixed j b => cases b <;> norm_num [Part5OriginalH430RequestedBranches.edgeWeight]
    | _ => norm_num [Part5OriginalH430RequestedBranches.edgeWeight]
  have hpath (es : List (Part5OriginalH430RequestedBranches.Edge N)) :
      (es.map Part5OriginalH430RequestedBranches.edgeWeight).prod ≤ 1 := by
    induction es with
    | nil => simp
    | cons e es ih =>
      simp only [List.map_cons,List.prod_cons]
      exact (mul_le_mul_of_nonneg_left ih
        (Part5OriginalH430RequestedBranches.edgeWeight_pos e).le).trans
        (by simpa only [mul_one] using hweight e)
  exact hpath o.path

end
end ImbalancedChen.Part5OriginalH430OwnedThetaWord
