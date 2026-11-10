import ImbalancedChen.Part5OriginalH430W1InclusiveRoughCounts

/-! Reindex the unsifted integer sum with the original prefix mask and
strictly ordered triple, including the physical size endpoint and unit. -/
namespace ImbalancedChen.Part5OriginalH430W1PhysicalRoughDictionary
noncomputable section
open Set Real Finset Wu2008DoubleSieve LiLiuPrereqBuchstab
open P5OriginalActionMassBound (W1Target W1Anchor)
open P2OriginalHalfOpenProfileCarrier P2OriginalLiteralW1OldProfile (cutoff_eq_physical_power)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2N48TiedMomentPrimitives (moment11)
open Part5OriginalH430W1ConvertedPrimeQuadrature (chamber chamber_bounds)
open Part5OriginalH430W1InclusiveRoughCounts (height mass)
open scoped Classical BigOperators

def integerMass (N : ℕ) (Q : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10) : ℝ :=
  ∑ t∈orderedTriples (primeWindow (d*N) (cutoff Q d (W1Anchor j)) (cutoff Q d (W1Target i))),
    ((roughNumbers ((N:ℝ)/((d*t.1*t.2.1*t.2.2:ℕ):ℝ)) (t.2.1:ℝ)).card:ℝ)

def label (q : Fin 3 → ℕ) : ℕ × ℕ × ℕ := (q 2,q 1,q 0)

private theorem lt_iff {N : ℕ} {L : ℝ} (hN : 1<N) (hL : 0<L) (q : Fin 3 → ℕ)
    (hh : ∀ a,0<q a) (a b : Fin 3) :
    normalizedLog N L q a < normalizedLog N L q b ↔ q a<q b := by
  rw [←mul_lt_mul_left hL,←rpow_lt_rpow_left_iff (by exact_mod_cast hN : (1:ℝ)<N),
    normalizedLog_rpow hN hL q hh a,normalizedLog_rpow hN hL q hh b]
  exact Nat.cast_lt

private theorem membership {N d : ℕ} {Q L : ℝ} (hN : 1<N) (hd : 0<d) (hL : 0<L)
    (hQ : Q=(d:ℝ)*(N:ℝ)^L) (i : Fin 7) (j : Fin 10) (q : Fin 3 → ℕ) :
    q∈(actualPrimeBoxTuples N (fun _ : Fin 3 => L/10) (fun _ => 3*L/5)).filter
      (fun q => normalizedLog N L q∈chamber (1/W1Anchor j) (1/W1Target i) ∧ ∀ a,(q a).Coprime (d*N)) ↔
    label q∈orderedTriples (primeWindow (d*N) (cutoff Q d (W1Anchor j)) (cutoff Q d (W1Target i))) := by
  let a := 1/W1Anchor j
  let b := 1/W1Target i
  have hz (s : ℝ) : cutoff Q d s=(N:ℝ)^(L*(1/s)) := by
    rw [cutoff_eq_physical_power hd hQ]; congr 1; ring
  let P := primeWindow (d*N) ((N:ℝ)^(L*a)) ((N:ℝ)^(L*b))
  have ht : (label q∈orderedTriples P) ↔ (∀ k,q k∈P) ∧ q 2<q 1 ∧ q 1<q 0 := by
    simp only [label,orderedTriples,mem_filter,mem_product]
    constructor
    · rintro ⟨⟨h2,h1,h0⟩,h⟩
      exact ⟨fun k => by fin_cases k <;> assumption,h⟩
    · rintro ⟨hp,h⟩
      exact ⟨⟨hp 2,hp 1,hp 0⟩,h⟩
  rw [hz,hz]
  change _ ↔ label q∈orderedTriples P
  rw [ht,mem_filter]
  constructor
  · rintro ⟨hq,hu,hcop⟩
    have hpos := fun k => (mem_actualPrimeBoxTuples_iff.mp hq k).1.pos
    have hall := chamber_bounds hu
    refine ⟨?_,(lt_iff hN hL q hpos 2 1).mp hu.2.1,(lt_iff hN hL q hpos 1 0).mp hu.2.2.1⟩
    intro k
    have hkub : normalizedLog N L q k<b := by
      fin_cases k <;> first | exact hu.2.2.2 | exact hu.2.2.1.trans hu.2.2.2 |
        exact hu.2.1.trans (hu.2.2.1.trans hu.2.2.2)
    exact mem_primeWindow.mpr ⟨(mem_actualPrimeBoxTuples_iff.mp hq k).1,hcop k,
      (normalizedLog_window hN hL q hpos k a b).mp ⟨(hall k).1,hkub⟩⟩
  · rintro ⟨hp,h21,h10⟩
    have hp' (k : Fin 3) := mem_primeWindow.mp (hp k)
    have hpos := fun k => (hp' k).1.pos
    have hw (k : Fin 3) := (normalizedLog_window hN hL q hpos k a b).mpr (hp' k).2.2
    have data := P2AllW1FrozenReceiverFiniteAction.original_W1_parameters i j
    have hs : 0<W1Target i := by linarith [data.1]
    have ha : 1/5≤a := one_div_le_one_div_of_le (hs.trans_le data.2.1) data.2.2
    have hb : b≤1/2 := one_div_le_one_div_of_le (by norm_num) data.1
    refine ⟨mem_actualPrimeBoxTuples_iff.mpr (fun k => ?_),⟨(hw 2).1,
      (lt_iff hN hL q hpos 2 1).mpr h21,(lt_iff hN hL q hpos 1 0).mpr h10,(hw 0).2⟩,fun k => (hp' k).2.1⟩
    have hNcop : (q k).Coprime N := ((Nat.coprime_mul_iff_right.mp (hp' k).2.1).2)
    have hbox := (normalizedLog_window hN hL q hpos k (1/10) (3/5)).mp
      (show 1/10≤normalizedLog N L q k ∧ normalizedLog N L q k<3/5 by
        constructor <;> linarith [(hw k).1,(hw k).2])
    refine ⟨(hp' k).1,(hp' k).1.coprime_iff_not_dvd.mp hNcop,?_,?_⟩
    · convert hbox.1 using 1 <;> congr 1 <;> ring
    · convert hbox.2 using 1 <;> congr 1 <;> ring

theorem actual_integer_mass_eq {N d : ℕ} {Q L : ℝ} (hN : 1<N) (hd : 0<d) (hL : 0<L)
    (hQ : Q=(d:ℝ)*(N:ℝ)^L) (i : Fin 7) (j : Fin 10) :
    integerMass N Q d i j=mass N L d i j := by
  unfold integerMass mass
  rw [←sum_filter]
  symm
  apply sum_bij (fun q _ => label q)
  · exact fun q hq => (membership hN hd hL hQ i j q).mp hq
  · intro q hq r hr h
    have h0 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) h
    have h1 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h
    have h2 := congrArg (fun t : ℕ × ℕ × ℕ => t.1) h
    funext k; fin_cases k <;> assumption
  · rintro ⟨a,b,c⟩ ht
    refine ⟨![c,b,a],(membership hN hd hL hQ i j _).mpr ht,rfl⟩
  · intro q hq
    have hh : d*q 0*q 1*q 2=d*q 2*q 1*q 0 := by ring
    simp only [label,height,hh]

end
end ImbalancedChen.Part5OriginalH430W1PhysicalRoughDictionary
