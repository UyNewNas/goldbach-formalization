import ImbalancedChen.P5ZU1011OriginalW16AttachedWellSupport
import ImbalancedChen.Part3ActualWResidualCompletion

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Actual original W16 four-prime caller of the existing repaired W program.
The residual inputs are primitive original well support at R and residual
rough primes below the actually constructed Z. Original four-prefix square
support, late-slot bounds, initialized capacities and positive natural
factors are derived here. No desired factorization, failure-free run,
selected remainder support, analytic monomial or count bound is a premise.
The already proved P3 residual completion program is reused unchanged.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16NativeCompletion
noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank U1011OriginalSixteenArithmeticProducts
open U1011OriginalW16NativeInitialization U1011OriginalW16AttachedWellSupport
open P5U1011JointOverlap
open Part3.ActualWThreeCapacityRun Part3.ActualWResidualCompletion
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation
open scoped BigOperators

theorem native_initial_bounded {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (he : TypedEligible wPolicy (coordinates N t))
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) :
    Bounded (fun n : ℕ => (n:ℝ)) A ((N:ℝ)^(2*theta (coordinates N t)-1))
      ((N:ℝ)^(1-theta (coordinates N t)-2*buffer (coordinates N t))/A)
        (initialBins A (firstThree t)) := by
  obtain ⟨hB,hC,hcapacity,hseed,hrun⟩ := actual_W_first_two_and_run hN ht he A hA hAupper []
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hApos : 0<A := zero_lt_one.trans_le hA
  have hAC : A*((N:ℝ)^(1-theta (coordinates N t)-2*buffer (coordinates N t))/A)=
      (N:ℝ)^(1-theta (coordinates N t)-2*buffer (coordinates N t)) := by
    field_simp [hApos.ne'] <;> ring
  have hc := actual_W_critical_intervals hN ht he
  have hs : actualDwellSupport
      (A*((N:ℝ)^(1-theta (coordinates N t)-2*buffer (coordinates N t))/A)) [slots t 1] := by
    intro i hi
    have hi0 : i=0 := by simp only [List.length_singleton] at hi; omega
    subst i
    simpa only [hAC,List.take_zero,List.map_nil,List.prod_nil,List.getElem_cons_zero,one_mul]
      using hc.2.1
  obtain ⟨hprod,hleft,hright⟩ := actualTwoCapacityFactors_correct hA hC [slots t 1] hs
  have hfirst : (slots t 0:ℝ)≤(N:ℝ)^(2*theta (coordinates N t)-1) := hc.1.trans
    (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith [(buffer_bounds _ he).1]))
  exact ⟨by simpa [initialBins,firstThree,wp,actualTwoCapacityFactors,actualNatList_cast_prod] using hleft,
    by simpa [initialBins,firstThree,wp] using hfirst,
    by simpa [initialBins,firstThree,wp,actualTwoCapacityFactors,actualNatList_cast_prod] using hright⟩

/-- The actual unread specified primes and residual rough primes all lie
below the original W late-slot capacity. Their original labels/order are
kept; no sorting or cross-owner reassignment is used. -/
theorem native_unread_slots {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (he : TypedEligible wPolicy (coordinates N t))
    (tail : List ℕ)
    (hrough : ∀ q ∈ tail, Nat.Prime q ∧ (q:ℝ)<(N:ℝ)^cutoffExponent (coordinates N t)) :
    ∀ q ∈ slots t 2 :: slots t 3 :: tail, (0:ℝ)<q ∧
      (q:ℝ)≤(N:ℝ)^(actualSelectedSubproductUpper 1 (theta (coordinates N t))-
        (2*theta (coordinates N t)-1)-buffer (coordinates N t)) := by
  have hlate := (actual_W_critical_intervals hN ht he).2.2.2
  have hZ := (native_W_cutoff_legal hN ht he).2.1
  have h32 : (slots t 3:ℝ)≤slots t 2 := by
    exact_mod_cast ((slots_strictAnti ht) (by norm_num : (2:Fin 4)<3)).le
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨by exact_mod_cast slots_pos ht 2,hlate⟩
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨by exact_mod_cast slots_pos ht 3,h32.trans hlate⟩
    · obtain ⟨hp,hsmall⟩ := hrough q hq
      exact ⟨by exact_mod_cast hp.pos,hsmall.le.trans (hZ.trans (h32.trans hlate))⟩

/-- Complete NATURAL original W16 factors at their actual four-prime
point. Both true outcomes are retained: original bounded capacities, or
an enlarged middle in the buffered original critical interval. -/
theorem actual_W16_complete_factors {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (he : TypedEligible wPolicy (coordinates N t))
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ)
    (hresidual : actualDwellSupport ((N:ℝ)^residualExponent (coordinates N t)) tail)
    (hrough : ∀ q ∈ tail, Nat.Prime q ∧ (q:ℝ)<(N:ℝ)^cutoffExponent (coordinates N t)) :
    let v := coordinates N t
    let B := (N:ℝ)^(2*theta v-1)
    let C := (N:ℝ)^(1-theta v-2*buffer v)/A
    let D := (N:ℝ)^(theta v-2*buffer v)
    let initial := initialBins A (firstThree t)
    let input := slots t 2 :: slots t 3 :: tail
    let out := complete (fun n : ℕ => (n:ℝ)) A B C initial input
    Trace initial input out ∧ out.left.prod*out.middle.prod*out.right.prod=fullPrefix t*tail.prod ∧
      (0<out.left.prod ∧ 0<out.middle.prod ∧ 0<out.right.prod) ∧
      (Bounded (fun n : ℕ => (n:ℝ)) A B C out ∨
        (B<wp (fun n : ℕ => (n:ℝ)) out.middle ∧
          wp (fun n : ℕ => (n:ℝ)) out.middle≤
            (N:ℝ)^(actualSelectedSubproductUpper 1 (theta v)-buffer v) ∧
          wp (fun n : ℕ => (n:ℝ)) out.left≤A ∧
          wp (fun n : ℕ => (n:ℝ)) out.right≤D/(A*wp (fun n : ℕ => (n:ℝ)) out.middle))) := by
  let v := coordinates N t
  let B := (N:ℝ)^(2*theta v-1)
  let C := (N:ℝ)^(1-theta v-2*buffer v)/A
  let D := (N:ℝ)^(theta v-2*buffer v)
  let U := (N:ℝ)^(actualSelectedSubproductUpper 1 (theta v)-(2*theta v-1)-buffer v)
  let initial := initialBins A (firstThree t)
  let input := slots t 2 :: slots t 3 :: tail
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := zero_lt_one.trans hn
  have hinit := native_initial_bounded hN ht he A hA hAupper
  have hpositive : Positive (fun n : ℕ => (n:ℝ)) initial := initialBins_positive A (firstThree t) (by
    intro i
    fin_cases i
    · simpa [firstThree] using slots_pos ht 0
    · simpa [firstThree] using slots_pos ht 1
    · simpa [firstThree] using slots_pos ht 2)
  have hslots := native_unread_slots hN ht he tail hrough
  obtain ⟨hB,hC,hcapacity,hseed,hrun⟩ := actual_W_first_two_and_run hN ht he A hA hAupper tail
  have hs : total (fun n : ℕ => (n:ℝ)) initial=wp (fun n : ℕ => (n:ℝ)) [slots t 0,slots t 1] := by
    simpa [wp,initial] using hseed
  have hfull : PrefixSquareBound (fun n : ℕ => (n:ℝ)) D ([slots t 0,slots t 1]++input) := by
    simpa [D,input,specified] using native_attached_well_support hN ht he tail hresidual
  obtain ⟨htrace,hprod,hcases⟩ := complete_correct (fun n : ℕ => (n:ℝ)) (U := U)
    (zero_lt_one.trans_le hA) hinit hpositive hslots hs hfull
  have hpos := trace_positive (fun n : ℕ => (n:ℝ)) htrace hpositive
    (fun q hq => (hslots q hq).1)
  have hnat : (complete (fun n : ℕ => (n:ℝ)) A B C initial input).left.prod*
      (complete (fun n : ℕ => (n:ℝ)) A B C initial input).middle.prod*
      (complete (fun n : ℕ => (n:ℝ)) A B C initial input).right.prod=fullPrefix t*tail.prod := by
    have hh : (((complete (fun n : ℕ => (n:ℝ)) A B C initial input).left.prod*
        (complete (fun n : ℕ => (n:ℝ)) A B C initial input).middle.prod*
        (complete (fun n : ℕ => (n:ℝ)) A B C initial input).right.prod:ℕ):ℝ)=
        ((fullPrefix t*tail.prod:ℕ):ℝ) := by
      simpa [total,wp,actualNatList_cast_prod,input,fullPrefix,Fin.prod_univ_succ,
        List.prod_append,Nat.cast_mul,mul_assoc] using hprod
    exact_mod_cast hh
  have hnatpos : 0<(complete (fun n : ℕ => (n:ℝ)) A B C initial input).left.prod ∧
      0<(complete (fun n : ℕ => (n:ℝ)) A B C initial input).middle.prod ∧
      0<(complete (fun n : ℕ => (n:ℝ)) A B C initial input).right.prod := by
    simpa only [Positive,wp,actualNatList_cast_prod,Nat.cast_pos] using hpos
  refine ⟨htrace,hnat,hnatpos,?_⟩
  rcases hcases with hbounded | ⟨hlo,hhi,hleft,hright⟩
  · exact Or.inl hbounded
  · refine Or.inr ⟨hlo,?_,hleft,hright⟩
    have hBU : B*U=(N:ℝ)^(actualSelectedSubproductUpper 1 (theta v)-buffer v) := by
      dsimp [B,U]
      rw [←Real.rpow_add hp]
      congr 1
      ring
    exact hhi.trans_eq hBU

end
end ImbalancedChen.P5Z.U1011OriginalW16NativeCompletion
