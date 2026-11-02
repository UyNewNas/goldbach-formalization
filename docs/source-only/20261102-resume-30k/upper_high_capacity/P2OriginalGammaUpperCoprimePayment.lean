import ImbalancedChen.P2OriginalGammaUpperLowRankConsumer
import ImbalancedChen.P4BPrimorialDivisorEnvelope
import ImbalancedChen.ActualUpperDensityAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The full original U5 Gamma costing source, with its mother LIST and all
unit/nonunit quotient labels, receives the SAME actual sign-sensitive upper
rho. The primorial envelope pays its complete-product coprime correction,
including arbitrarily high rough-modulus ranks. No fullK, J bound, PP,
polynomial modulus range, or replacement lower-W coefficient is assumed.

The final error is eta * sourceJ on H_N's normalization. Thus an eventual
sourceJ bound is still owed, but the exact-coprime correction needs no new
analytic licence or division by that source mass. Outer rank199 is used
ONLY for the number of terms in this prime-divisor union, never as modulus
square support or a Medium monomial licence.
-/
namespace ImbalancedChen.P2OriginalGammaUpperCoprimePayment
noncomputable section
open Filter Topology Wu2008DoubleSieve
open scoped Classical BigOperators
open P2OriginalU5ExactNormalizedSource P2OriginalGammaUpperLowRankConsumer
open P2OriginalU5WholeGroupCapacity
open P2TwentyOneUnsiftedArithmeticSource (product)
open P2TwentyOneMaskedTailFloor (completeWord)
open P5OriginalU5CausalFinite (pairSupport)
open P4BPrimorialDivisorEnvelope

private theorem list_finset_swap {α β : Type*} (l : List α) (s : Finset β)
    (f : α → β → ℝ) :
    (l.map (fun a => ∑ b ∈ s, f a b)).sum = ∑ b ∈ s, (l.map (fun a => f a b)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih,Finset.sum_add_distrib]

theorem sourceTest_mono (N : ℕ) (t : ℕ × ℕ) (F G : ℕ → ℝ)
    (h : ∀ cs, ∀ x ∈ rootLabels N t cs,
      F (product (t.1*t.2) x) ≤ G (product (t.1*t.2) x)) :
    sourceTest N t F ≤ sourceTest N t G := by
  unfold sourceTest
  apply secondFunctionalMother_list_sum_mono
  intro i _hi
  apply secondFunctionalMother_list_sum_mono
  intro cs _hcs
  exact Finset.sum_le_sum (fun x hx => h cs x hx)

theorem sourceTest_const_mul (N : ℕ) (t : ℕ × ℕ) (c : ℝ) (F : ℕ → ℝ) :
    sourceTest N t (fun m => c*F m) = c*sourceTest N t F := by
  simp only [sourceTest,← Finset.mul_sum,List.sum_map_mul_left]

theorem sourceTest_const (N : ℕ) (t : ℕ × ℕ) (c : ℝ) :
    sourceTest N t (fun _ => c) = c*sourceTest N t (fun _ => 1) := by
  simpa only [mul_one] using sourceTest_const_mul N t c (fun _ => 1)

theorem sourceMass_nonneg (N : ℕ) (t : ℕ × ℕ) : 0 ≤ sourceTest N t (fun _ => 1) := by
  have h := sourceTest_mono N t (fun _ => 0) (fun _ => 1) (by intros; norm_num)
  simpa [sourceTest] using h

theorem sourceTest_finsetSum {α : Type*} (N : ℕ) (t : ℕ × ℕ)
    (s : Finset α) (F : α → ℕ → ℝ) :
    sourceTest N t (fun m => ∑ a ∈ s,F a m) = ∑ a ∈ s,sourceTest N t (F a) := by
  have hinner (cs : List ℕ) :
      (∑ x ∈ rootLabels N t cs, ∑ a ∈ s,F a (product (t.1*t.2) x)) =
        ∑ a ∈ s, ∑ x ∈ rootLabels N t cs,F a (product (t.1*t.2) x) := Finset.sum_comm
  simp only [sourceTest]
  simp_rw [hinner,list_finset_swap]

theorem sourceTest_abs_bound (N : ℕ) (t : ℕ × ℕ) (F : ℕ → ℝ) (M : ℝ)
    (h : ∀ cs, ∀ x ∈ rootLabels N t cs, |F (product (t.1*t.2) x)| ≤ M) :
    |sourceTest N t F| ≤ sourceTest N t (fun _ => 1)*M := by
  have hu := sourceTest_mono N t F (fun _ => M) (fun cs x hx => (abs_le.mp (h cs x hx)).2)
  have hl := sourceTest_mono N t (fun _ => -M) F (fun cs x hx => (abs_le.mp (h cs x hx)).1)
  rw [sourceTest_const] at hu hl
  apply abs_le.mpr
  constructor <;> nlinarith

def correction (N : ℕ) (t : ℕ × ℕ) (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) : ℝ :=
  ∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
    attachedUpperCoefficient nu r epsilon retain cap N q *
      ((sourceTest N t (fun m => if Nat.Coprime m q then 1 else 0) -
        sourceTest N t (fun _ => 1))/(Nat.totient q : ℝ))

def correctionKernel (D : Finset ℕ) (rho : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ q ∈ D, rho q*((if Nat.Coprime m q then 1 else 0)-1)/(Nat.totient q : ℝ)

theorem correction_eq_source (N : ℕ) (t : ℕ × ℕ) (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    correction N t nu r epsilon retain cap = sourceTest N t
      (correctionKernel (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N)) := by
  unfold correction correctionKernel
  rw [sourceTest_finsetSum]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [sourceTest_div,sourceTest_const_mul,sourceTest_sub]
  ring

/-- A list union preserves repeated prime occurrences and the empty word. -/
private theorem prime_list_union (ps : List ℕ) (q : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hp : ∀ p ∈ ps,Nat.Prime p) :
    (if Nat.Coprime ps.prod q then 0 else u) ≤
      (ps.map (fun p => if p ∣ q then u else 0)).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hpp := hp p (by simp)
      have iht := ih (fun a ha => hp a (List.mem_cons_of_mem p ha))
      have htail : 0 ≤ (ps.map (fun a => if a ∣ q then u else 0)).sum := by
        apply List.sum_nonneg
        intro a ha
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
        split_ifs <;> linarith
      by_cases hd : p ∣ q
      · have hn : ¬Nat.Coprime (p*ps.prod) q := by
          intro hc
          exact (hpp.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_left.mp hc).1) hd
        simp only [List.prod_cons,if_neg hn,List.map_cons,if_pos hd,List.sum_cons]
        linarith
      · have hc : Nat.Coprime p q := hpp.coprime_iff_not_dvd.mpr hd
        simpa only [List.prod_cons,Nat.coprime_mul_iff_left,hc,true_and,
          List.map_cons,if_neg hd,List.sum_cons,zero_add] using iht

/-- The bound comes from the true prime-divisible envelope, not from
counting all moduli. Its list rank is the OUTER source rank only. -/
theorem correctionKernel_le_prime_union (D : Finset ℕ) (rho : ℕ → ℝ)
    (ps : List ℕ) (hp : ∀ p ∈ ps,Nat.Prime p) :
    |correctionKernel D rho ps.prod| ≤
      (ps.map (fun p => ∑ q ∈ D,if p ∣ q then |rho q|/(Nat.totient q : ℝ) else 0)).sum := by
  calc
    _ ≤ ∑ q ∈ D,|rho q*((if Nat.Coprime ps.prod q then 1 else 0)-1)/(Nat.totient q : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ D,if Nat.Coprime ps.prod q then 0 else |rho q|/(Nat.totient q : ℝ) := by
      apply Finset.sum_congr rfl
      intro q _hq
      by_cases hc : Nat.Coprime ps.prod q <;>
        simp [hc,abs_div,abs_mul,abs_of_nonneg (Nat.cast_nonneg (Nat.totient q))]
    _ ≤ ∑ q ∈ D,(ps.map (fun p => if p ∣ q then |rho q|/(Nat.totient q : ℝ) else 0)).sum :=
      Finset.sum_le_sum (fun q _ => prime_list_union ps q _ (by positivity) hp)
    _ = _ := (list_finset_swap ps D _).symm

theorem actual_kernel_bound (C : ℝ) (hC : 0 < C)
    (henvelope : ∀ nu r epsilon : ℝ,0 < nu → 0 < r → epsilon^2 ≤ r →
      ∀ (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (N : ℕ),Even N → 2 ≤ N →
      ∀ p : ℕ,Nat.Prime p →
        (∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
          if p ∣ q then |attachedUpperCoefficient nu r epsilon retain cap N q|/(Nat.totient q : ℝ) else 0) ≤
          (C*(nu*r+1)*Real.log (N : ℝ))/((p : ℝ)-1))
    (nu r epsilon : ℝ) (hnu : 0 < nu) (hr : 0 < r) (heps : epsilon^2 ≤ r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (N : ℕ) (hEven : Even N) (hN : 2 ≤ N)
    (ps : List ℕ) (hp : ∀ p ∈ ps,Nat.Prime p) (H : ℝ) (hH : 1 < H)
    (hfloor : ∀ p ∈ ps,H ≤ (p : ℝ)) (hrank : ps.length ≤ 199) :
    |correctionKernel (attachedUpperModuli nu r epsilon retain cap N)
      (attachedUpperCoefficient nu r epsilon retain cap N) ps.prod| ≤
      199*C*(nu*r+1)*Real.log (N : ℝ)/(H-1) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1<N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  let A := C*(nu*r+1)*Real.log (N : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hterm (p : ℕ) (hpin : p ∈ ps) :
      (∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
        if p ∣ q then |attachedUpperCoefficient nu r epsilon retain cap N q|/(Nat.totient q : ℝ) else 0) ≤ A/(H-1) := by
    exact (henvelope nu r epsilon hnu hr heps retain cap N hEven hN p (hp p hpin)).trans
      (div_le_div_of_nonneg_left hA (by linarith) (by linarith [hfloor p hpin]))
  have hsum := secondFunctionalMother_list_sum_mono ps _ (fun _ => A/(H-1)) hterm
  have hlength : (ps.length : ℝ) ≤ 199 := by exact_mod_cast hrank
  calc
    _ ≤ _ := correctionKernel_le_prime_union _ _ ps hp
    _ ≤ (ps.map (fun _ => A/(H-1))).sum := hsum
    _ = (ps.length : ℝ)*(A/(H-1)) := by simp
    _ ≤ 199*(A/(H-1)) := mul_le_mul_of_nonneg_right hlength (div_nonneg hA (by linarith))
    _ = _ := by dsimp [A]; ring

/-- One constant and one source threshold precede ALL retention policies,
caps, genuine root pairs and original mother occurrences. No sourceJ bound. -/
theorem exists_original_Gamma_correction_bound :
    ∃ C : ℝ,0 < C ∧ ∀ nu r epsilon : ℝ,0 < nu → 0 < r → epsilon^2 ≤ r →
      ∀ᶠ N : ℕ in atTop,Even N →
      ∀ (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ),∀ t ∈ pairSupport N,
      |correction N t nu r epsilon retain cap| ≤
        sourceTest N t (fun _ => 1)*
          (199*C*(nu*r+1)*Real.log (N : ℝ)/((N : ℝ)^(1/200 : ℝ)-1)) := by
  obtain ⟨C,hC,henvelope⟩ := exists_actual_upper_prime_divisor_envelope
  refine ⟨C,hC,?_⟩
  intro nu r epsilon hnu hr heps
  filter_upwards [eventually_complete_word_capacity,eventually_ge_atTop (2 : ℕ)] with N hsource hN
  intro hEven retain cap t ht
  rw [correction_eq_source]
  apply sourceTest_abs_bound
  intro cs x hx
  have hdata := hsource t ht cs x hx
  rw [← hdata.1]
  apply actual_kernel_bound C hC henvelope nu r epsilon hnu hr heps retain cap N hEven hN
    (completeWord (t.1*t.2) x) (fun p hp => (hdata.2.1 p hp).1)
    ((N : ℝ)^(1/200 : ℝ))
  · apply Real.one_lt_rpow (by exact_mod_cast (show 1<N by omega))
    norm_num
  · exact fun p hp => (hdata.2.1 p hp).2
  · exact hdata.2.2

/-- On the original H_N normalization this is a vanishing relative
sourceJ error, uniform in the actual upper policy. sourceJ=0 is included.
This removes the coprime-mean replacement port, not the J or density bound. -/
theorem eventually_original_Gamma_normalized_correction
    (nu r epsilon : ℝ) (hnu : 0 < nu) (hr : 0 < r) (heps : epsilon^2 ≤ r)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,Even N →
      ∀ (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ),∀ t ∈ pairSupport N,
      |correction N t nu r epsilon retain cap / singularNormalization N| ≤ eta*sourceJ N t := by
  obtain ⟨C,hC,hfinite⟩ := exists_original_Gamma_correction_bound
  let B := 199*C*(nu*r+1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hTwin : 0 < twinPrimeConstant := twinPrimeConstant_pos
  have hdecay : Tendsto (fun N : ℕ => (2*B/twinPrimeConstant)*
      ((Real.log (N : ℝ))^2/(N : ℝ)^(1/200 : ℝ))) atTop (𝓝 0) := by
    have h := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ)<1/200)).tendsto_div_nhds_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def,Real.rpow_two,mul_zero] using h.const_mul (2*B/twinPrimeConstant)
  have hlarge : ∀ᶠ N : ℕ in atTop,(2 : ℝ) ≤ (N : ℝ)^(1/200 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/200)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hfinite nu r epsilon hnu hr heps,hlarge,
    hdecay.eventually (gt_mem_nhds heta),eventually_ge_atTop (2 : ℕ)] with N hfin hpow hsmall hN
  intro hEven retain cap t ht
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1<N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  have hS : 0 < singularSeries N := singularSeries_pos N
  have hnorm : 0 < singularNormalization N := by
    unfold singularNormalization
    positivity
  have hJ : 0 ≤ sourceJ N t := mul_nonneg (div_nonneg hlog.le hNp.le) (sourceMass_nonneg N t)
  have hfiniteN := hfin hEven retain cap t ht
  have hden : 0 < (N : ℝ)^(1/200 : ℝ)-1 := by linarith
  have hnormalized : |correction N t nu r epsilon retain cap / singularNormalization N| ≤
      sourceJ N t*(B*(Real.log (N : ℝ))^2/
        (singularSeries N*((N : ℝ)^(1/200 : ℝ)-1))) := by
    rw [abs_div,abs_of_pos hnorm]
    apply (div_le_div_of_nonneg_right hfiniteN hnorm.le).trans_eq
    dsimp [sourceJ,B,singularNormalization]
    field_simp [hNp.ne',hlog.ne',hS.ne',hden.ne']
    <;> ring
  have hbudget : B*(Real.log (N : ℝ))^2/
      (singularSeries N*((N : ℝ)^(1/200 : ℝ)-1)) ≤
        (2*B/twinPrimeConstant)*((Real.log (N : ℝ))^2/(N : ℝ)^(1/200 : ℝ)) := by
    have hd : twinPrimeConstant*((N : ℝ)^(1/200 : ℝ)/2) ≤
        singularSeries N*((N : ℝ)^(1/200 : ℝ)-1) := by
      apply mul_le_mul (twinPrimeConstant_le_singularSeries N) (by linarith)
        (by positivity) hS.le
    calc
      _ ≤ B*(Real.log (N : ℝ))^2/(twinPrimeConstant*((N : ℝ)^(1/200 : ℝ)/2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hd
      _ = _ := by
        field_simp [hTwin.ne', (Real.rpow_pos_of_pos hNp (1/200 : ℝ)).ne']
        <;> ring
  calc
    _ ≤ _ := hnormalized
    _ ≤ sourceJ N t*((2*B/twinPrimeConstant)*
        ((Real.log (N : ℝ))^2/(N : ℝ)^(1/200 : ℝ))) := mul_le_mul_of_nonneg_left hbudget hJ
    _ ≤ sourceJ N t*eta := mul_le_mul_of_nonneg_left hsmall.le hJ
    _ = eta*sourceJ N t := mul_comm _ _

/-- The unit/nonunit quotient split is exact after centering and after
the same upper rho has been attached. No surface is deleted to pay it. -/
theorem correction_unit_nonunit (N : ℕ) (t : ℕ × ℕ) (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    correction N t nu r epsilon retain cap =
      unitTest N t (correctionKernel (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N))+
      nonunitTest N t (correctionKernel (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N)) := by
  rw [correction_eq_source,sourceTest_unit_nonunit]

end
end ImbalancedChen.P2OriginalGammaUpperCoprimePayment
