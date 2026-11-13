import ImbalancedChen.P1OriginalSingletonOneLongProfile
import ImbalancedChen.P5OriginalOneLongActualChartE5

/-!
SOURCE ONLY, NOT COMPILED OR KERNEL ACCEPTED.

The coefficient of the modulus is never used as a long-slot sequence.
The only short coefficient below is the literal product of the OTHER
ordered HB positions, with their original real Mobius cutoff. The long
interval keeps the original complete-product cap exactly.
-/
namespace ImbalancedChen.P1OriginalSingletonOneLongFiniteE5
noncomputable section
open Classical
open scoped BigOperators
open P5Z.ActualRoughHeathBrownWords P5Z.HBRightClosedDyadicRoles
open P5Z.ActualHBDyadicProductWindow P5Z.ActualHBPostModulusLogCutoff
open P5Z.OrderedFactorTupleRectangleReindex
open P5Z.ActualLowerNormalizedAtlasOccurrence P5Z.PerGroupIntegerHBAtlasPushforward
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.IndependentPrimeSourceWordDictionary
open P1OriginalSingletonOneLongRectangle P1OriginalSingletonOneLongFibres
open P1OriginalSingletonOneLongProfile
open OriginalOneLongFiniteBrun OriginalOneLongSmoothAbel OriginalOneLongE5FiniteBudget
open OriginalOneLongActualChartE5 OriginalOneLongModulusMeans
open Part3.RoughSlotCharacterLift20261026b Part3.TwoLongDivisorAxisClosure

/-- This includes the prime equal to z. It is the actual strict rough
projector, not a different half-open prime alphabet. -/
theorem strict_rough_dictionary {z : ℝ} (hz : 0≤z) (n : ℕ) :
    Part3.roughOneSlot z n=(actualRough (chartDivisor (smallPrimes z)) n : ℂ) := by
  rw [roughOneSlot_eq_coprime_indicator hz]
  simp only [actualRough,chartDivisor,smallProduct]
  split_ifs <;> norm_num

/-- Count and exact coprime mean are the two terms of the SAME original
kernel, including the nonprimitive case. No progression bound is used. -/
theorem actual_count_mean_dictionary (q N m n : ℕ) :
    PrimeProducts.MellinInsertion20261028.residueKernel q N (m*n)=
      ((actualCount q N m n-actualMean q m n : ℝ) : ℂ) := by
  rw [residueKernel_real]
  unfold actualCount actualMean
  by_cases h : (m*n).Coprime q <;> simp [h]

def shortCoefficient {j : ℕ} (z y : ℝ) (a : Fin (2*(j+1)))
    (v : ShortIndex a→ℕ) : ℂ :=
  ∏ i : ShortIndex a,actual z y (rowRoles j i.val) (v i)

theorem hbSlots_insert (z y : ℝ) (j : ℕ) (a : Fin (2*(j+1)))
    (v : ShortIndex a→ℕ) (n : ℕ) :
    hbSlots z (fun _=>y) (rowRoles j) (insert a v n)=
      shortCoefficient z y a v*actual z y (rowRoles j a) n := by
  have hs : shortCoefficient z y a v=
      ∏ i∈Finset.univ.erase a,actual z y (rowRoles j i) (insert a v n i) := by
    unfold shortCoefficient
    apply Finset.prod_bij (fun i _=>i.val)
    · intro i hi
      exact Finset.mem_erase.mpr ⟨i.property,Finset.mem_univ _⟩
    · intro i hi k hk hik
      exact Subtype.ext hik
    · intro i hi
      exact ⟨⟨i,(Finset.mem_erase.mp hi).1⟩,Finset.mem_univ _,rfl⟩
    · intro i hi
      simp only [insert_away]
  rw [hs]
  simpa only [hbSlots,insert_at] using
    (Finset.prod_erase_mul Finset.univ
      (fun i=>actual z y (rowRoles j i) (insert a v n i)) (Finset.mem_univ a)).symm

theorem profileError_interval (L K q N m p : ℕ) (F : ℝ→ℂ) (u : ℝ) :
    profileError L K q N m p F u=
      ∑ n∈Finset.Ico L (L+K),F ((n : ℝ)/u)*actualCoefficient q N m p n := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left,profileError]

def longFibre (kap : ℝ) (B N cj K : ℕ) (kap0 : ℝ) {j : ℕ}
    (a : Fin (2*(j+1))) (v : ShortIndex a→ℕ) (U : ℕ)
    (Q : Finset ℕ) (rho : ℕ→ℂ) : ℂ :=
  ∑ n∈fibreInterval (2*N) (shortProduct v) U,
    shortCoefficient (beforeHBCutoff K [cj]) (hbCutoff cj) a v*
      actual (beforeHBCutoff K [cj]) (hbCutoff cj) (rowRoles j a) n*
      (scalarProfile kap B N cj kap0 (shortProduct v*n) : ℂ)*
      wordKernel Q rho N [shortProduct v*n]

/-- The exact finite E5 input for one ACTUAL ordered short vector.
The source m*n, original rho, original reciprocal group log and strict
rough mask are unchanged on both sides. The interval can be empty. -/
theorem longFibre_eq_actual_profileError
    (kap : ℝ) (B N cj K : ℕ) (kap0 : ℝ) {j : ℕ}
    (a : Fin (2*(j+1))) (v : ShortIndex a→ℕ) (U : ℕ)
    (hm : 0<shortProduct v) (hU : 0<U)
    (hz : 0≤beforeHBCutoff K [cj])
    (hr : rowRoles j a=.one ∨ rowRoles j a=.logarithm)
    (Q : Finset ℕ) (rho : ℕ→ℂ) :
    longFibre kap B N cj K kap0 a v U Q rho=
      shortCoefficient (beforeHBCutoff K [cj]) (hbCutoff cj) a v*
        ∑ q∈Q,rho q*
          profileError (U+1) (fibreWidth (2*N) (shortProduct v) U) q N (shortProduct v)
            (chartDivisor (smallPrimes (beforeHBCutoff K [cj])))
            (longProfile kap B N cj kap0 (shortProduct v) U
              (decide (rowRoles j a=.logarithm))) (U : ℝ) := by
  simp only [longFibre,wordKernel,List.prod_cons,List.prod_nil,mul_one]
  simp_rw [profileError_interval]
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hb := (mem_fibreInterval hm).mp hn
  apply Finset.sum_congr rfl
  intro q hq
  have hp := actual_long_profile kap B N cj kap0
    (beforeHBCutoff K [cj]) (hbCutoff cj) (shortProduct v) U n hU hb.1 hb.2.1
    (rowRoles j a) hr
  calc
    _=shortCoefficient (beforeHBCutoff K [cj]) (hbCutoff cj) a v*
        (actual (beforeHBCutoff K [cj]) (hbCutoff cj) (rowRoles j a) n*
          (scalarProfile kap B N cj kap0 (shortProduct v*n) : ℂ))*
        (rho q*PrimeProducts.MellinInsertion20261028.residueKernel q N (shortProduct v*n)) := by ring
    _=_ := by
      rw [hp,strict_rough_dictionary hz,actual_count_mean_dictionary]
      simp only [actualCoefficient,Complex.ofReal_mul]
      ring

/-- The complete-product cutoff is used BEFORE any one-dimensional E5.
In particular, the original closed endpoint 2N is not smoothed away. -/
theorem occurrenceAtom_short_fibres
    (kap : ℝ) (hk : kap<1) (B N cj K : ℕ) (kap0 : ℝ) (j : ℕ)
    (bs : Fin (2*(j+1))→Block) (a : Fin (2*(j+1))) (k : ℕ)
    (ha : bs a=.dyadic k) (Q : Finset ℕ) (rho : ℕ→ℂ) :
    (∑ n∈rectangle bs,
      hbSlots (beforeHBCutoff K [cj]) (fun _=>hbCutoff cj) (rowRoles j) n*
        (integerProfile kap B N cj kap0 n : ℂ)*wordKernel Q rho N [completeProduct n])=
      ∑ v∈shortBox bs a,longFibre kap B N cj K kap0 a v (2^k) Q rho := by
  have hcap : (∑ n∈rectangle bs,
      hbSlots (beforeHBCutoff K [cj]) (fun _=>hbCutoff cj) (rowRoles j) n*
        (integerProfile kap B N cj kap0 n : ℂ)*wordKernel Q rho N [completeProduct n])=
      ∑ n∈(rectangle bs).filter (fun n=>completeProduct n≤2*N),
        hbSlots (beforeHBCutoff K [cj]) (fun _=>hbCutoff cj) (rowRoles j) n*
          (integerProfile kap B N cj kap0 n : ℂ)*wordKernel Q rho N [completeProduct n] := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : completeProduct n≤2*N
    · simp [h]
    · have hz : integerProfile kap B N cj kap0 n=0 := by
        by_contra hp
        exact h (scalarProfile_support kap hk B N cj kap0 hp)
      simp [h,hz]
  rw [hcap,sum_rectangle_capped_short_fibres]
  apply Finset.sum_congr rfl
  intro v hv
  rw [ha,dyadic_fibre_exact _ _ _ (short_product_pos bs a hv)]
  unfold longFibre
  apply Finset.sum_congr rfl
  intro n hn
  simp only [hbSlots_insert,integerProfile,product_insert]

/-- Chosen ONCE from the actual B=6 global supplier, before any N,
modulus channel, HB row, selected position or short vector. -/
def profileConstant : ℝ := Classical.choose (longProfile_uniform_C1 6)

theorem profileConstant_nonneg : 0≤profileConstant :=
  (Classical.choose_spec (longProfile_uniform_C1 6)).1

theorem profileConstant_C1 (kap : ℝ) (N cj : ℕ) (kap0 : ℝ) (m U : ℕ)
    (hN : 0<N) (hm : 0<m) (hU : 0<U) (hUc : U≤2*N) (b : Bool) (x : ℝ) :
    ‖longProfile kap 6 N cj kap0 m U b x‖+
      ‖deriv (longProfile kap 6 N cj kap0 m U b) x‖≤
        profileConstant*profileHeight N^73 := by
  simpa only [profileConstant,show 6*12+1=73 by norm_num] using
    (Classical.choose_spec (longProfile_uniform_C1 6)).2 kap N cj kap0 m U hN hm hU hUc b x

/-- One genuine fibre, supplied with the proved GLOBAL C1 envelope.
There is no hAmp/hDer/profileError estimate in the hypotheses. The
primitive finite prime cap and harmonic hypotheses are supplied uniformly
from the actual chart in the later restoration theorem. -/
theorem actual_fibre_finite
    (kap : ℝ) (N cj K D jBrun : ℕ) (kap0 : ℝ) {j : ℕ}
    (a : Fin (2*(j+1))) (v : ShortIndex a→ℕ) (U : ℕ)
    (Q : Finset ℕ) (rho : ℕ→ℂ) (Rrho zEnvelope H : ℝ)
    (hN : 0<N) (hm : 0<shortProduct v) (hU : 0<U) (hUc : U≤2*N)
    (hz : 0≤beforeHBCutoff K [cj]) (hzEnv : 1≤zEnvelope)
    (hcut : beforeHBCutoff K [cj]≤zEnvelope)
    (hH : Part3.BrunFactorialRecurrenceE1.chartHarmonic
      (smallPrimes (beforeHBCutoff K [cj]))≤H)
    (hD : 1≤D) (hQ : Q⊆Finset.Ioc 0 D) (hcop : ∀ q∈Q,N.Coprime q)
    (hR : 0≤Rrho) (hrho : ∀ q∈Q,‖rho q‖≤Rrho)
    (hr : rowRoles j a=.one ∨ rowRoles j a=.logarithm) :
    ‖longFibre kap 6 N cj K kap0 a v U Q rho‖≤
        ‖shortCoefficient (beforeHBCutoff K [cj]) (hbCutoff cj) a v‖*
          (2*profileConstant*profileHeight N^73)*Rrho*logBudget D^4*
            (10*zEnvelope^(2*jBrun+1)*(D : ℝ)+
              2*(H^(2*jBrun+1)/(Nat.factorial (2*jBrun+1) : ℝ))*
                (fibreWidth (2*N) (shortProduct v) U : ℝ)) := by
  let z := beforeHBCutoff K [cj]
  let P := smallPrimes z
  let Z := max 1 ⌊z⌋₊
  let F := longProfile kap 6 N cj kap0 (shortProduct v) U
    (decide (rowRoles j a=.logarithm))
  let E := profileConstant*profileHeight N^73
  have hE : 0≤E := by
    dsimp [E,profileHeight]
    have := Real.log_nonneg (show (1 : ℝ)≤8*(N : ℝ)+8 by nlinarith [Nat.cast_nonneg N])
    have := profileConstant_nonneg
    positivity
  have hnorm (x : ℝ) : ‖F x‖+‖deriv F x‖≤E := by
    simpa only [F,E] using profileConstant_C1 kap N cj kap0 (shortProduct v) U hN hm hU hUc
      (decide (rowRoles j a=.logarithm)) x
  have hZ : 1≤Z := le_max_left _ _
  have hcap : ∀ p∈P,p≤Z := by
    intro p hp
    exact (Nat.le_floor ((mem_smallPrimes hz).mp hp).2).trans (le_max_right _ _)
  have hZE : (Z : ℝ)≤zEnvelope := by
    rw [show (Z : ℝ)=max 1 (⌊z⌋₊ : ℝ) by simp [Z]]
    exact max_le hzEnv ((Nat.floor_le hz).trans hcut)
  have hfinite := actual_chart_one_long_finite (U+1)
    (fibreWidth (2*N) (shortProduct v) U) N D 0 jBrun Z Q {shortProduct v} P rho
    (fun _=>1) F (U : ℝ) E E 1 zEnvelope H Rrho 1
    (fun p hp=>smallPrimes_prime hp) hZ hcap hZE hH hD hQ hcop hR
    (by intro q hq; simpa using hrho q hq) (by simp) (by exact_mod_cast hU)
    hE hE (by norm_num) ((longProfile_smooth kap 6 N cj kap0 (shortProduct v) U hU _).differentiable (by simp))
    (fun x=>by linarith [hnorm x,norm_nonneg (deriv F x)])
    (fun x=>by linarith [hnorm x,norm_nonneg (F x)])
    (by simpa using (Nat.cast_le.mpr (fibre_width_le (2*N) (shortProduct v) U) :
      (fibreWidth (2*N) (shortProduct v) U : ℝ)≤U))
  have hzEnv0 : 0≤zEnvelope := zero_le_one.trans hzEnv
  have hH0 : 0≤H := (show 0≤Part3.BrunFactorialRecurrenceE1.chartHarmonic P by
    unfold Part3.BrunFactorialRecurrenceE1.chartHarmonic; positivity).trans hH
  have hbudget := physicalBudget_le_common_log D 0
    (fibreWidth (2*N) (shortProduct v) U) (zEnvelope^(2*jBrun+1))
    (H^(2*jBrun+1)/(Nat.factorial (2*jBrun+1) : ℝ)) Rrho hD
    (by positivity : 0≤zEnvelope^(2*jBrun+1))
    (by positivity) hR
  rw [longFibre_eq_actual_profileError kap 6 N cj K kap0 a v U hm hU hz hr,norm_mul]
  simp only [Finset.sum_singleton,one_mul] at hfinite
  have hb := hfinite.trans (mul_le_mul_of_nonneg_left hbudget
    (show 0≤E+E by positivity))
  have hh := mul_le_mul_of_nonneg_left hb
    (norm_nonneg (shortCoefficient z (hbCutoff cj) a v))
  convert hh using 1 <;> dsimp [E,z,P,F] <;> norm_num <;> ring

end
end ImbalancedChen.P1OriginalSingletonOneLongFiniteE5
