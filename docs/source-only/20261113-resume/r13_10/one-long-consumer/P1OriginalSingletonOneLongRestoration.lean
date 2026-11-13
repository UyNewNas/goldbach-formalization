import ImbalancedChen.P1OriginalSingletonOneLongFiniteE5

/-! SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.
This is finite restoration on the actual ordered rectangle. In particular,
the growing Brun gap is charged to sum(width), not to U times a new,
assumed coefficient mass. The modulus coefficient remains outside every
short vector and is common to its count and exact coprime mean. -/
namespace ImbalancedChen.P1OriginalSingletonOneLongRestoration
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
open P1OriginalSingletonOneLongProfile P1OriginalSingletonOneLongFiniteE5
open OriginalOneLongModulusMeans

theorem short_index_card {r : ℕ} (a : Fin r) : Fintype.card (ShortIndex a)=r-1 := by
  let e : ShortIndex a ≃ ↥(Finset.univ.erase a) :=
    { toFun := fun i=>⟨i.val,Finset.mem_erase.mpr ⟨i.property,Finset.mem_univ _⟩⟩
      invFun := fun i=>⟨i.val,(Finset.mem_erase.mp i.property).1⟩
      left_inv := fun i=>Subtype.ext rfl
      right_inv := fun i=>Subtype.ext rfl }
  calc
    _=Fintype.card ↥(Finset.univ.erase a) := Fintype.card_congr e
    _=r-1 := by simp

theorem height_one_le (N : ℕ) : 1≤profileHeight N := by
  have h := Real.log_nonneg (show (1 : ℝ)≤8*(N : ℝ)+8 by nlinarith [Nat.cast_nonneg N])
  dsimp [profileHeight]
  linarith

theorem actual_role_norm_le_height (N : ℕ) (z y : ℝ) (r : Role) (n : ℕ)
    (hn : 0<n) (hc : n≤4*N) : ‖actual z y r n‖≤profileHeight N := by
  have hL := height_one_le N
  cases r with
  | mobius => exact (roughMuTrunc_norm_le z y n).trans hL
  | one => exact (Part3.roughOneSlot_norm_le z n).trans hL
  | logarithm =>
    have hn1 : (1 : ℝ)≤n := by exact_mod_cast hn
    have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
    have hl0 : 0≤Real.log (n : ℝ) := Real.log_nonneg hn1
    have hlo : Real.log (n : ℝ)≤Real.log (8*(N : ℝ)+8) :=
      Real.log_le_log hn0 (by exact_mod_cast (hc.trans (by omega : 4*N≤8*N+8)))
    calc
      _=|Real.log (n : ℝ)|*‖Part3.roughOneSlot z n‖ := by
        simp only [actual,roughLog,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      _≤Real.log (n : ℝ)*1 := by
        rw [abs_of_nonneg hl0]
        exact mul_le_mul_of_nonneg_left (Part3.roughOneSlot_norm_le z n) hl0
      _≤profileHeight N := by dsimp [profileHeight]; linarith

/-- The scale bound is derived from one actual nonzero source profile.
It is uniform over the ENTIRE ordered short box, even where that profile
later vanishes or the same short product occurs several times. -/
theorem actual_raw_product_cap (kap : ℝ) (hk : kap<1) (B N cj : ℕ) (kap0 : ℝ)
    {r : ℕ} (bs : Fin r→Block)
    (hactive : ∃ n∈rectangle bs,integerProfile kap B N cj kap0 n≠0) :
    (∏ i,lower (bs i))≤2*N := by
  obtain ⟨n,hn,hp⟩ := hactive
  apply (show (∏ i,lower (bs i))≤completeProduct n from ?_).trans
    (scalarProfile_support kap hk B N cj kap0 hp)
  exact Finset.prod_le_prod (fun i hi=>Nat.zero_le _)
    (fun i hi=>(owns_bounds ((mem_rectangle bs n).mp hn i)).1)

theorem lower_le_raw {r : ℕ} (bs : Fin r→Block) (a : Fin r) :
    lower (bs a)≤∏ i,lower (bs i) :=
  Nat.le_of_dvd (Finset.prod_pos (fun i hi=>lower_pos _))
    (Finset.dvd_prod_of_mem (fun i=>lower (bs i)) (Finset.mem_univ a))

theorem actual_short_coefficient_bound
    (kap : ℝ) (hk : kap<1) (B N cj : ℕ) (kap0 z y : ℝ) (j : ℕ)
    (hj : j<3) (bs : Fin (2*(j+1))→Block) (a : Fin (2*(j+1)))
    (hactive : ∃ n∈rectangle bs,integerProfile kap B N cj kap0 n≠0)
    (v : ShortIndex a→ℕ) (hv : v∈shortBox bs a) :
    ‖shortCoefficient z y a v‖≤profileHeight N^5 := by
  have hraw := actual_raw_product_cap kap hk B N cj kap0 bs hactive
  have hp (i : ShortIndex a) : 0<v i ∧ v i≤4*N := by
    have ho := (mem_shortBox bs a v).mp hv i
    refine ⟨owns_pos ho,?_⟩
    have hl := (lower_le_raw bs i.val).trans hraw
    exact (owns_bounds ho).2.trans (by omega)
  have hcard : Fintype.card (ShortIndex a)≤5 := by rw [short_index_card]; omega
  rw [shortCoefficient,norm_prod]
  calc
    _≤∏ _i : ShortIndex a,profileHeight N := Finset.prod_le_prod
      (fun i hi=>norm_nonneg _)
      (fun i hi=>actual_role_norm_le_height N z y _ _ (hp i).1 (hp i).2)
    _=profileHeight N^Fintype.card (ShortIndex a) := by simp
    _≤profileHeight N^5 := pow_le_pow_right₀ (height_one_le N) hcard

def rectangleValue (kap : ℝ) (B N cj K : ℕ) (kap0 : ℝ) (j : ℕ)
    (bs : Fin (2*(j+1))→Block) (Q : Finset ℕ) (rho : ℕ→ℂ) : ℂ :=
  ∑ n∈rectangle bs,
    hbSlots (beforeHBCutoff K [cj]) (fun _=>hbCutoff cj) (rowRoles j) n*
      (integerProfile kap B N cj kap0 n : ℂ)*wordKernel Q rho N [completeProduct n]

theorem actual_occurrenceAtom_dictionary
    (kap : ℝ) (B N cj K : ℕ) (kap0 : ℝ) (j : ℕ)
    (bs : List Block) (Q : Finset ℕ) (rho : ℕ→ℂ) :
    occurrenceAtom kap B N cj K kap0 j bs Q rho=
      rectangleValue kap B N cj K kap0 j (blockVector (2*(j+1)) bs) Q rho := by
  simp only [occurrenceAtom,rectangleValue,
    PrimeProducts.MellinInsertion20261028.exactDiscrepancy,
    PrimeProducts.MellinInsertion20261028.functional,wordKernel,List.prod_cons,List.prod_nil,mul_one]

theorem rectangleValue_zero_of_not_active
    (kap : ℝ) (B N cj K : ℕ) (kap0 : ℝ) (j : ℕ)
    (bs : Fin (2*(j+1))→Block) (Q : Finset ℕ) (rho : ℕ→ℂ)
    (h : ¬∃ n∈rectangle bs,integerProfile kap B N cj kap0 n≠0) :
    rectangleValue kap B N cj K kap0 j bs Q rho=0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have hz : integerProfile kap B N cj kap0 n=0 := by
    by_contra hp
    exact h ⟨n,hn,hp⟩
  simp [hz]

/-- Finite E5 after the actual restoration of ALL ordered short vectors.
The second term contains 4 epsilon N, not S epsilon U with S separately
restored after a per-fibre O(N) estimate. No total-restoration premise is
introduced: both coefficient and width budgets are proved above/in the
immutable fibre foundations. -/
theorem actual_rectangle_finite
    (kap : ℝ) (hk : kap<1) (N cj K D jBrun : ℕ) (kap0 : ℝ)
    (j : ℕ) (hj : j<3) (bs : Fin (2*(j+1))→Block)
    (a : Fin (2*(j+1))) (k : ℕ) (ha : bs a=.dyadic k)
    (hactive : ∃ n∈rectangle bs,integerProfile kap 6 N cj kap0 n≠0)
    (Q : Finset ℕ) (rho : ℕ→ℂ) (Rrho zEnvelope H : ℝ)
    (hN : 0<N) (hz : 0≤beforeHBCutoff K [cj]) (hzEnv : 1≤zEnvelope)
    (hcut : beforeHBCutoff K [cj]≤zEnvelope)
    (hH : Part3.BrunFactorialRecurrenceE1.chartHarmonic
      (Part3.RoughSlotCharacterLift20261026b.smallPrimes (beforeHBCutoff K [cj]))≤H)
    (hD : 1≤D) (hQ : Q⊆Finset.Ioc 0 D) (hcop : ∀ q∈Q,N.Coprime q)
    (hR : 0≤Rrho) (hrho : ∀ q∈Q,‖rho q‖≤Rrho)
    (hr : rowRoles j a=.one ∨ rowRoles j a=.logarithm) :
    ‖rectangleValue kap 6 N cj K kap0 j bs Q rho‖≤
      (2*profileConstant*Rrho)*profileHeight N^78*logBudget D^4*
        (10*zEnvelope^(2*jBrun+1)*(D : ℝ)*(shortSize bs a : ℝ)+
          4*(H^(2*jBrun+1)/(Nat.factorial (2*jBrun+1) : ℝ))*(N : ℝ)) := by
  let L := profileHeight N
  let Y := zEnvelope^(2*jBrun+1)
  let e := H^(2*jBrun+1)/(Nat.factorial (2*jBrun+1) : ℝ)
  let V := (2*profileConstant*L^73)*Rrho*logBudget D^4
  have hL : 1≤L := height_one_le N
  have hL0 : 0≤L := zero_le_one.trans hL
  have hC := profileConstant_nonneg
  have hze : 0≤zEnvelope := zero_le_one.trans hzEnv
  have hH0 : 0≤H := (show 0≤Part3.BrunFactorialRecurrenceE1.chartHarmonic
      (Part3.RoughSlotCharacterLift20261026b.smallPrimes (beforeHBCutoff K [cj])) by
        unfold Part3.BrunFactorialRecurrenceE1.chartHarmonic; positivity).trans hH
  have he : 0≤e := by dsimp [e]; positivity
  have hY : 0≤Y := by dsimp [Y]; positivity
  have hV : 0≤V := by dsimp [V]; positivity
  have hUc : 2^k≤2*N := by
    have h := (lower_le_raw bs a).trans (actual_raw_product_cap kap hk 6 N cj kap0 bs hactive)
    simpa only [ha,lower] using h
  have hUp : 0<2^k := Nat.pow_pos (by norm_num)
  have hpoint (v : ShortIndex a→ℕ) (hv : v∈shortBox bs a) :
      ‖longFibre kap 6 N cj K kap0 a v (2^k) Q rho‖≤
        L^5*V*(10*Y*(D : ℝ)+2*e*(fibreWidth (2*N) (shortProduct v) (2^k) : ℝ)) := by
    have hf := actual_fibre_finite kap N cj K D jBrun kap0 a v (2^k) Q rho
      Rrho zEnvelope H hN (short_product_pos bs a hv) hUp hUc hz hzEnv hcut hH hD hQ hcop hR hrho hr
    have hc := actual_short_coefficient_bound kap hk 6 N cj kap0
      (beforeHBCutoff K [cj]) (hbCutoff cj) j hj bs a hactive v hv
    have hpos : 0≤10*Y*(D : ℝ)+2*e*(fibreWidth (2*N) (shortProduct v) (2^k) : ℝ) := by positivity
    calc
      _≤_ := hf
      _=‖shortCoefficient (beforeHBCutoff K [cj]) (hbCutoff cj) a v‖*V*
          (10*Y*(D : ℝ)+2*e*(fibreWidth (2*N) (shortProduct v) (2^k) : ℝ)) := by
        dsimp [V,L,Y,e]
        ring
      _≤_ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hV) hpos
  have hw : (∑ v∈shortBox bs a,fibreWidth (2*N) (shortProduct v) (2^k) : ℝ)≤2*(N : ℝ) := by
    have h := actual_width_sum_le_twoN kap hk 6 N cj kap0 bs a hactive
    simpa only [ha,lower,Nat.cast_sum,Nat.cast_mul,Nat.cast_ofNat] using (Nat.cast_le.mpr h :
      ((∑ v∈shortBox bs a,fibreWidth (2*N) (shortProduct v) (lower (bs a)) : ℕ) : ℝ)≤(2*N : ℕ))
  rw [rectangleValue,occurrenceAtom_short_fibres kap hk 6 N cj K kap0 j bs a k ha]
  calc
    _≤∑ v∈shortBox bs a,‖longFibre kap 6 N cj K kap0 a v (2^k) Q rho‖ := norm_sum_le _ _
    _≤∑ v∈shortBox bs a,
        L^5*V*(10*Y*(D : ℝ)+2*e*(fibreWidth (2*N) (shortProduct v) (2^k) : ℝ)) :=
      Finset.sum_le_sum hpoint
    _=L^5*V*(10*Y*(D : ℝ)*(shortSize bs a : ℝ)+
        2*e*∑ v∈shortBox bs a,(fibreWidth (2*N) (shortProduct v) (2^k) : ℝ)) := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,short_card,←Finset.mul_sum]
      simp only [nsmul_eq_mul]
      ring
    _≤L^5*V*(10*Y*(D : ℝ)*(shortSize bs a : ℝ)+4*e*(N : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh := mul_le_mul_of_nonneg_left hw (show 0≤2*e by positivity)
      nlinarith
    _=_ := by dsimp [L,V,Y,e]; ring

end
end ImbalancedChen.P1OriginalSingletonOneLongRestoration
