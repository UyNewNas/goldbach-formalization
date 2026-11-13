import ImbalancedChen.P1OriginalSingletonMiddleTensor

/-! SOURCE ONLY. The two actual singleton modulus channels are kept
separate. `free` is a coefficient of the whole modulus, not a sequence on
the selected long occurrence. No smoothness or discrepancy bound is input. -/
namespace ImbalancedChen.P1OriginalSingletonOneLongCoefficients
noncomputable section
open Classical
open scoped BigOperators
open P4BOriginalCollisionWords (Params)
open P4AHeldTaggedCompilerSupport (J0)
open P4BOriginalCollisionTensor (products free fibre_card scalar_bound)
open P4BOriginalCollisionPhysical (freeRecord supported_physical)
open P1OriginalSingletonMiddleRank (live live_data)

def modulusCap (N : ℕ) : ℕ := ⌊(N : ℝ)^(599/1000 : ℝ)⌋₊

theorem modulusCap_pos (N : ℕ) (hN : 1≤N) : 1≤modulusCap N := by
  apply Nat.le_floor
  exact Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)

theorem physical_data (P : Params) (hN : 1<P.N) (he : 0≤P.e)
    (ho : 0<P.omega) (hell : P.ell<1/1000)
    (ht : P.ell+P.T*(J0 P.omega : ℝ)<1/1000) :
    live P ⊆ Finset.Ioc 0 (modulusCap P.N) ∧
      (∀ q∈live P,P.N.Coprime q) ∧
      (∀ q∈live P,‖(P.rho q : ℂ)‖≤1) := by
  have data (q : ℕ) (hq : q∈live P) := live_data P hN he ho hell ht hq
  refine ⟨?_,?_,?_⟩
  · intro q hq
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Icc.mp (data q hq).1).1,
      Nat.le_floor (supported_physical P hN he ho hell ht (Finset.mem_filter.mp hq).2).le⟩
  · intro q hq
    exact (data q hq).2.2.1.symm
  · intro q hq
    simpa only [Complex.norm_real,Real.norm_eq_abs] using (data q hq).2.2.2

/-- Removing zero modulus coefficients changes neither the count nor its
same-modulus exact coprime mean. The test can be complex and arbitrary. -/
theorem physical_read_live (P : Params) (G : ℕ→ℂ) :
    (∑ q∈live P,(P.rho q : ℂ)*G q)=∑ q∈P.S,(P.rho q : ℂ)*G q := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro q hq hn
  have hz : P.rho q=0 := by
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨hq,h⟩)
  simp [hz]

theorem record_coprime (P : Params) (hN : 1<P.N) {h : ℕ×List ℕ}
    (hh : h∈P.records) : (Params.modulus h).Coprime P.N := by
  obtain ⟨ha,hJ,hps,hsmall⟩ := P.record_data hN hh
  have hcop : ∀ p∈h.2,p.Coprime P.N := by
    intro p hp
    have crop := (P4AOrderedThirdClippedFactorial.crop _ _ _ _).mp hps
    have rough := mem_roughPrimeFinset.mp (crop.2 p hp)
    exact rough.2.1.coprime_iff_not_dvd.mpr rough.2.2.1
  have product_coprime : ∀ xs : List ℕ,(∀ p∈xs,p.Coprime P.N)→xs.prod.Coprime P.N := by
    intro xs
    induction xs with
    | nil => intro hp; simp
    | cons p ps ih =>
      intro hp
      exact Nat.coprime_mul_iff_left.mpr ⟨hp p (by simp),
        ih (fun q hq=>hp q (List.mem_cons_of_mem p hq))⟩
  exact Nat.coprime_mul_iff_left.mpr
    ⟨actualSmallRosserSupport_coprime_target P.N P.N P.W ha,product_coprime h.2 hcop⟩

theorem freeRecord_abs_le_one (P : Params) (h : ℕ×List ℕ) :
    |freeRecord P h|≤1 := by
  have hsmall : |P.small (P.label h.2) h.1|≤1 := by
    unfold Params.small P4AOriginalFiniteFallbackGroupedAtoms.beta
    split
    · exact actualSmallRosserPlus_abs_le_one _ _ _ _ _
    · exact actualSmallRosserMinus_abs_le_one _ _ _ _ _
  have hs := scalar_bound P (P.label h.2)
  simp only [freeRecord,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
  exact (mul_le_mul hs hsmall (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

/-- Ordered record multiplicity is paid by the existing genuine fibre
cardinality bound. No long-slot coefficient is introduced by this sum. -/
theorem free_abs_le (P : Params) (hN : 1<P.N) (he : 0≤P.e) (ho : 0<P.omega) (q : ℕ) :
    |free P q|≤((J0 P.omega).factorial : ℝ) := by
  unfold free
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _≤∑ _h∈P.records.filter (fun h=>Params.modulus h=q),(1 : ℝ) :=
      Finset.sum_le_sum (fun h hh=>freeRecord_abs_le_one P h)
    _≤_ := by
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using
        (Nat.cast_le.mpr (fibre_card P hN he ho q) :
          ((P.records.filter (fun h=>Params.modulus h=q)).card : ℝ)≤(J0 P.omega).factorial)

theorem free_data (P : Params) (hN : 1<P.N) (he : 0≤P.e) (ho : 0<P.omega)
    (ht : P.ell+P.T*(J0 P.omega : ℝ)<1/1000) :
    products P ⊆ Finset.Ioc 0 (modulusCap P.N) ∧
      (∀ q∈products P,P.N.Coprime q) ∧
      (∀ q∈products P,‖(free P q : ℂ)‖≤((J0 P.omega).factorial : ℝ)) := by
  refine ⟨?_,?_,?_⟩
  · intro q hq
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨ha,hJ,hps,hsmall⟩ := P.record_data hN hh
    have hpos : 0<Params.modulus h := Nat.mul_pos
      (Nat.pos_of_ne_zero (actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ ha).1)
      (Nat.pos_of_ne_zero (P.rough hps).1)
    exact Finset.mem_Ioc.mpr ⟨hpos,Nat.le_floor (P.full_cap hN he ho ht hh).le⟩
  · intro q hq
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hq
    exact (record_coprime P hN hh).symm
  · intro q hq
    simpa only [Complex.norm_real,Real.norm_eq_abs] using free_abs_le P hN he ho q

end
end ImbalancedChen.P1OriginalSingletonOneLongCoefficients
