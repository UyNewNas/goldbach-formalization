import ImbalancedChen.P4AOrderedThirdActualRoughGeometry

namespace ImbalancedChen.P4AOrderedThirdPhysicalSplit
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AUpperTaggedFrozenAdmissionCatalogue
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalOrderedThirdTable (retained capValue)
open P4AOriginalOrderedThirdFullPolicy (current)
open P2CanonicalWallFullResidualPayment

theorem rough_short {N c d : ℕ} {w z : ℝ} (hz : 1≤z)
    (hd : d∈P4AUpperTaggedParityCompiler.universe N c w z)
    (hr : d.primeFactorsList.length≤2) : (d:ℝ)≤z^2 := by
  have ⟨hs,hv⟩ := P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N c w z hd
  have hbound (xs : List ℕ) (hxs : ∀ p∈xs,(p:ℝ)≤z) : (xs.prod:ℝ)≤z^xs.length := by
    induction xs with
    | nil => simp
    | cons p xs ih =>
      rw [List.prod_cons,List.length_cons,Nat.cast_mul,pow_succ,mul_comm (z^_)]
      exact mul_le_mul (hxs _ List.mem_cons_self) (ih (fun t ht => hxs _ (List.mem_cons_of_mem _ ht)))
        (Nat.cast_nonneg _) (zero_le_one.trans hz)
  have hh := hbound d.primeFactorsList.reverse (fun p hp => (mem_roughPrimeUniverse_upper (hs.subset hp)).le)
  rw [hv,List.length_reverse] at hh
  exact hh.trans (pow_le_pow_right₀ hz hr)

/-- Both beta signs are read from this very rough component. Rank is
that of d alone, not the number of prime factors of the physical modulus. -/
theorem actual_split (r n : ℕ) (e : ℚ) (he : 0≤e) (q : ℕ) (a omega ell : ℝ)
    (hw : 0≤omega) (hell : ell<1/1000) (N : ℕ) (hN : 1<N) (tau : ℝ) (x : ℕ)
    (hx : coefficient r n e q a omega N tau ((N:ℝ)^ell) x≠0) :
    let D := data e q a
    let Y := (N:ℝ)^omega
    let Z := cutoff N
    let L := (N:ℝ)^ell
    let f := keep r n e q a omega N
    ∃ b d : ℕ, b*d=x ∧ b∈actualSmallRosserSupport N N Y ∧ (b:ℝ)<L ∧
      d∈P4AUpperTaggedParityCompiler.universe N N Y Z ∧
      (coefficient r n e q a omega N tau L x=
        P4AUpperTaggedParityCompiler.coefficient f (fun _ => []) N N Y Z tau d*
        (if 0≤P4AUpperTaggedParityCompiler.coefficient f (fun _ => []) N N Y Z tau d
          then actualSmallRosserPlus N N Y L b else actualSmallRosserMinus N N Y L b)) ∧
      ((d.primeFactorsList.length≤2 ∧ (x:ℝ)<(N:ℝ)^(1/2:ℝ)) ∨
      (3≤d.primeFactorsList.length ∧
       ∃ y∈P4AUpperTaggedParityCompiler.rawSupport f N N Y Z,
        y∈P4AUpperTaggedParityCompiler.cell (fun _ => []) N N Y Z tau d ∧
        ∃ j∈retained (D.e:ℝ) D.m,actualPrimeTupleLog N (canonicalPrefix 3 y)∈logPrimeMeshCell 0 (19/96) D.m j ∧
          (current D omega N y.primeFactorsList).scalar=capValue (D.e:ℝ) D.m j ∧
          capValue (D.e:ℝ) D.m j≤VariableEnvelope.cap-2*(D.e:ℝ))) := by
  let D := data e q a
  let f := keep r n e q a omega N
  let Y := (N:ℝ)^omega
  let Z := cutoff N
  let L := (N:ℝ)^ell
  have hS : x∈P4AUpperTaggedBetaAttachment.support N N Y Z := by
    by_contra h
    exact hx (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ h)
  obtain ⟨⟨b,d⟩,hpair,hm⟩ := Finset.mem_image.mp hS
  obtain ⟨hb,hd⟩ := Finset.mem_product.mp hpair
  have hp := P4AUpperTaggedBetaAttachment.rho_at_product f (fun _ => []) N N Y Z tau L hb hd
  rw [hm] at hp
  have hnon : P4AUpperTaggedParityCompiler.coefficient f (fun _ => []) N N Y Z tau d*
      (if 0≤P4AUpperTaggedParityCompiler.coefficient f (fun _ => []) N N Y Z tau d
       then actualSmallRosserPlus N N Y L b else actualSmallRosserMinus N N Y L b)≠0 := by
    rw [← hp]; exact hx
  obtain ⟨hc,hs⟩ := mul_ne_zero_iff.mp hnon
  have hbL : (b:ℝ)<L := by
    split_ifs at hs
    · exact (actualSmallRosserPlus_active hs).2.1
    · exact (actualSmallRosserMinus_active hs).2.1
  refine ⟨b,d,hm,hb,hbL,hd,hp,?_⟩
  by_cases hr : d.primeFactorsList.length≤2
  · left
    refine ⟨hr,?_⟩
    have hn : (1:ℝ)<N := by exact_mod_cast hN
    have hz : (1:ℝ)≤Z := Real.one_le_rpow hn.le (by norm_num [thirdPrefixRho])
    have hrough := rough_short hz hd hr
    have heq : Z^2=(N:ℝ)^(2*(19/96):ℝ) := by
      change ((N:ℝ)^(19/96:ℝ))^2=_
      rw [pow_two,←Real.rpow_add (zero_lt_one.trans hn)]
      congr 1 <;> ring
    calc
      (x:ℝ)=(b:ℝ)*(d:ℝ) := by rw [← hm,Nat.cast_mul]
      _≤L*Z^2 := mul_le_mul hbL.le hrough (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _=(N:ℝ)^(ell+2*(19/96):ℝ) := by rw [heq]; exact (Real.rpow_add (zero_lt_one.trans hn) _ _).symm
      _<(N:ℝ)^(1/2:ℝ) := Real.rpow_lt_rpow_of_exponent_lt hn (by linarith)
  · have h3 : 3≤d.primeFactorsList.length := by omega
    exact Or.inr ⟨h3,P4AOrderedThirdActualRoughGeometry.active_high_witness (width r) n D he hN hw hc h3⟩

end
end ImbalancedChen.P4AOrderedThirdPhysicalSplit
