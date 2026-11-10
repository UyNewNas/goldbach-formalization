import ImbalancedChen.P4AFull87UnsupportedThirdAdmission
import Mathlib.NumberTheory.Bertrand

/-! Arithmetic input for a clustered word on the genuine policy. A single
upper integer bound checks *all* odd-cube tests at every ancestor. The
separate Bertrand construction supplies arbitrarily many ordered primes. -/
namespace ImbalancedChen.P4AFull87ClusteredRoughWords
noncomputable section
open scoped Classical BigOperators
open P4AFull87UnsupportedThirdAdmission P5OriginalCommonRefinedConstructor VariableEnvelope

theorem product_bounds {l u : ℕ} (xs : List ℕ) (h : ∀ p ∈ xs, l≤p ∧ p≤u) :
    l^xs.length≤xs.prod ∧ xs.prod≤u^xs.length := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
    obtain ⟨hl,hu⟩ := h p List.mem_cons_self
    obtain ⟨hl',hu'⟩ := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [List.length_cons,List.prod_cons,pow_succ']
    exact ⟨Nat.mul_le_mul hl hl',Nat.mul_le_mul hu hu'⟩

theorem ordinary_small_word {X k : ℕ} (hX : 1≤X) {R : ℝ}
    (hR : (X:ℝ)^(k+2)<R) (xs : List ℕ) (hlen : xs.length≤k)
    (h : ∀ p ∈ xs, p≤X) : ordinaryRosserPrefixAdmissible false R xs := by
  have H := (product_bounds (l:=0) xs (fun p hp => ⟨Nat.zero_le _,h p hp⟩)).2
  have H' : xs.prod≤X^(k+2) := H.trans (pow_le_pow_right₀ hX (by omega))
  refine ⟨lt_of_le_of_lt (by exact_mod_cast H') hR,?_⟩
  intro p hp _
  let S := xs.toFinset.filter (fun q => p≤q)
  have hc : S.card≤k := (Finset.card_le_card (Finset.filter_subset _ _)).trans
    ((List.toFinset_card_le xs).trans hlen)
  have hs : S.prod id ≤ X^k := calc
    _ ≤ ∏ _q ∈ S, X := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun q hq =>
      h q (List.mem_toFinset.mp (Finset.mem_filter.mp hq).1))
    _ = X^S.card := Finset.prod_const _
    _ ≤ _ := pow_le_pow_right₀ hX hc
  have hp' := h p (List.mem_toFinset.mp hp)
  have hm : (S.prod id)*p^2 ≤ X^(k+2) := by
    rw [pow_add]
    exact Nat.mul_le_mul hs (Nat.pow_le_pow_left hp' _)
  exact lt_of_le_of_lt (by exact_mod_cast hm) hR

private theorem tuple_value {xs : List ℕ} (k : ℕ) (i : Fin k) :
    primeHistoryTuple k xs i=0 ∨ primeHistoryTuple k xs i ∈ xs := by
  unfold primeHistoryTuple
  by_cases hi : i.val<xs.reverse.length
  · right
    rw [List.getD_eq_getElem _ _ hi]
    exact List.mem_reverse.mp (List.getElem_mem _)
  · exact Or.inl (List.getD_eq_default _ _ (le_of_not_gt hi))

private theorem coord_bounds {N : ℕ} (hN : 1<N) {X : ℕ} (hX : 1≤X)
    (xs : List ℕ) (h : ∀ p ∈ xs, 1≤p ∧ p≤X) (k : ℕ) (i : Fin k) :
    0≤primeHistoryLogCoordinates (N:ℝ) k xs i ∧
      primeHistoryLogCoordinates (N:ℝ) k xs i ≤ Real.log X/Real.log N := by
  have hn : 0<Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hx : 0≤Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  rcases tuple_value (xs:=xs) k i with hz|hm
  · simp [primeHistoryLogCoordinates,hz,div_nonneg hx hn.le]
  · obtain ⟨hp,hu⟩ := h _ hm
    exact ⟨div_nonneg (Real.log_nonneg (by exact_mod_cast hp)) hn.le,
      div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hu)) hn.le⟩

theorem clustered_rho {d : OriginalData} {N cap X : ℕ} (hN : 1<N) (hX : 1≤X)
    {delta w z tau L : ℝ} (hd : 0<delta) (hL : 1<L) (n : ℕ)
    (xs : List ℕ) (hxs : xs.Sublist (roughPrimeUniverse N cap w z)) (he : Even xs.length)
    (hu : ∀ p ∈ xs, p≤X) (hsmall : (X:ℝ)<(N:ℝ)^d.omega)
    (h8 : Real.log X/Real.log N≤1/100)
    (hlo : Real.log X/Real.log N < logPrimeMeshPoint 0 (19/96) d.m 1)
    (hstop : logPrimeMeshPoint 0 (19/96) d.m 1 ≤ extendedFirstStop-4*(d.e:ℝ))
    (hcube : (X:ℝ)^(xs.length+2)<(N:ℝ)^HistoricalThirdCoarse.initial d.e) :
    let keep := P4AFull87UnionCompilerPayment.keep delta n d N
    let tag := P4AFull87DataCompilerReads.tag delta hd n d N
    xs.prod ∈ P4AUpperTaggedBetaAttachment.support N cap w z ∧
    P4AUpperTaggedBetaAttachment.rho keep tag N cap w z tau L xs.prod=1 := by
  apply even_word_rho hN.le hd hL n xs hxs he
  intro i hi
  let pre := (xs.take (i+1)).reverse
  have hs (p : ℕ) (hp : p∈pre) : p∈xs := (List.take_sublist _ _).subset (List.mem_reverse.mp hp)
  have hp (p : ℕ) (hm : p∈pre) : 1≤p ∧ p≤X :=
    ⟨(mem_roughPrimeUniverse_prime (hxs.subset (hs _ hm))).pos,hu _ (hs _ hm)⟩
  have ha (r : ℕ) (p : ℕ) (hm : p∈rosserAncestor r pre) : 1≤p ∧ p≤X :=
    hp p ((List.drop_sublist _ _).subset hm)
  have ht : (primeHistoryTuple 3 (rosserAncestor 3 pre) 2:ℝ) ≤ X := by
    rcases tuple_value (xs:=rosserAncestor 3 pre) 3 2 with h0|hmem
    · simp [h0]
    · exact_mod_cast (ha 3 _ hmem).2
  have hl : pre.length≤xs.length := by simp [pre]
  refine ⟨missed_of_small (ht.trans_lt hsmall),?_,ordinary_small_word hX hcube pre hl
    (fun p hmem => (hp p hmem).2),?_⟩
  · exact ((coord_bounds hN hX _ (ha 8) 8 2).2).trans h8
  · intro _
    have hc := coord_bounds hN hX pre hp 1 0
    exact ⟨0,by simpa using hc.1,hc.2.trans_lt hlo,hstop⟩

/-- k distinct odd primes between 2^j and 2^(j+k), coprime to *every*
target 2^D. Each dyadic interval is disjoint at its assigned endpoint. -/
theorem dyadic_primes (k j D : ℕ) (hj : 1≤j) :
    ∃ p : Fin k → ℕ, StrictMono p ∧
      ∀ i, (p i).Prime ∧ ¬p i ∣ 2^D ∧ 2^j < p i ∧ p i ≤ 2^(j+k) := by
  classical
  have hex (i : Fin k) := Nat.exists_prime_lt_and_le_two_mul (2^(j+i.val)) (by positivity)
  choose p hpr hlo hhi using hex
  have H (i : Fin k) : p i≤2^(j+i.val+1) := by simpa [pow_succ'] using hhi i
  have L0 (i : Fin k) : 2^j < p i :=
    (pow_le_pow_right₀ (by norm_num : 1≤(2:ℕ)) (by omega : j≤j+i.val)).trans_lt (hlo i)
  refine ⟨p,?_,?_⟩
  · intro i l hil
    have hil' : i.val<l.val := hil
    exact (H i).trans_lt ((pow_le_pow_right₀ (by norm_num : 1≤(2:ℕ))
      (by omega : j+i.val+1≤j+l.val)).trans_lt (hlo l))
  · intro i
    have h₂ : 2 < p i := lt_of_le_of_lt (by simpa using
      (pow_le_pow_right₀ (by norm_num : 1≤(2:ℕ)) hj)) (L0 i)
    refine ⟨hpr i,fun h => ?_,L0 i,(H i).trans (pow_le_pow_right₀ (by norm_num) (by omega))⟩
    exact (ne_of_gt h₂) ((Nat.prime_dvd_prime_iff_eq (hpr i) Nat.prime_two).mp
      ((hpr i).dvd_of_dvd_pow h))

private theorem power_compare {D a k : ℕ} {s : ℝ}
    (h : (a:ℝ)*k < (D:ℝ)*s) :
    (((2^a:ℕ):ℝ)^k) < ((2^D:ℕ):ℝ)^s := by
  have h₂ : Real.log 2>0 := Real.log_pos (by norm_num)
  apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
  push_cast
  rw [Real.log_pow,Real.log_pow,Real.log_rpow (by positivity),Real.log_pow]
  nlinarith [mul_lt_mul_of_pos_right h h₂]

private theorem power_compare' {D a k : ℕ} {s : ℝ}
    (h : (D:ℝ)*s < (a:ℝ)*k) :
    ((2^D:ℕ):ℝ)^s < (((2^a:ℕ):ℝ)^k) := by
  have h₂ : Real.log 2>0 := Real.log_pos (by norm_num)
  apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
  push_cast
  rw [Real.log_rpow (by positivity),Real.log_pow,Real.log_pow,Real.log_pow]
  nlinarith [mul_lt_mul_of_pos_right h h₂]

/-- At the *target* N=2^D, on the complete Q with per-prime bounds w,z,
an honest nonzero modulus larger than N^s. The hypotheses are scalar
inequalities in three integer lengths; the primes, tree, ALL/ANY,
small beta, target coprimality, and the value 1 are all conclusions. -/
theorem clustered_target (d : OriginalData) (n k j D : ℕ) (he : Even k)
    (hj : 1≤j) (hD : 0<D) (delta wExp zExp s : ℝ) (hd : 0<delta)
    (hz : zExp≤1) (hw : (D:ℝ)*wExp < j) (hs : (D:ℝ)*s < (j:ℝ)*k)
    (hu : (j:ℝ)+k < D*zExp) (hom : (j:ℝ)+k < D*d.omega)
    (h8 : (j:ℝ)+k ≤ D*(1/100:ℝ))
    (hfirst : (j:ℝ)+k < D*logPrimeMeshPoint 0 (19/96) d.m 1)
    (hstop : logPrimeMeshPoint 0 (19/96) d.m 1 ≤ extendedFirstStop-4*(d.e:ℝ))
    (hcu : ((j:ℝ)+k)*(k+2) < D*HistoricalThirdCoarse.initial d.e)
    (tau L : ℝ) (hL : 1<L) :
    let N := 2^D
    let w := (N:ℝ)^wExp
    let z := (N:ℝ)^zExp
    let keep := P4AFull87UnionCompilerPayment.keep delta n d N
    let tag := P4AFull87DataCompilerReads.tag delta hd n d N
    ∃ x ∈ P4AUpperTaggedBetaAttachment.support N N w z, (N:ℝ)^s < (x:ℝ) ∧
      P4AUpperTaggedBetaAttachment.rho keep tag N N w z tau L x=1 := by
  let N := 2^D
  let X := 2^(j+k)
  obtain ⟨p,hp,H⟩ := dyadic_primes k j D hj
  let xs := (List.ofFn p).reverse
  have hN : 1<N := one_lt_pow₀ (by decide : 1<(2:ℕ)) hD.ne'
  have hNR : (1:ℝ)<N := by exact_mod_cast hN
  have hX : 1≤X := Nat.one_le_pow _ _ (by decide)
  have hlen : xs.length=k := by simp [xs]
  have hmem (x : ℕ) (hm : x∈xs) : ∃ i, p i=x := List.mem_ofFn.mp (List.mem_reverse.mp hm)
  have hward : ((N:ℝ)^wExp) < ((2^j:ℕ):ℝ) := by
    simpa only [pow_one] using (power_compare' (k:=1) (by simpa using hw))
  have B (t : ℝ) (ht : (j:ℝ)+k < D*t) : (X:ℝ) < (N:ℝ)^t := by
    simpa only [pow_one] using (power_compare (a:=j+k) (k:=1) (by simpa using ht))
  have hsort : xs.Pairwise (· > ·) := by
    simpa only [xs,List.pairwise_reverse] using (List.pairwise_ofFn.mpr hp)
  have hsub : xs.Sublist (roughPrimeUniverse N N ((N:ℝ)^wExp) ((N:ℝ)^zExp)) := by
    apply List.sublist_of_subperm_of_pairwise _ hsort (roughPrimeUniverse_pairwise_gt _ _ _ _)
    apply List.subperm_of_subset hsort.nodup
    intro x hm
    obtain ⟨i,rfl⟩ := hmem x hm
    have hzN : (N:ℝ)^zExp ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNR.le hz
    exact (mem_roughPrimeUniverse_iff_of_cutoff_le_cap hzN).mpr
      ⟨(H i).1,(H i).2.1,hward.le.trans (by exact_mod_cast (H i).2.2.1.le),
        lt_of_le_of_lt (by exact_mod_cast (H i).2.2.2) (B zExp hu)⟩
  have hr : Real.log X/Real.log N = ((j:ℝ)+k)/D := by
    dsimp only [X,N]
    push_cast
    rw [Real.log_pow,Real.log_pow]
    push_cast
    field_simp [(by exact_mod_cast hD.ne' : (D:ℝ)≠0),(Real.log_pos (by norm_num : (1:ℝ)<2)).ne']
    <;> ring
  have hDR : 0<(D:ℝ) := by exact_mod_cast hD
  have Hx (x : ℕ) (hm : x∈xs) : 2^j≤x ∧ x≤X := by
    obtain ⟨i,rfl⟩ := hmem x hm
    exact ⟨(H i).2.2.1.le,(H i).2.2.2⟩
  have hpay := clustered_rho hN hX hd hL n xs hsub (by simpa only [hlen] using he)
    (fun x hx => (Hx x hx).2) (B d.omega hom)
    (by rw [hr]; exact (div_le_iff₀ hDR).mpr (by linarith))
    (by rw [hr]; exact (div_lt_iff₀ hDR).mpr (by linarith)) hstop
    (by rw [hlen]; apply power_compare; push_cast; exact hcu)
  have hprod := (product_bounds xs Hx).1
  rw [hlen] at hprod
  exact ⟨xs.prod,hpay.1,(power_compare' hs).trans_le (by exact_mod_cast hprod),hpay.2⟩

end
end ImbalancedChen.P4AFull87ClusteredRoughWords
