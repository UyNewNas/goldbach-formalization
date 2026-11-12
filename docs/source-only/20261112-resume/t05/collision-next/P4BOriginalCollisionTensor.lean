import ImbalancedChen.P4BOriginalCollisionPhysical

/-! The unrestricted tensor has the same small factor, three whole groups,
original reciprocal multiplicity and restored group factorials. Its excess
over the actual squarefree coefficient is supported on complete moduli
with a rough prime square, including repeats within a single group. -/
namespace ImbalancedChen.P4BOriginalCollisionTensor
noncomputable section
open Classical
open scoped BigOperators
open P4BOriginalCollisionWords
open P4BOriginalCollisionPhysical (signedRecord freeRecord records_sum physical)
open P4AOriginalFiniteFallbackGroupedAtoms (box beta slots partition)
open P4AOriginalFiniteFallbackPhysicalSelected (head pick)
open P4AOriginalFull87RawChronology (cutoff)
open P4AHeldTaggedCompilerSupport (J0)
variable (P : Params)

def products := P.records.image Params.modulus
def free (t : ℕ) := ∑ h∈P.records.filter (fun h => Params.modulus h=t),freeRecord P h
def error (t : ℕ) := ∑ h∈P.records.filter (fun h => Params.modulus h=t),freeRecord P h-signedRecord P h
def bad := roughSquareExceptions (Nat.floor ((P.N:ℝ)^(599/1000:ℝ))) P.W

theorem push (G : ℕ×List ℕ→ℝ) (F : ℕ→ℝ) :
    (∑ t∈products P,(∑ h∈P.records.filter (fun h => Params.modulus h=t),G h)*F t)=
      ∑ h∈P.records,G h*F (Params.modulus h) := by
  rw [←Finset.sum_fiberwise_of_maps_to (s:=P.records) (t:=products P) (g:=Params.modulus)
    (fun h hh => Finset.mem_image_of_mem _ hh) (fun h => G h*F (Params.modulus h))]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun h hh => by rw [(Finset.mem_filter.mp hh).2])

theorem difference (hN : 1<P.N) (F : ℕ→ℝ) :
    (∑ t∈products P,free P t*F t)-(∑ t∈P.S,P.rho t*F t)=
      ∑ t∈products P,error P t*F t := by
  rw [←physical P hN F,push,show (∑ t∈products P,error P t*F t)=_ from
    push P (fun h => freeRecord P h-signedRecord P h) F,←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => (sub_mul _ _ _).symm)

theorem scalar_bound (J : List ℕ) : |P.scalar J|≤1 := by
  have hp : 0<actualPrimeFineWordMultiplicity J :=
    Finset.prod_pos (fun j _ => Nat.factorial_pos _)
  have hm : (1:ℝ)≤actualPrimeFineWordMultiplicity J := by exact_mod_cast hp
  have hs : |P.valJ J|≤1 := by
    unfold Params.valJ P4AOrderedThirdPhysicalAtoms.boxScalar
    split <;> norm_num
  rw [Params.scalar,abs_div,abs_of_pos (by positivity : 0<(actualPrimeFineWordMultiplicity J:ℝ))]
  exact (div_le_one (by positivity)).mpr (hs.trans hm)

theorem record_cost (hN : 1<P.N) {h : ℕ×List ℕ} (hh : h∈P.records) :
    |freeRecord P h-signedRecord P h|≤1 ∧
      (freeRecord P h≠signedRecord P h → ∃p : ℕ,p.Prime ∧ P.W≤(p:ℝ) ∧ p^2∣Params.modulus h) := by
  obtain ⟨ha,hJ,hps,hb⟩ := P.record_data hN hh
  have pr := P.prime_data hps
  by_cases hs : Squarefree h.2.prod
  · have he : (ArithmeticFunction.moebius h.2.prod:ℝ)=(-1:ℝ)^h.2.length := by
      exact_mod_cast actualPrimeVector_moebius_eq_sign h.2 (fun p hp => (pr p hp).1)
        (actualPrimeVector_nodup_of_squarefree h.2 (fun p hp => (pr p hp).1) hs)
    simp [freeRecord,signedRecord,he]
  · have hz := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs
    have hbeta : |P.small (P.label h.2) h.1|≤1 := by
      unfold Params.small beta
      split
      · exact actualSmallRosserPlus_abs_le_one _ _ _ _ _
      · exact actualSmallRosserMinus_abs_le_one _ _ _ _ _
    have hrough := P.rough hps
    obtain ⟨p,hprime,hdiv⟩ : ∃ p : ℕ,p.Prime ∧ p^2∣h.2.prod := by
      by_contra hn
      apply hs
      apply Nat.squarefree_iff_prime_squarefree.mpr
      intro p hp hd
      exact hn ⟨p,hp,hd⟩
    refine ⟨?_,fun _ => ⟨p,hprime,hrough.2 p (Nat.mem_primeFactors.mpr
      ⟨hprime,(dvd_pow_self p (by decide : 2≠0)).trans hdiv,hrough.1⟩),hdiv.trans (dvd_mul_left _ _)⟩⟩
    simp only [signedRecord,freeRecord,hz,Int.cast_zero,zero_mul,mul_zero,sub_zero,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
    simpa only [one_mul] using mul_le_mul (scalar_bound P _) hbeta (abs_nonneg _) (by norm_num : (0:ℝ)≤1)

theorem fibre_card (hN : 1<P.N) (he : 0≤P.e) (ho : 0<P.omega) (t : ℕ) :
    (P.records.filter (fun h => Params.modulus h=t)).card≤(J0 P.omega).factorial := by
  let S := P.records.filter (fun h => Params.modulus h=t)
  by_cases hn : S.Nonempty
  · obtain ⟨base,hbase⟩ := hn
    obtain ⟨hs0,ht0⟩ := Finset.mem_filter.mp hbase
    obtain ⟨ha0,hJ0,hps0,hb0⟩ := P.record_data hN hs0
    have data {h : ℕ×List ℕ} (hh : h∈S) : h.1=base.1 ∧ h.2.Perm base.2 := by
      obtain ⟨hs1,ht1⟩ := Finset.mem_filter.mp hh
      obtain ⟨ha1,hJ1,hps1,hb1⟩ := P.record_data hN hs1
      have H : (h.1,h.2.prod)=(base.1,base.2.prod) := smallRough_factorization_unique
        (actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ ha1) (P.rough hps1)
        (actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ ha0) (P.rough hps0) (ht1.trans ht0.symm)
      exact ⟨congrArg Prod.fst H,(Nat.primeFactorsList_unique (congrArg Prod.snd H)
        (fun p hp => (P.prime_data hps1 p hp).1)).trans
          (Nat.primeFactorsList_unique (rfl : base.2.prod=base.2.prod) (fun p hp => (P.prime_data hps0 p hp).1)).symm⟩
    calc
      S.card≤base.2.permutations.toFinset.card := Finset.card_le_card_of_injOn Prod.snd
        (fun h hh => List.mem_toFinset.mpr (List.mem_permutations.mpr (data hh).2))
        (fun x hx y hy hxy => Prod.ext ((data hx).1.trans (data hy).1.symm) hxy)
      _≤base.2.permutations.length := List.toFinset_card_le _
      _=base.2.length.factorial := List.length_permutations _
      _≤_ := Nat.factorial_le (by simpa only [Params.label,List.length_map] using P.rank_cap hJ0 hN he ho)
  · rw [show P.records.filter (fun h => Params.modulus h=t)=∅ from Finset.not_nonempty_iff_eq_empty.mp hn]
    simp

theorem error_bound (hN : 1<P.N) (he : 0≤P.e) (ho : 0<P.omega) (t : ℕ) :
    |error P t|≤((J0 P.omega).factorial:ℝ) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _≤∑ _h∈P.records.filter (fun h => Params.modulus h=t),(1:ℝ) :=
      Finset.sum_le_sum (fun h hh => (record_cost P hN (Finset.mem_filter.mp hh).1).1)
    _≤_ := by simpa using (Nat.cast_le.mpr (fibre_card P hN he ho t) :
      ((P.records.filter (fun h => Params.modulus h=t)).card:ℝ)≤(J0 P.omega).factorial)

theorem error_support (hN : 1<P.N) (he : 0≤P.e) (ho : 0<P.omega)
    (ht : P.ell+P.T*(J0 P.omega:ℝ)<1/1000) {t : ℕ} (hnz : error P t≠0) : t∈bad P ∧ t∈products P := by
  obtain ⟨h,hh,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  obtain ⟨hR,ht'⟩ := Finset.mem_filter.mp hh
  obtain ⟨ha,hJ,hps,_⟩ := P.record_data hN hR
  have h1 : 0<Params.modulus h := Nat.mul_pos
    (Nat.pos_of_ne_zero (actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ ha).1)
    (Nat.pos_of_ne_zero (P.rough hps).1)
  rw [←ht']
  exact ⟨mem_roughSquareExceptions.mpr ⟨h1,Nat.le_floor (P.full_cap hN he ho ht hR).le,
      (record_cost P hN hR).2 (sub_ne_zero.mp hv)⟩,Finset.mem_image_of_mem _ hR⟩

/-- The head comes from the same canonical raw label owner. Whole-bin
slots may vary with the local x and U and have no effect on the free
coefficient. Thus the complete arithmetic test may be chosen afterward. -/
def ownerHead (J : List ℕ) :=
  head (pick P.f P.N P.N P.W (cutoff P.N) P.T (J.map (fun j => (j:ℤ)))).primeFactorsList.reverse

theorem ownerHead_at (hN : 1<P.N) {d : ℕ} {J} (hd : d∈P4BOriginalCollisionPhysical.physicalBox P J) :
    ownerHead P J=head (pick P.f P.N P.N P.W (cutoff P.N) P.T
      (P4AUpperTaggedParityCompiler.primeWordLabel P.N P.T d)).primeFactorsList.reverse := by
  simp only [ownerHead,P4BOriginalCollisionPhysical.owner_key P hN hd]

def grouped (x U eta : ℝ) (F : ℕ→ℝ) :=
  ∑ h∈P.A,∑ J∈P.words,
    let S := slots P.m P.N (P4AOriginalNewFifthUnion.data P.e P.q P.a) P.omega P.T x U eta (ownerHead P J) J
    let T := P.bins
    ∑ a∈(T S.1).image List.prod,∑ b∈(T S.2.1).image List.prod,∑ c∈(T S.2.2).image List.prod,
      (P.scalar J*(S.1.length.factorial:ℝ)*(S.2.1.length.factorial:ℝ)*(S.2.2.length.factorial:ℝ))*
      actualNormalizedPrimeTupleCoefficient (T S.1) S.1.length a*
      actualNormalizedPrimeTupleCoefficient (T S.2.1) S.2.1.length b*
      actualNormalizedPrimeTupleCoefficient (T S.2.2) S.2.2.length c*
      ((-1:ℝ)^J.length*(P.small J h*F (h*(a*b*c))))

theorem grouped_eq_free (hN : 1<P.N) (x U eta : ℝ) (F : ℕ→ℝ) :
    grouped P x U eta F=∑ t∈products P,free P t*F t := by
  rw [show (∑ t∈products P,free P t*F t)=_ from push P (freeRecord P) F,show
    (∑ hp∈P.records,freeRecord P hp*F (Params.modulus hp))=_ from records_sum P hN F (fun ps => (-1:ℝ)^ps.length)]
  symm
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro J hJ
  let S := slots P.m P.N (P4AOriginalNewFifthUnion.data P.e P.q P.a) P.omega P.T x U eta (ownerHead P J) J
  let G := fun t => (-1:ℝ)^J.length*(P.small J h*F (h*t))
  have hsum : P.scalar J*(∑ ps∈P.bins J,(-1:ℝ)^ps.length*(P.small J h*F (h*ps.prod)))=
      ∑ ps∈P.bins J,P.scalar J*G ps.prod := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun ps hp => by rw [actualPrimeSlotBox_length _ J ps hp])
  rw [hsum,←actualPrimeSlotBox_product_sum_perm _ (partition P.m P.N _ P.omega P.T x U eta (ownerHead P J) J
    (Finset.mem_filter.mp hJ).2) (fun t => P.scalar J*G t),actualPrimeSlotBox_product_sum_append]
  simp_rw [actualPrimeSlotBox_product_sum_append]
  simpa only [mul_assoc] using actualPrimeTuple_threeGroup_sum_normalized (P.bins S.1) (P.bins S.2.1)
    (P.bins S.2.2) S.1.length S.2.1.length S.2.2.length (P.scalar J) G

end
end ImbalancedChen.P4BOriginalCollisionTensor
