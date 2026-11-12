import ImbalancedChen.P4BOriginalCollisionModes

/-! Absorb the true small Rosser via the unique small/rough factorisation
into the third group, also on nonsquarefree rough products. Bound all
restored scalars by a bank fixed before the target. -/
namespace ImbalancedChen.P4BOriginalCollisionThirdFactor
noncomputable section
open Classical
open scoped BigOperators
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (grouped products free ownerHead grouped_eq_free)
open P4AOriginalFiniteFallbackGroupedAtoms (slots partition group_unit group_support)
open P4AHeldTaggedCompilerSupport (J0)
open P4AOriginalFiniteFallbackNaturalEndpoints (tag)
open P4AOriginalFiniteFallbackPhysicalSelected (word)
open P4AOriginalFull87RawChronology (cutoff)
open P5Z.ExactOriginalSmoothDyadicPartition (words)
open P4BUpperSelectedBoxCapacity (endpoint)
variable (P : Params)

def thirdPairs (J G : List ℕ) :=
  (P.A.filter (fun h => P.small J h≠0)).product ((P.bins G).image List.prod)
def thirdSupport (J G : List ℕ) := (thirdPairs P J G).image (fun hc => hc.1*hc.2)
def factor (G : List ℕ) := actualNormalizedPrimeTupleCoefficient (P.bins G) G.length
def gamma (J G : List ℕ) (t : ℕ) :=
  ∑ hc∈(thirdPairs P J G).filter (fun hc => hc.1*hc.2=t),P.small J hc.1*factor P G hc.2

private theorem unique {J G} {a b : ℕ×ℕ} (ha : a∈thirdPairs P J G) (hb : b∈thirdPairs P J G)
    (he : a.1*a.2=b.1*b.2) : a=b := by
  have H (v : ℕ×ℕ) (hv : v∈thirdPairs P J G) : SmallPrimeSupportedAt P.W v.1 ∧ RoughPrimeSupportedAt P.W v.2 := by
    obtain ⟨hs,hr⟩ := Finset.mem_product.mp hv
    obtain ⟨ps,hp,hprod⟩ := Finset.mem_image.mp hr
    exact ⟨actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ (Finset.mem_filter.mp hs).1,hprod ▸ P.rough hp⟩
  exact smallRough_factorization_unique (H a ha).1 (H a ha).2 (H b hb).1 (H b hb).2 he

theorem gamma_at {J G} {v : ℕ×ℕ} (hv : v∈thirdPairs P J G) :
    gamma P J G (v.1*v.2)=P.small J v.1*factor P G v.2 := by
  have hset : (thirdPairs P J G).filter (fun hc => hc.1*hc.2=v.1*v.2)={v} := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨ht,he⟩
      exact unique P ht hv he
    · rintro rfl
      exact ⟨hv,rfl⟩
  simp only [gamma,hset,Finset.sum_singleton]

theorem gamma_one (J G : List ℕ) (t : ℕ) : |gamma P J G t|≤1 := by
  by_cases ht : t∈thirdSupport P J G
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht
    rw [gamma_at P hv,abs_mul]
    have hb : |P.small J v.1|≤1 := by
      unfold Params.small P4AOriginalFiniteFallbackGroupedAtoms.beta
      split
      · exact actualSmallRosserPlus_abs_le_one _ _ _ _ _
      · exact actualSmallRosserMinus_abs_le_one _ _ _ _ _
    simpa only [one_mul] using mul_le_mul hb (group_unit P.N P.omega P.T G v.2) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  · have hz : (thirdPairs P J G).filter (fun hc => hc.1*hc.2=t)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv; exact ht (Finset.mem_image.mpr ⟨v,(Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2⟩)
    simp [gamma,hz]

theorem gamma_range {J G} {t} (ht : t∈thirdSupport P J G) :
    (t:ℝ)≤P.L*endpoint (actualPrimeFineLabelIntegerUpper P.N P.T) G := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hv1,hv2⟩ := Finset.mem_product.mp hv
  have hh := (Finset.mem_filter.mp hv1).2
  have hl : (v.1:ℝ)<P.L := by
    unfold Params.small P4AOriginalFiniteFallbackGroupedAtoms.beta at hh
    split_ifs at hh
    · exact (actualSmallRosserPlus_active hh).2.1
    · exact (actualSmallRosserMinus_active hh).2.1
  rw [Nat.cast_mul]
  exact mul_le_mul hl.le (group_support _ _ _ _ _ hv2) (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem gamma_apply (J G : List ℕ) (F : ℕ→ℝ) :
    (∑ h∈P.A,∑ c∈(P.bins G).image List.prod,P.small J h*factor P G c*F (h*c))=
      ∑ t∈thirdSupport P J G,gamma P J G t*F t := by
  calc
    _=∑ hc∈thirdPairs P J G,P.small J hc.1*factor P G hc.2*F (hc.1*hc.2) := by
      unfold thirdPairs
      rw [Finset.sum_product,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro h hh
      by_cases hz : P.small J h=0 <;> simp [hz]
    _=_ := by
      rw [thirdSupport,Finset.sum_image (fun x hx y hy he => unique P hx hy he)]
      exact Finset.sum_congr rfl (fun t ht => by rw [gamma_at P ht])

def splitAt (x U eta : ℝ) (J : List ℕ) :=
  slots P.m P.N (P4AOriginalNewFifthUnion.data P.e P.q P.a) P.omega P.T x U eta (ownerHead P J) J

def restoring (x U eta : ℝ) (J : List ℕ) :=
  let S := splitAt P x U eta J
  P.scalar J*(S.1.length.factorial:ℝ)*(S.2.1.length.factorial:ℝ)*(S.2.2.length.factorial:ℝ)*(-1:ℝ)^J.length

def tensor (x U eta : ℝ) (F : ℕ→ℝ) :=
  ∑ J∈P.words,
    let S := splitAt P x U eta J
    restoring P x U eta J*∑ a∈(P.bins S.1).image List.prod,∑ b∈(P.bins S.2.1).image List.prod,
      ∑ t∈thirdSupport P J S.2.2,factor P S.1 a*factor P S.2.1 b*gamma P J S.2.2 t*F (a*b*t)

theorem tensor_eq (hN : 1<P.N) (x U eta : ℝ) (F : ℕ→ℝ) :
    tensor P x U eta F=∑ t∈products P,free P t*F t := by
  rw [←grouped_eq_free P hN x U eta F]
  unfold tensor grouped
  rw [Finset.sum_comm (s:=P.A)]
  apply Finset.sum_congr rfl
  intro J hJ
  let S := splitAt P x U eta J
  let D := restoring P x U eta J
  let B := fun G : List ℕ => (P.bins G).image List.prod
  have H (a b : ℕ) := gamma_apply P J S.2.2 (fun t => F (a*b*t))
  change D*(∑ a∈B S.1,∑ b∈B S.2.1,∑ t∈thirdSupport P J S.2.2,
    factor P S.1 a*factor P S.2.1 b*gamma P J S.2.2 t*F (a*b*t))=_
  have hab (a b : ℕ) :
      (∑ t∈thirdSupport P J S.2.2,factor P S.1 a*factor P S.2.1 b*gamma P J S.2.2 t*F (a*b*t))=
      ∑ h∈P.A,∑ c∈B S.2.2,(factor P S.1 a*factor P S.2.1 b)*
        (P.small J h*factor P S.2.2 c*F (a*b*(h*c))) := by
    calc
      _=(factor P S.1 a*factor P S.2.1 b)*
          ∑ t∈thirdSupport P J S.2.2,gamma P J S.2.2 t*F (a*b*t) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _=_ := by rw [←H a b]; simp only [Finset.mul_sum]
  simp_rw [hab,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro c hc
  dsimp [D,restoring,factor,S,splitAt]
  rw [show a*b*(h*c)=h*(a*b*c) by ring]
  ring

/-- Evaluation on a complete complex congruence row with the same
coprime mean and three independent arithmetic factors. -/
theorem row_tensor (hN : 1<P.N) (x U eta : ℝ) {ι : Type*} (I : Finset ι)
    (prod : ι→ℕ) (w : ι→ℂ) :
    ImbalancedChen.PrimeProducts.MellinInsertion20261028.exactDiscrepancy I (products P)
      (fun t => (free P t:ℂ)) prod P.N w=
    (tensor P x U eta (fun t => (P4BOriginalCollisionKernel.row I prod w P.N t).re):ℂ)+
      Complex.I*(tensor P x U eta (fun t => (P4BOriginalCollisionKernel.row I prod w P.N t).im):ℂ) := by
  rw [P4BOriginalCollisionKernel.reindex,tensor_eq P hN,tensor_eq P hN]
  have H := P4BOriginalCollisionModes.grouped_complex P hN x U eta (P4BOriginalCollisionKernel.row I prod w P.N)
  rw [grouped_eq_free P hN,grouped_eq_free P hN] at H
  exact H.symm

/-- A fixed alphabet and rank bank can be selected before N, x, U, or
any mode. Its cardinal alone suffices, without estimating its growth in
tau: the original resolution of these prime labels is held fixed. -/
def alphabet (T : ℝ) := Finset.range (⌈1/T⌉₊+1)
def master (omega T : ℝ) := (Finset.range (J0 omega+1)).biUnion (words (alphabet T))

private theorem word_mem (A : Finset ℕ) (J : List ℕ) (h : ∀i∈J,i∈A) : J∈words A J.length := by
  induction J with
  | nil => simp [words]
  | cons j J ih =>
    exact Finset.mem_image.mpr ⟨(j,J),Finset.mem_product.mpr ⟨h j List.mem_cons_self,
      ih (fun i hi => h i (List.mem_cons_of_mem _ hi))⟩,rfl⟩

theorem admissible_words (hN : 1<P.N) (he : 0≤P.e) (ho : 0<P.omega) :
    P.words⊆master P.omega P.T := by
  intro J hJ
  refine Finset.mem_biUnion.mpr ⟨J.length,Finset.mem_range.mpr (Nat.lt_succ_of_le (P.rank_cap hJ hN he ho)),
    word_mem _ J ?_⟩
  obtain ⟨v,hv,hvJ⟩ := P.word_witness hJ
  obtain ⟨hsub,_⟩ := P2LowerCanonicalRetainedTrace.canonical_subword_of_universe _ _ _ _
    (P4AUpperTaggedParityCompiler.rawSupport_subset_universe _ _ _ _ _ hv)
  intro i hi
  rw [←hvJ] at hi
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hi
  obtain ⟨hcap,hprime,hn,hw,hz⟩ := mem_roughPrimeUniverse.mp (hsub.subset hp)
  have hpn : (1:ℝ)<P.N := by exact_mod_cast hN
  have H := (mem_actualPrimeFineLabelFinset.mp (P4AOriginalFiniteFallbackNaturalEndpoints.interval hN P.T_pos hprime hn)).2.2.1
  have hle : (P.N:ℝ)^(P.T*(tag P.N P.T p:ℝ))≤(P.N:ℝ)^(1:ℝ) := by
    rw [Real.rpow_one]; exact H.trans (by exact_mod_cast hcap.le)
  have hmul := (Real.rpow_le_rpow_left_iff hpn).mp hle
  have hr : (tag P.N P.T p:ℝ)≤1/P.T := (le_div_iff₀ P.T_pos).mpr (by linarith only [hmul,mul_comm P.T (tag P.N P.T p:ℝ)])
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.cast_le.mp (hr.trans (Nat.le_ceil _))))

theorem restored_mass (hN : 1<P.N) (he : 0≤P.e) (ho : 0<P.omega) (x U eta : ℝ) :
    (∑ J∈P.words,|restoring P x U eta J|)≤
      ((master P.omega P.T).card:ℝ)*((J0 P.omega).factorial:ℝ)^3 := by
  let K := ((J0 P.omega).factorial:ℝ)
  have hbound (J) (hJ : J∈P.words) : |restoring P x U eta J|≤K^3 := by
    let S := splitAt P x U eta J
    have hpart := (partition P.m P.N _ P.omega P.T x U eta (ownerHead P J) J (Finset.mem_filter.mp hJ).2).length_eq
    change (S.1++(S.2.1++S.2.2)).length=J.length at hpart
    simp only [List.length_append] at hpart
    have hr := P.rank_cap hJ hN he ho
    have h (a : ℕ) (ha : a≤J0 P.omega) : (a.factorial:ℝ)≤K := by exact_mod_cast Nat.factorial_le ha
    have hab := P4BOriginalCollisionTensor.scalar_bound P J
    simp only [restoring,abs_mul,abs_pow,abs_neg,abs_one,one_pow,mul_one,abs_of_nonneg (Nat.cast_nonneg _)]
    change |P.scalar J|*(S.1.length.factorial:ℝ)*(S.2.1.length.factorial:ℝ)*(S.2.2.length.factorial:ℝ)≤_
    calc
      _≤1*K*K*K := mul_le_mul (mul_le_mul (mul_le_mul hab (h _ (by omega)) (Nat.cast_nonneg _) (by norm_num))
        (h _ (by omega)) (Nat.cast_nonneg _) (by positivity)) (h _ (by omega)) (Nat.cast_nonneg _) (by positivity)
      _=_ := by ring
  calc
    _≤∑ _J∈P.words,K^3 := Finset.sum_le_sum hbound
    _≤_ := by
      simpa only [Finset.sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Finset.card_le_card (admissible_words P hN he ho)) : (P.words.card:ℝ)≤_)
        (pow_nonneg (Nat.cast_nonneg _) 3)

end
end ImbalancedChen.P4BOriginalCollisionThirdFactor
