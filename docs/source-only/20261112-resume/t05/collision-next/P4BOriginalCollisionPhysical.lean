import ImbalancedChen.P4BOriginalCollisionWords

/-! Replace the actual high-rank physical sum by its complete labelled
Cartesian sum with the original global Möbius factor. -/
namespace ImbalancedChen.P4BOriginalCollisionPhysical
noncomputable section
open Classical
open scoped BigOperators
open P4BOriginalCollisionWords
open P4AOriginalFiniteFallbackNaturalEndpoints (tag interval)
open P4AOriginalFiniteFallbackPhysicalSelected (word)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOrderedThirdPhysicalAtoms (sorted_label)
open P4AUpperTaggedParityCompiler (universe coefficient primeWordLabel)
open P4AOriginalFiniteFallbackGroupedAtoms (box beta)
open P4AHeldTaggedCompilerSupport (J0)
variable (P : Params)

def physicalBox (J : List ℕ) :=
  (((actualPrimeSlotBox (actualPrimeFineLabelFinset P.N P.T) J).filter List.SortedGT).image List.prod).filter (·∈P.U)

theorem own_label (hN : 1<P.N) {j : ℕ} (hj : j∈P.U) (J : List ℕ) :
    j∈physicalBox P J ↔ P.wordOf j=J := by
  constructor
  · intro h
    obtain ⟨ps,hp,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
    obtain ⟨hbox,hs⟩ := Finset.mem_filter.mp hp
    have H := congrArg (List.map Int.toNat) (sorted_label P.N hN P.T P.T_pos J ps hbox hs)
    simpa [Params.wordOf,word,tag,primeWordLabel,P2LowerFiniteCellRounding.label,
      List.map_map,Function.comp_def] using H
  · rintro rfl
    obtain ⟨hsub,hprod⟩ := P2LowerCanonicalRetainedTrace.canonical_subword_of_universe _ _ _ _ hj
    let ps := j.primeFactorsList.reverse
    have H (xs : List ℕ) (hh : ∀ p∈xs,p∈roughPrimeUniverse P.N P.N P.W (cutoff P.N)) :
        xs∈actualPrimeSlotBox (actualPrimeFineLabelFinset P.N P.T) (xs.map (tag P.N P.T)) := by
      induction xs with
      | nil => simp [actualPrimeSlotBox]
      | cons p xs ih =>
        have hx := mem_roughPrimeUniverse.mp (hh p List.mem_cons_self)
        exact Finset.mem_image.mpr ⟨(p,xs),Finset.mem_product.mpr
          ⟨interval hN P.T_pos hx.2.1 hx.2.2.1,ih (fun q hq => hh q (List.mem_cons_of_mem p hq))⟩,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨ps,Finset.mem_filter.mpr
      ⟨H ps hsub.subset,List.sortedGT_iff_pairwise.mpr ((roughPrimeUniverse_pairwise_gt _ _ _ _).sublist hsub)⟩,hprod⟩,hj⟩

theorem owner_key (hN : 1<P.N) {d : ℕ} {J} (hd : d∈physicalBox P J) :
    primeWordLabel P.N P.T d=J.map (fun j => (j:ℤ)) := by
  obtain ⟨ps,hp,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hd).1
  obtain ⟨hbox,horder⟩ := Finset.mem_filter.mp hp
  exact sorted_label P.N hN P.T P.T_pos J ps hbox horder

theorem ordered (hN : 1<P.N) {J} (hJ : J∈P.words) : J.Pairwise (·≥·) := by
  obtain ⟨v,hv,rfl⟩ := P.word_witness hJ
  have hN0 : (1:ℝ)<P.N := by exact_mod_cast hN
  have mono : Monotone (tag P.N P.T) := by
    intro p q hpq
    have H : Real.log (p:ℝ)≤Real.log (q:ℝ) := by
      by_cases hp : p=0
      · subst p
        by_cases hq : q=0
        · simp [hq]
        · simpa only [Nat.cast_zero,Real.log_zero] using Real.log_nonneg
            (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq : (1:ℝ)≤q)
      · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hp) (by exact_mod_cast hpq)
    have hh := Int.floor_mono (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right H (Real.log_pos hN0).le) P.T_pos.le)
    change (⌊(Real.log (p:ℝ)/Real.log P.N)/P.T⌋:ℤ).toNat≤(⌊(Real.log (q:ℝ)/Real.log P.N)/P.T⌋:ℤ).toNat
    omega
  exact List.pairwise_map.mpr ((Nat.primeFactorsList_sorted v).reverse.pairwise.imp (fun h => mono h))

/-- Every nonzero native rough row supplies its own raw representative in
this bank. Membership of a zero coefficient has no role in this assertion. -/
theorem active_word (hN : 1<P.N) {d : ℕ} (hr : 3≤d.primeFactorsList.length)
    (hc : coefficient P.f (fun _ => []) P.N P.N P.W (cutoff P.N) P.T d≠0) : P.wordOf d∈P.words := by
  obtain ⟨u,hu,_,_,hj⟩ := P4AUpperTaggedParityCompiler.active_has_raw_witness _ _ _ _ _ _ _ hc
  have hw : P.wordOf u=P.wordOf d := by
    simpa only [Params.wordOf,word,tag,primeWordLabel,P2LowerFiniteCellRounding.label,List.map_map,Function.comp_def]
      using congrArg (List.map Int.toNat) hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨u,hu,hw⟩,by simpa only [Params.wordOf,word,List.length_map,List.length_reverse] using hr⟩

def signedRecord (hp : ℕ×List ℕ) : ℝ :=
  P.scalar (P.label hp.2)*((ArithmeticFunction.moebius hp.2.prod:ℝ)*P.small (P.label hp.2) hp.1)
def freeRecord (hp : ℕ×List ℕ) : ℝ :=
  P.scalar (P.label hp.2)*((-1:ℝ)^hp.2.length*P.small (P.label hp.2) hp.1)

/-- Collecting records adds only the filter beta≠0 and uses the unique
literal word of each ordered tuple. -/
theorem records_sum (hN : 1<P.N) (F : ℕ→ℝ) (g : List ℕ→ℝ) :
    (∑ hp∈P.records,P.scalar (P.label hp.2)*(g hp.2*P.small (P.label hp.2) hp.1)*F (Params.modulus hp))=
    ∑ h∈P.A,∑ J∈P.words,P.scalar J * ∑ ps∈P.bins J,g ps*(P.small J h*F (h*ps.prod)) := by
  unfold Params.records
  rw [Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro h hh
  let G := fun ps : List ℕ => P.scalar (P.label ps)*(g ps*P.small (P.label ps) h)*F (h*ps.prod)
  have drop : (∑ ps∈P.primeLists,if P.small (P.label ps) h≠0 then G ps else 0)=
      ∑ ps∈P.primeLists,G ps := by
    apply Finset.sum_congr rfl
    intro ps _
    by_cases hz : P.small (P.label ps) h=0 <;> simp [hz,G]
  change (∑ ps∈P.primeLists,if P.small (P.label ps) h≠0 then G ps else 0)=_
  rw [drop]
  have source (ps) (hp : ps∈P.primeLists) : P.label ps∈P.words := by
    obtain ⟨J,hJ,hb⟩ := Finset.mem_biUnion.mp hp
    rwa [P.label_of_box hN hb]
  rw [←Finset.sum_fiberwise_of_maps_to (s:=P.primeLists) (t:=P.words) (g:=P.label) source G]
  apply Finset.sum_congr rfl
  intro J hJ
  have he : P.primeLists.filter (fun ps => P.label ps=J)=P.bins J := by
    ext ps
    constructor
    · rintro him
      obtain ⟨hp,he⟩ := Finset.mem_filter.mp him
      obtain ⟨jj,_,hb⟩ := Finset.mem_biUnion.mp hp
      simpa only [←he,P.label_of_box hN hb] using hb
    · intro hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨J,hJ,hb⟩,P.label_of_box hN hb⟩
  rw [he,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ps hp
  dsimp only [G]
  rw [P.label_of_box hN hp]; ring

theorem box_signed (hN : 1<P.N) (F : ℕ→ℝ) {J} (hJ : J∈P.words) {h} (hh : h∈P.A) :
    P.scalar J*(∑ ps∈P.bins J,(ArithmeticFunction.moebius ps.prod:ℝ)*(P.small J h*F (h*ps.prod)))=
      ∑ d∈physicalBox P J,P.rho (h*d)*F (h*d) := by
  rw [show P.scalar J*(∑ ps∈P.bins J,(ArithmeticFunction.moebius ps.prod:ℝ)*(P.small J h*F (h*ps.prod)))=
      ∑ d∈((actualPrimeSlotBox (actualPrimeFineLabelFinset P.N P.T) J).filter List.SortedGT).image List.prod,
        coefficient P.f (fun _ => []) P.N P.N P.W (cutoff P.N) P.T d*(P.small J h*F (h*d)) from
    P4AOriginalFiniteFallbackAtoms.rectangular_factorial P.f P.omega P.N hN P.T P.T_pos J
      (ordered P hN hJ) _]
  unfold physicalBox
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hu : d∈P.U
  · rw [if_pos hu]
    have H := P4AOriginalFiniteFallbackGroupedAtoms.rho_atom P.f P.N P.omega P.T P.L J hh hu hd
    change _=P4AUpperTaggedBetaAttachment.rho P.f (fun _ => []) P.N P.N P.W (cutoff P.N) P.T P.L (h*d)*_
    rw [H]; ring
  · rw [if_neg hu]
    simp only [coefficient,if_neg hu,zero_mul]

theorem physical (hN : 1<P.N) (F : ℕ→ℝ) :
    (∑ hp∈P.records,signedRecord P hp*F (Params.modulus hp))=∑ q∈P.S,P.rho q*F q := by
  rw [show (∑ hp∈P.records,signedRecord P hp*F (Params.modulus hp))=
    ∑ h∈P.A,∑ J∈P.words,P.scalar J*(∑ ps∈P.bins J,(ArithmeticFunction.moebius ps.prod:ℝ)*
      (P.small J h*F (h*ps.prod))) from records_sum P hN F _]
  have hprod (h : ℕ) (hh : h∈P.A) :
      (∑ J∈P.words,∑ d∈physicalBox P J,P.rho (h*d)*F (h*d))=
        ∑ d∈P.U,if h*d∈P.S then P.rho (h*d)*F (h*d) else 0 := by
    have eqf (J : List ℕ) : physicalBox P J=P.U.filter (fun d => P.wordOf d=J) := by
      ext d
      constructor
      · intro hd
        have hi := (Finset.mem_filter.mp hd).2
        exact Finset.mem_filter.mpr ⟨hi,(own_label P hN hi J).mp hd⟩
      · intro hd
        obtain ⟨hi,hj⟩ := Finset.mem_filter.mp hd
        exact (own_label P hN hi J).mpr hj
    simp_rw [eqf,Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    have hQ : h*d∈P4BOriginalFiniteSmoothCount.Q P.omega P.N :=
      Finset.mem_image.mpr ⟨(h,d),Finset.mem_product.mpr ⟨hh,hd⟩,rfl⟩
    by_cases hn : P.rho (h*d)=0
    · simp [hn]
    have hval := P4AUpperTaggedBetaAttachment.rho_at_product P.f (fun _ => []) P.N P.N P.W
      (cutoff P.N) P.T P.L hh hd
    have hc : coefficient P.f (fun _ => []) P.N P.N P.W (cutoff P.N) P.T d≠0 := by
      intro hz; exact hn (by rw [show P.rho (h*d)=_ from hval,hz,zero_mul])
    by_cases hr : 3≤d.primeFactorsList.length
    · have hj := active_word P hN hr hc
      have hs : h*d∈P.S := Finset.mem_sdiff.mpr ⟨hQ,fun hlow => by
        have hle := (Finset.mem_filter.mp hlow).2.2 h hh d hd rfl
        omega⟩
      simp [hs,hj]
    · have hs : h*d∉P.S := fun him => (Finset.mem_sdiff.mp him).2
        (P4AFiniteFallbackLowRankRho.mem_activeLow_of_decomposition _ _ _ _ _ _ _ _ _ _ hn hh hd rfl (by omega))
      have hj : P.wordOf d∉P.words := fun him => hr (by
        simpa only [Params.wordOf,word,List.length_map,List.length_reverse] using (Finset.mem_filter.mp him).2)
      simp [hs,hj]
  calc
    _=∑ h∈P.A,∑ J∈P.words,∑ d∈physicalBox P J,P.rho (h*d)*F (h*d) :=
      Finset.sum_congr rfl (fun h hh => Finset.sum_congr rfl (fun J hJ => box_signed P hN F hJ hh))
    _=∑ h∈P.A,∑ d∈P.U,if h*d∈P.S then P.rho (h*d)*F (h*d) else 0 := Finset.sum_congr rfl hprod
    _=∑ v∈P4BOriginalFiniteSmoothCount.Q P.omega P.N,if v∈P.S then P.rho v*F v else 0 := by
      rw [←Finset.sum_product',show P4BOriginalFiniteSmoothCount.Q P.omega P.N=
        (P.A.product P.U).image (fun hd => hd.1*hd.2) from rfl,Finset.sum_image]
      intro x hx y hy hxy
      obtain ⟨h1,h2⟩ := P4AUpperTaggedBetaAttachment.product_unique P.N P.N P.W (cutoff P.N)
        (Finset.mem_product.mp hx).1 (Finset.mem_product.mp hx).2
        (Finset.mem_product.mp hy).1 (Finset.mem_product.mp hy).2 hxy
      exact Prod.ext h1 h2
    _=_ := by
      rw [←Finset.sum_filter]
      congr 1
      ext v
      simp only [Finset.mem_filter]
      exact ⟨And.right,fun h => ⟨(Finset.mem_sdiff.mp h).1,h⟩⟩

/-- A nonzero high coefficient has an actual nonzero complete record. The
original short-rank estimate covers the complementary nonzero class. -/
theorem supported_physical (hN : 1<P.N) (he : 0≤P.e) (ho : 0<P.omega)
    (hell : P.ell<1/1000) (ht : P.ell+P.T*(J0 P.omega:ℝ)<1/1000) {d : ℕ} (hd : P.rho d≠0) :
    (d:ℝ)<(P.N:ℝ)^(599/1000:ℝ) := by
  have hQ : d∈P4BOriginalFiniteSmoothCount.Q P.omega P.N := by
    by_contra hn
    exact hd (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hn)
  by_cases hl : d∈P4BOriginalAllRankClassicalRange.lowRank P.m P.r P.n P.e P.q P.a P.omega P.k P.N P.ell
  · apply (P4AFiniteFallbackLowRankRho.activeLow_power _ _ _ _ _ _ _ _ hN _ _ hell hl).trans_le
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) (by norm_num)
  · have hs : d∈P.S := Finset.mem_sdiff.mpr ⟨hQ,hl⟩
    let F := fun t : ℕ => if t=d then (1:ℝ) else 0
    have hsum : (∑ t∈P.S,P.rho t*F t)=P.rho d := by simp [F,mul_ite,hs]
    have H := physical P hN F
    rw [hsum] at H
    have hnon : (∑ h∈P.records,signedRecord P h*F (Params.modulus h))≠0 :=
      fun hz => hd (H.symm.trans hz)
    obtain ⟨h,hh,hval⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnon
    have hpos : Params.modulus h=d := by
      by_contra hn
      exact hval (by simp [F,hn])
    rw [←hpos]; exact P.full_cap hN he ho ht hh

end
end ImbalancedChen.P4BOriginalCollisionPhysical
