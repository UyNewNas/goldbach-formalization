import ImbalancedChen.P4BOriginalHighRankMediumHeads
import ImbalancedChen.P4AOriginalFiniteFallbackGroupedAtoms
import ImbalancedChen.P5RoughSquarePowerPayment

/-! The actual raw label bank and its clipped ordered prime tuples.  No
restriction is placed on equal primes inside or across groups. -/
namespace ImbalancedChen.P4BOriginalCollisionWords
noncomputable section
open Classical
open scoped BigOperators
open P4AOriginalFiniteFallbackGroupedAtoms (box beta)
open P4AOriginalFiniteFallbackPhysicalSelected (word)
open P4AOriginalFiniteFallbackNaturalEndpoints (tag upper interval endpoint_bounds power_of_slots)
open P4AOriginalFull87RawChronology (cutoff)
open P4AUpperTaggedParityCompiler (rawSupport universe rawSupport_subset_universe)
open P4AOrderedThirdPhysicalAtoms (boxScalar)
open P4AHeldTaggedCompilerSupport (J0)

structure Params where
  m : ℕ
  r : ℕ
  n : ℕ
  e : ℚ
  q : ℕ
  a : ℝ
  omega : ℝ
  k : ℕ
  N : ℕ
  ell : ℝ

namespace Params
variable (P : Params)
abbrev f := P4AFiniteFallbackLowRankRho.retain P.m P.r P.n P.e P.q P.a P.omega P.N
abbrev T := P4BOriginalRankTwoChartPayment.tau P.m P.e P.q P.a P.k
abbrev W := (P.N:ℝ)^P.omega
abbrev L := (P.N:ℝ)^P.ell
abbrev U := universe P.N P.N P.W (cutoff P.N)
abbrev A := actualSmallRosserSupport P.N P.N P.W
abbrev raw := rawSupport P.f P.N P.N P.W (cutoff P.N)
abbrev rho := P4BOriginalFiniteSmoothCount.coefficient P.m P.r P.n P.e P.q P.a P.omega P.k P.N P.L
abbrev S := P4BOriginalAllRankClassicalRange.wholeHigh P.m P.r P.n P.e P.q P.a P.omega P.k P.N P.ell
abbrev wordOf := word P.N P.T
abbrev bins := box P.N P.omega P.T
abbrev small := beta P.N P.omega P.L
abbrev valJ (J : List ℕ) := boxScalar P.f P.N P.N P.W (cutoff P.N) P.T J
def words := (P.raw.image P.wordOf).filter (fun J => 3≤J.length)
def label (ps : List ℕ) := ps.map (tag P.N P.T)
def scalar (J : List ℕ) := P.valJ J/(actualPrimeFineWordMultiplicity J:ℝ)
def primeLists := P.words.biUnion P.bins
def records := (P.A.product P.primeLists).filter (fun hp => P.small (P.label hp.2) hp.1≠0)
abbrev modulus (hp : ℕ×List ℕ) := hp.1*hp.2.prod
theorem T_pos : 0<P.T := div_pos (logPrimeMeshStep_pos (by norm_num) _) (by positivity)

theorem word_witness {J} (hJ : J∈P.words) : ∃v∈P.raw,P.wordOf v=J :=
  Finset.mem_image.mp (Finset.mem_filter.mp hJ).1

theorem label_of_box (hN : 1<P.N) {J ps : List ℕ} (h : ps∈P.bins J) :
    P.label ps=J := by
  induction J generalizing ps with
  | nil =>
    have he : ps=[] := by simpa [bins,box,actualPrimeSlotBox] using h
    simp only [he,label,List.map_nil]
  | cons j J ih =>
    obtain ⟨⟨p,xs⟩,hh,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hp,hxs⟩ := Finset.mem_product.mp hh
    have he := P4AOrderedThirdPhysicalAtoms.prime_label hN P.T_pos (Finset.mem_inter.mp hp).1
    change (P2LowerFiniteCellRounding.primeLabel P.N P.T p).toNat :: P.label xs=j::J
    rw [he,Int.toNat_natCast,ih hxs]

theorem record_data (hN : 1<P.N) {h : ℕ×List ℕ} (hm : h∈P.records) :
    h.1∈P.A ∧ P.label h.2∈P.words ∧ h.2∈P.bins (P.label h.2) ∧
    P.small (P.label h.2) h.1≠0 := by
  obtain ⟨hab,hb⟩ := Finset.mem_filter.mp hm
  obtain ⟨ha,hbox⟩ := Finset.mem_product.mp hab
  obtain ⟨J,hJ,hps⟩ := Finset.mem_biUnion.mp hbox
  have heq := P.label_of_box hN hps
  exact ⟨ha,by rwa [heq],by rwa [heq],hb⟩

theorem prime_data {J ps : List ℕ} (hp : ps∈P.bins J) :
    ∀p∈ps,p.Prime ∧ P.W≤(p:ℝ) := by
  have hc := (P4AOrderedThirdClippedFactorial.crop _ _ _ _).mp hp
  intro p h
  have hr := mem_roughPrimeFinset.mp (hc.2 p h)
  exact ⟨hr.2.1,hr.2.2.2.1⟩

theorem rough {J ps : List ℕ} (hp : ps∈P.bins J) : RoughPrimeSupportedAt P.W ps.prod := by
  have H := P.prime_data hp
  have hperm := Nat.primeFactorsList_unique (rfl : ps.prod=ps.prod) (fun p h => (H p h).1)
  refine ⟨(List.prod_pos (fun p h => (H p h).1.pos)).ne',?_⟩
  intro p h
  rw [←Nat.toFinset_factors,List.mem_toFinset] at h
  exact (H p (hperm.mem_iff.mpr h)).2

theorem rank_cap {J} (hJ : J∈P.words) (hN : 1<P.N) (he : 0≤P.e) (ho : 0<P.omega) :
    J.length≤J0 P.omega := by
  obtain ⟨v,hv,rfl⟩ := P.word_witness hJ
  have H := P4AOriginalFiniteFallbackRange.raw_range _ (P4AOriginalFiniteFallbackCanonical.bounded P.m) _
    (P4AOriginalFull87HistoryCore.width_pos P.r) _ _ (show 0≤(P4AOriginalNewFifthUnion.data P.e P.q P.a).e from he)
    _ _ _ (by omega : 2≤P.N) _ _ ho hv
  simpa only [wordOf,word,List.length_reverse,List.length_map] using H.1.le

/-- Endpoints of a live whole label even for a repeated prime and for a
rejected ALL word. The original raw representative is used only to pay
the lengths and inflation. -/
theorem full_cap (hN : 1<P.N) (he : 0≤P.e) (ho : 0<P.omega)
    (ht : P.ell+P.T*(J0 P.omega:ℝ)<1/1000) {h : ℕ×List ℕ} (hh : h∈P.records) :
    (modulus h:ℝ)<(P.N:ℝ)^(599/1000:ℝ) := by
  obtain ⟨ha,hJ,hps,hb⟩ := P.record_data hN hh
  obtain ⟨v,hv,hvJ⟩ := P.word_witness hJ
  obtain ⟨hr,hvtop⟩ := P4AOriginalFiniteFallbackRange.raw_range _ (P4AOriginalFiniteFallbackCanonical.bounded P.m) _
    (P4AOriginalFull87HistoryCore.width_pos P.r) _ _ (show 0≤(P4AOriginalNewFifthUnion.data P.e P.q P.a).e from he)
    _ _ _ (by omega : 2≤P.N) _ _ ho hv
  obtain ⟨hs,hprod⟩ := P2LowerCanonicalRetainedTrace.canonical_subword_of_universe _ _ _ _
    (rawSupport_subset_universe _ _ _ _ _ hv)
  have hn : (1:ℝ)<P.N := by exact_mod_cast hN
  have pr (p : ℕ) (hp : p∈v.primeFactorsList.reverse) := mem_roughPrimeUniverse.mp (hs.subset hp)
  have top := power_of_slots v.primeFactorsList.reverse P.N P.T
    (fun p hp => (endpoint_bounds hN P.T_pos (pr p hp).2.1 (pr p hp).2.2.1).2) (zero_lt_one.trans hn)
  have hpsle := P4AOriginalFiniteFallbackGroupedAtoms.group_support P.N P.omega P.T (P.label h.2) _
    (Finset.mem_image_of_mem List.prod hps)
  rw [←hvJ] at hpsle
  have hrle : (v.primeFactorsList.length:ℝ)≤J0 P.omega := by exact_mod_cast hr.le
  have htop : (P4BUpperSelectedBoxCapacity.endpoint (upper P.N P.T) v.primeFactorsList.reverse:ℝ)≤
      (P.N:ℝ)^(P.T*v.primeFactorsList.reverse.length)*(v.primeFactorsList.reverse.prod:ℝ) := top
  have hbox : (h.2.prod:ℝ)≤P4BUpperSelectedBoxCapacity.endpoint (upper P.N P.T) v.primeFactorsList.reverse := by
    simpa only [wordOf,word,P4BUpperSelectedBoxCapacity.endpoint,List.map_map,Function.comp_def,upper] using hpsle
  have hrough : (h.2.prod:ℝ)≤(P.N:ℝ)^(P.T*v.primeFactorsList.length)*(v:ℝ) := by
    simpa only [List.length_reverse,hprod] using hbox.trans htop
  have hsm : (h.1:ℝ)<P.L := by
    unfold small beta at hb
    split_ifs at hb
    · exact (actualSmallRosserPlus_active hb).2.1
    · exact (actualSmallRosserMinus_active hb).2.1
  calc
    (modulus h:ℝ)=(h.1:ℝ)*(h.2.prod:ℝ) := by simp only [modulus,Nat.cast_mul]
    _≤P.L*((P.N:ℝ)^(P.T*v.primeFactorsList.length)*(v:ℝ)) :=
      mul_le_mul hsm.le hrough (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _<(P.N:ℝ)^P.ell*((P.N:ℝ)^(P.T*v.primeFactorsList.length)*(P.N:ℝ)^P4AFull87UnionCompilerPayment.top) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hvtop (Real.rpow_pos_of_pos (zero_lt_one.trans hn) _))
        (Real.rpow_pos_of_pos (zero_lt_one.trans hn) _)
    _≤_ := by
      rw [←Real.rpow_add (zero_lt_one.trans hn),←Real.rpow_add (zero_lt_one.trans hn)]
      apply Real.rpow_le_rpow_of_exponent_le hn.le
      have H := mul_le_mul_of_nonneg_left hrle P.T_pos.le
      dsimp only [P4AFull87UnionCompilerPayment.top]
      linarith

end Params
end
end ImbalancedChen.P4BOriginalCollisionWords
