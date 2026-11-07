import ImbalancedChen.P2EnhancedSwitchedTrueNormalization
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSourceGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

O's actual UNSIFTED quotient-one source is a prime-product count, without
receiver primality. The native HighUnitSource geometry concerns a smaller
prime-receiver carrier, so its source inclusion cannot prove the needed
raw-mass comparison. Here the physical product inequality itself supplies
the last-prime fibre membership. Complete lists are retained in the
injection; Gamma20 and Gamma21 have independent five/six-prime sources.
-/

namespace ImbalancedChen.P2EnhancedUnitSourceGeometry
noncomputable section
open Finset Wu2008DoubleSieve
open SecondFunctionalUnitPrimeFibre HighUnitSource
open P2EnhancedSwitchedUnsiftedSource
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2SeedOmegaLiteralFibre (a0 a1 a2 a3 b)
open scoped Classical BigOperators

def productLabels (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) : Finset (List ℕ) :=
  (labels N Q d cs).filter (fun l => d*l.prod≤N)

def physical20 (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ g∈HighUnit.primePrefix20 (Q/d) a2 a3 b,
    ((physical (prefixProduct g) ((N:ℝ)/d) (g (Fin.last 3)).val ((Q/d)^b)).card:ℝ)

def physical21 (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ g∈HighUnit.primePrefix21 (Q/d) a3 b,
    ((physical (prefixProduct g) ((N:ℝ)/d) (g (Fin.last 4)).val ((Q/d)^b)).card:ℝ)

theorem labels_power (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) :
    labels N Q d cs=
      (secondFunctionalMotherTuples (primeWindow N ((Q/d)^a0) ((Q/d)^b)) cs.length).filter
        (fun l => l.map (secondFunctionalMotherColour ((Q/d)^a1) ((Q/d)^a2)
          ((Q/d)^a3))=cs) := by
  norm_num [labels,cutoff,a0,a1,a2,a3,b]

/-- This membership uses the unsifted product inequality, not an invented
prime output for the unit atom. Equality at the physical cap is retained. -/
theorem physical_of_product {N d n q : ℕ} {R H : ℝ}
    (hd : 0<d) (hH : 0≤H) (g : Fin n → primeSlabPrimes R) (j : Fin n)
    (hp : q.Prime) (hq : (g j).val<q) (hcap : (q:ℝ)≤H)
    (hproduct : d*(fullList ⟨g,q⟩).prod≤N) :
    q∈physical (prefixProduct g) ((N:ℝ)/d) (g j).val H := by
  have hr : (d:ℝ)*((fullList ⟨g,q⟩).prod:ℝ)≤N := by exact_mod_cast hproduct
  have hprod : ((fullList ⟨g,q⟩).prod:ℝ)=prefixProduct g*q := by
    simp [fullList,List.prod_ofFn,prefixProduct,Nat.cast_prod]
  rw [hprod] at hr
  apply mem_filter.mpr
  refine ⟨(mem_primesIcc hH).mpr ⟨hp,Nat.cast_nonneg _,hcap⟩,?_,?_⟩
  · exact_mod_cast hq
  · apply (le_div_iff₀ (Nat.cast_pos.mpr hd)).mpr
    simpa only [mul_comm] using hr

/-- Reusable finite full-list injection. No multiplication image identifies
two different labelled source lists. -/
theorem product_count_le_physical {N d n : ℕ} {R H : ℝ}
    (L : Finset (List ℕ)) (S : Finset (Fin n → primeSlabPrimes R)) (j : Fin n)
    (hgeometry : ∀l∈L,∃y∈S.sigma
      (fun g => physical (prefixProduct g) ((N:ℝ)/d) (g j).val H),fullList y=l) :
    (L.card:ℝ)≤∑g∈S,((physical (prefixProduct g) ((N:ℝ)/d) (g j).val H).card:ℝ) := by
  let T := S.sigma (fun g => physical (prefixProduct g) ((N:ℝ)/d) (g j).val H)
  let f (l : L) : T := ⟨(hgeometry l.val l.property).choose,
    (hgeometry l.val l.property).choose_spec.1⟩
  have hf (l : L) : fullList (f l).val=l.val :=
    (hgeometry l.val l.property).choose_spec.2
  have hinj : Function.Injective f := by
    intro l l' heq
    apply Subtype.ext
    exact (hf l).symm.trans
      ((congrArg (fun y : T => fullList y.val) heq).trans (hf l'))
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_coe] at hc
  have hcr : (L.card:ℝ)≤(T.card:ℝ) := by exact_mod_cast hc
  simpa [T,card_sigma] using hcr

/-- The actual five-prime word maps to the four-prefix physical chart. -/
theorem geometry20 {N d : ℕ} {Q : ℝ} (hd : 0<d) (hR : 1<Q/d)
    {l : List ℕ} (hl : l∈productLabels N Q d [2,3,3,3,3]) :
    ∃y∈(HighUnit.primePrefix20 (Q/d) a2 a3 b).sigma
      (fun g => physical (prefixProduct g) ((N:ℝ)/d) (g (Fin.last 3)).val ((Q/d)^b)),
      fullList y=l := by
  obtain ⟨hl,hproduct⟩ := mem_filter.mp hl
  rw [labels_power] at hl
  obtain ⟨htup,hcol⟩ := mem_filter.mp hl
  obtain ⟨hlen,hord,hm⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp htup
  obtain ⟨p0,p1,p2,p3,p4,rfl⟩ := length_five hlen
  have hc : secondFunctionalMotherColour ((Q/d)^a1) ((Q/d)^a2) ((Q/d)^a3) p0=2 ∧
      secondFunctionalMotherColour ((Q/d)^a1) ((Q/d)^a2) ((Q/d)^a3) p1=3 ∧
      secondFunctionalMotherColour ((Q/d)^a1) ((Q/d)^a2) ((Q/d)^a3) p2=3 ∧
      secondFunctionalMotherColour ((Q/d)^a1) ((Q/d)^a2) ((Q/d)^a3) p3=3 ∧
      secondFunctionalMotherColour ((Q/d)^a1) ((Q/d)^a2) ((Q/d)^a3) p4=3 := by
    simpa using hcol
  have ho : p0<p1 ∧ p1<p2 ∧ p2<p3 ∧ p3<p4 := by
    simp [List.pairwise_cons] at hord
    exact ⟨hord.1.1,hord.2.1.1,hord.2.2.1.1,hord.2.2.2⟩
  have hlo : (Q/d)^a2≤(p0:ℝ) := (colour_two hc.1).1
  have hslab (p : ℕ) (hp : p∈[p0,p1,p2,p3,p4]) (h0p : p0≤p) :
      p∈primeSlabPrimes (Q/d) := by
    apply slab_of_window hR (by norm_num [a2] : 1/10≤a2)
      (by norm_num [b] : b≤1/2) (hm p hp)
    exact hlo.trans (by exact_mod_cast h0p)
  let z0 : primeSlabPrimes (Q/d) := ⟨p0,hslab p0 (by simp) le_rfl⟩
  let z1 : primeSlabPrimes (Q/d) := ⟨p1,hslab p1 (by simp) (by omega)⟩
  let z2 : primeSlabPrimes (Q/d) := ⟨p2,hslab p2 (by simp) (by omega)⟩
  let z3 : primeSlabPrimes (Q/d) := ⟨p3,hslab p3 (by simp) (by omega)⟩
  let g : Fin 4 → primeSlabPrimes (Q/d) := ![z0,z1,z2,z3]
  have hg : g∈HighUnit.primePrefix20 (Q/d) a2 a3 b := by
    simp only [HighUnit.primePrefix20,mem_filter,mem_univ,true_and]
    change (Q/d)^a2≤(p0:ℝ) ∧ (p0:ℝ)<(Q/d)^a3 ∧ (Q/d)^a3≤(p1:ℝ) ∧
      p1<p2 ∧ p2<p3 ∧ (p3:ℝ)<(Q/d)^b
    exact ⟨hlo,(colour_two hc.1).2,colour_three hc.2.1,ho.2.1,ho.2.2.1,
      (mem_primeWindow.mp (hm p3 (by simp))).2.2.2⟩
  have hfull : fullList ⟨g,p4⟩=[p0,p1,p2,p3,p4] := by
    simp [fullList,g,List.ofFn_succ,z0,z1,z2,z3]
  have hp4 := mem_primeWindow.mp (hm p4 (by simp))
  refine ⟨⟨g,p4⟩,mem_sigma.mpr ⟨hg,?_⟩,hfull⟩
  apply physical_of_product hd (Real.rpow_nonneg (zero_lt_one.trans hR).le _) g
    (Fin.last 3) hp4.1 (show p3<p4 from ho.2.2.2) hp4.2.2.2.le
  simpa only [hfull] using hproduct

/-- The actual six-prime word has a separate five-prefix chart. -/
theorem geometry21 {N d : ℕ} {Q : ℝ} (hd : 0<d) (hR : 1<Q/d)
    {l : List ℕ} (hl : l∈productLabels N Q d [3,3,3,3,3,3]) :
    ∃y∈(HighUnit.primePrefix21 (Q/d) a3 b).sigma
      (fun g => physical (prefixProduct g) ((N:ℝ)/d) (g (Fin.last 4)).val ((Q/d)^b)),
      fullList y=l := by
  obtain ⟨hl,hproduct⟩ := mem_filter.mp hl
  rw [labels_power] at hl
  obtain ⟨htup,hcol⟩ := mem_filter.mp hl
  obtain ⟨hlen,hord,hm⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp htup
  obtain ⟨p0,p1,p2,p3,p4,p5,rfl⟩ := length_six hlen
  have hc : secondFunctionalMotherColour ((Q/d)^a1) ((Q/d)^a2) ((Q/d)^a3) p0=3 := by
    have hh := congrArg (fun xs : List ℕ => xs.getD 0 0) hcol
    simpa using hh
  have ho : p0<p1 ∧ p1<p2 ∧ p2<p3 ∧ p3<p4 ∧ p4<p5 := by
    simp [List.pairwise_cons] at hord
    exact ⟨hord.1.1,hord.2.1.1,hord.2.2.1.1,hord.2.2.2.1.1,hord.2.2.2.2⟩
  have hlo : (Q/d)^a3≤(p0:ℝ) := colour_three hc
  have hslab (p : ℕ) (hp : p∈[p0,p1,p2,p3,p4,p5]) (h0p : p0≤p) :
      p∈primeSlabPrimes (Q/d) := by
    apply slab_of_window hR (by norm_num [a3] : 1/10≤a3)
      (by norm_num [b] : b≤1/2) (hm p hp)
    exact hlo.trans (by exact_mod_cast h0p)
  let z0 : primeSlabPrimes (Q/d) := ⟨p0,hslab p0 (by simp) le_rfl⟩
  let z1 : primeSlabPrimes (Q/d) := ⟨p1,hslab p1 (by simp) (by omega)⟩
  let z2 : primeSlabPrimes (Q/d) := ⟨p2,hslab p2 (by simp) (by omega)⟩
  let z3 : primeSlabPrimes (Q/d) := ⟨p3,hslab p3 (by simp) (by omega)⟩
  let z4 : primeSlabPrimes (Q/d) := ⟨p4,hslab p4 (by simp) (by omega)⟩
  let g : Fin 5 → primeSlabPrimes (Q/d) := ![z0,z1,z2,z3,z4]
  have hg : g∈HighUnit.primePrefix21 (Q/d) a3 b := by
    simp only [HighUnit.primePrefix21,mem_filter,mem_univ,true_and]
    change (Q/d)^a3≤(p0:ℝ) ∧ p0<p1 ∧ p1<p2 ∧ p2<p3 ∧ p3<p4 ∧
      (p4:ℝ)<(Q/d)^b
    exact ⟨hlo,ho.1,ho.2.1,ho.2.2.1,ho.2.2.2.1,
      (mem_primeWindow.mp (hm p4 (by simp))).2.2.2⟩
  have hfull : fullList ⟨g,p5⟩=[p0,p1,p2,p3,p4,p5] := by
    simp [fullList,g,List.ofFn_succ,z0,z1,z2,z3,z4]
  have hp5 := mem_primeWindow.mp (hm p5 (by simp))
  refine ⟨⟨g,p5⟩,mem_sigma.mpr ⟨hg,?_⟩,hfull⟩
  apply physical_of_product hd (Real.rpow_nonneg (zero_lt_one.trans hR).le _) g
    (Fin.last 4) hp5.1 (show p4<p5 from ho.2.2.2.2) hp5.2.2.2.le
  simpa only [hfull] using hproduct

/-- Both O unsifted unit masses, not their prime-filtered subcarriers. -/
theorem actual_unit_masses_le_physical {N d : ℕ} {Q : ℝ}
    (hd : 0<d) (hR : 1<Q/d) :
    unitWordMass N Q d [2,3,3,3,3]≤physical20 N Q d ∧
    unitWordMass N Q d [3,3,3,3,3,3]≤physical21 N Q d := by
  constructor
  · rw [unitWordMass_eq_product_count hd]
    exact product_count_le_physical (productLabels N Q d _) _ (Fin.last 3)
      (fun _ hl => geometry20 hd hR hl)
  · rw [unitWordMass_eq_product_count hd]
    exact product_count_le_physical (productLabels N Q d _) _ (Fin.last 4)
      (fun _ hl => geometry21 hd hR hl)

end
end ImbalancedChen.P2EnhancedUnitSourceGeometry
