import ImbalancedChen.P5U7OriginalComponentCollarDictionary

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Mixed-cutoff rough-row reconstruction for spatial product counts. M is the
physical product cutoff; the arithmetic carrier, excluded prime divisors,
and original marked pair all retain target N. No substitution N:=M is made.
The exact ordered-pair image retains repeated terminal factors. Unit and
inclusive endpoint losses are explicit in the final rough-mother bound.
-/
namespace ImbalancedChen
noncomputable section
open LiLiuPrereqBuchstab
open scoped BigOperators
open Classical

def p5U7MassSemiprimeWindow (N M : ℕ) (t : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N).filter (fun u =>
    t.2 ≤ u.1 ∧ u.1 ≤ u.2 ∧ t.1*t.2*(u.1*u.2) < M)

def p5U7SpatialGoodRough (N M : ℕ) (t : ℕ × ℕ) : Finset ℕ :=
  (roughNumbers ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ)) (t.2 : ℝ)).filter
    (fun q => q ≠ 1 ∧ Nat.Coprime q N ∧ t.1*t.2*q < M)

def p5U7SpatialRoughEndpoint (M : ℕ) (t : ℕ × ℕ) : Finset ℕ :=
  (roughNumbers ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ)) (t.2 : ℝ)).filter
    (fun q => t.1*t.2*q=M)

theorem p5U7MassSemiprimeWindow_subset {N M : ℕ} (hMN : M ≤ N) (t : ℕ × ℕ) :
    p5U7MassSemiprimeWindow N M t ⊆ p5U7MassSemiprimePairs N t := by
  intro u hu
  obtain ⟨hc,hw,ho,hm⟩ := Finset.mem_filter.mp hu
  exact Finset.mem_filter.mpr ⟨hc,hw,ho,hm.trans_le hMN⟩

/-- Exact actual target-N source reconstruction at independent cutoff M.
The prime fibre on the right is the literal mixed window, not target M. -/
theorem p5U7SpatialGoodRough_eq_components {N M : ℕ} (hMN : M ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ chenY7PrimeSelector N ((N : ℝ)^(59/250 : ℝ))) :
    p5U7SpatialGoodRough N M t =
      ((chenAdditivePrimeCarrier N).filter (fun q => t.2 ≤ q ∧ t.1*t.2*q<M)) ∪
        (p5U7MassSemiprimeWindow N M t).image (fun u => u.1*u.2) := by
  have ha := (p5U7Mass_outer_geometry ht).1
  have haR : (0 : ℝ) < ((t.1*t.2 : ℕ) : ℝ) := by exact_mod_cast ha
  ext q
  constructor
  · intro hq
    obtain ⟨hqR,hn,hcop,hstrict⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq0,_,hrough⟩ := mem_roughNumbers.mp hqR
    have hsource := p5U7Arithmetic_rough_nonunit_mem_three_or_four ht hq0 hn hcop
      (hstrict.trans_le hMN) hrough
    rcases hsource with hp | ⟨r,s,hprod,hs⟩
    · obtain ⟨hc,hw,_⟩ := Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc,hw,hstrict⟩)
    · obtain ⟨hc,hw,ho,_⟩ := Finset.mem_filter.mp (Finset.mem_sigma.mp hs).2
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(r,s),
        Finset.mem_filter.mpr ⟨hc,hw,ho,by simpa only [hprod] using hstrict⟩,hprod.symm⟩)
  · intro hq
    rcases Finset.mem_union.mp hq with hp | hs
    · obtain ⟨hc,hw,hm⟩ := Finset.mem_filter.mp hp
      have hp := mem_chenAdditivePrimeCarrier.mp hc
      have hmr : ((t.1*t.2 : ℕ) : ℝ)*(q : ℝ) < M := by exact_mod_cast hm
      have hrough : ChenPrimeRough (t.2 : ℝ) q := by
        intro p hprime hd
        have heq := (Nat.prime_dvd_prime_iff_eq hprime hp.2.1).mp hd
        subst p
        exact_mod_cast hw
      exact Finset.mem_filter.mpr ⟨mem_roughNumbers.mpr ⟨hp.2.1.pos,
        ((lt_div_iff₀ haR).mpr (by simpa only [mul_comm] using hmr)).le,hrough⟩,
        hp.2.1.ne_one,hp.2.2,hm⟩
    · obtain ⟨⟨r,s⟩,hrs,rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨hc,hw,ho,hm⟩ := Finset.mem_filter.mp hrs
      obtain ⟨hrc,hsc⟩ := Finset.mem_product.mp hc
      have hr := mem_chenAdditivePrimeCarrier.mp hrc
      have hs := mem_chenAdditivePrimeCarrier.mp hsc
      have hmr : ((t.1*t.2 : ℕ) : ℝ)*((r*s : ℕ) : ℝ) < M := by exact_mod_cast hm
      have hrough : ChenPrimeRough (t.2 : ℝ) (r*s) := by
        intro p hp hd
        rcases hp.dvd_mul.mp hd with hdr | hds
        · have heq := (Nat.prime_dvd_prime_iff_eq hp hr.2.1).mp hdr
          subst p
          exact_mod_cast hw
        · have heq := (Nat.prime_dvd_prime_iff_eq hp hs.2.1).mp hds
          subst p
          exact_mod_cast hw.trans ho
      have hn : r*s ≠ 1 := by
        have hle := Nat.le_mul_of_pos_right r hs.2.1.pos
        have htwo := hr.2.1.two_le
        omega
      exact Finset.mem_filter.mpr ⟨mem_roughNumbers.mpr ⟨mul_pos hr.2.1.pos hs.2.1.pos,
        ((lt_div_iff₀ haR).mpr (by simpa only [mul_comm] using hmr)).le,hrough⟩,
        hn,hr.2.2.mul_left hs.2.2,hm⟩

/-- Ordered pair-to-product is injective within each retained marked row,
including r=s; the prime image is disjoint from this composite image. -/
theorem p5U7SpatialGoodRough_card_eq_components {N M : ℕ} (hMN : M ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ chenY7PrimeSelector N ((N : ℝ)^(59/250 : ℝ))) :
    (p5U7SpatialGoodRough N M t).card =
      ((chenAdditivePrimeCarrier N).filter (fun q => t.2 ≤ q ∧ t.1*t.2*q<M)).card +
        (p5U7MassSemiprimeWindow N M t).card := by
  have hsub := p5U7MassSemiprimeWindow_subset hMN t
  have hinj : Set.InjOn (fun u : ℕ × ℕ => u.1*u.2) (p5U7MassSemiprimeWindow N M t) := by
    intro a ha b hb hab
    exact p5U7ComponentSemiprime_product_injOn N t (hsub ha) (hsub hb) hab
  have hd : Disjoint ((chenAdditivePrimeCarrier N).filter (fun q => t.2 ≤ q ∧ t.1*t.2*q<M))
      ((p5U7MassSemiprimeWindow N M t).image (fun u => u.1*u.2)) := by
    apply Finset.disjoint_left.mpr
    intro q hp hs
    have hprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1
    have hs' : q ∈ p5U7ComponentSemiprimeCofactors N t := by
      obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp hs
      exact Finset.mem_image.mpr ⟨u,hsub hu,heq⟩
    exact p5U7ComponentSemiprime_not_prime hs' hprime
  rw [p5U7SpatialGoodRough_eq_components hMN ht,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injOn hinj]

theorem p5U7SpatialRoughEndpoint_card_le_one {M : ℕ} {t : ℕ × ℕ}
    (ha : 0 < t.1*t.2) : (p5U7SpatialRoughEndpoint M t).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro q hq r hr
  exact Nat.eq_of_mul_eq_mul_left ha
    ((Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hr).2.symm)

/-- Rough-mother correction at cutoff M pays prime divisors of ORIGINAL N,
plus a literal unit and possible endpoint a*q=M. -/
theorem p5U7SpatialRough_gap_le {N M : ℕ} (hN : 0 < N)
    {t : ℕ × ℕ} (ht : t ∈ chenY7PrimeSelector N ((N : ℝ)^(59/250 : ℝ))) :
    0 ≤ (roughCount ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ)-
      ((p5U7SpatialGoodRough N M t).card : ℝ) ∧
    (roughCount ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ)-
      ((p5U7SpatialGoodRough N M t).card : ℝ) ≤
      (Real.log (N : ℝ)/Real.log 2)*
        (((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))/(t.2 : ℝ))+2 := by
  let x : ℝ := (M : ℝ)/((t.1*t.2 : ℕ) : ℝ)
  let R := roughNumbers x (t.2 : ℝ)
  let G := p5U7SpatialGoodRough N M t
  let B := p5U7ActualBadRough N x (t.2 : ℝ)
  let E := p5U7SpatialRoughEndpoint M t
  have ha := (p5U7Mass_outer_geometry ht).1
  have haR : (0 : ℝ) < ((t.1*t.2 : ℕ) : ℝ) := by exact_mod_cast ha
  have hc := (Finset.mem_filter.mp ht).1
  have hp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).2).2.1
  have hz : (0 : ℝ) < t.2 := by exact_mod_cast hp.pos
  have hcover : R ⊆ G ∪ B ∪ ({1} : Finset ℕ) ∪ E := by
    intro q hq
    obtain ⟨hq0,hqx,hrough⟩ := mem_roughNumbers.mp hq
    by_cases hone : q=1
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp only [hone,Finset.mem_singleton]))
    by_cases hcop : Nat.Coprime q N
    · have hmulR : ((t.1*t.2 : ℕ) : ℝ)*(q : ℝ) ≤ M := by
        have hh := (le_div_iff₀ haR).mp hqx
        simpa only [mul_comm] using hh
      have hmul : t.1*t.2*q ≤ M := by exact_mod_cast hmulR
      by_cases hstrict : t.1*t.2*q<M
      · have hg : q ∈ G := Finset.mem_filter.mpr ⟨hq,hone,hcop,hstrict⟩
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hg))
      · have heq : t.1*t.2*q=M := by omega
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq,heq⟩)
    · have hb : q ∈ B := Finset.mem_filter.mpr ⟨hq,hcop⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hb))
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_union_le G B
  have h3 := Finset.card_union_le (G ∪ B) ({1} : Finset ℕ)
  have h4 := Finset.card_union_le (G ∪ B ∪ ({1} : Finset ℕ)) E
  have hE : E.card ≤ 1 := p5U7SpatialRoughEndpoint_card_le_one ha
  have hOne : ({1} : Finset ℕ).card=1 := Finset.card_singleton 1
  have hcard : R.card ≤ G.card+B.card+2 := by omega
  have hcast : (R.card : ℝ) ≤ (G.card : ℝ)+(B.card : ℝ)+2 := by exact_mod_cast hcard
  have hbad := p5U7ActualBadRough_card_le_log hN
    (div_nonneg (Nat.cast_nonneg M) haR.le) hz
  have hsub : G ⊆ R := Finset.filter_subset _ _
  have hlow : (G.card : ℝ) ≤ (R.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  change 0 ≤ (R.card : ℝ)-(G.card : ℝ) ∧
    (R.card : ℝ)-(G.card : ℝ) ≤ (Real.log (N : ℝ)/Real.log 2)*(x/(t.2 : ℝ))+2
  exact ⟨by linarith only [hlow],by linarith only [hcast,hbad]⟩

end
end ImbalancedChen
