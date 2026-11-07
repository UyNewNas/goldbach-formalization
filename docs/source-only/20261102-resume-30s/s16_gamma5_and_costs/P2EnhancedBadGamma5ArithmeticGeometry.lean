import ImbalancedChen.P2EnhancedBadGamma5PrimeQuadrature
import ImbalancedChen.P2EnhancedShortWordUnitBound

/-! SOURCE ONLY / UNCOMPILED.
The actual old-target-deleted, strictly ordered low-band prime LISTS are
injected into the closed bad-square reciprocal quadrature. Unit atoms
are cardinalities, including equality, and are paid independently. -/
namespace ImbalancedChen.P2EnhancedBadGamma5ArithmeticGeometry
noncomputable section
open Real Finset Set Filter MeasureTheory Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedSwitchedUnsiftedSource P2EnhancedSwitchedTrueNormalization
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedNonunitWordMass (rawScale)
open P2SeedOmegaLiteralFibre (a0 a2 corner badLower)
open P2EnhancedBadGamma5PrimeQuadrature
open scoped Classical BigOperators Topology

def badLabels (N : ℕ) (Q : ℝ) (d : ℕ) : Finset (List ℕ) :=
  (pairLabels N Q d).filter (badPair Q d)

def ordinaryBad (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ l ∈ badLabels N Q d,
    ((roughNumbers ((N : ℝ)/(d*l.prod : ℕ)) (cutoff Q d (227/50))).card : ℝ)

def ordinaryBadNonunit (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ l ∈ badLabels N Q d,
    (((roughNumbers ((N : ℝ)/(d*l.prod : ℕ)) (cutoff Q d (227/50))).erase 1).card : ℝ)

def badUnit (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ l ∈ badLabels N Q d, (unitCarrier N d l (cutoff Q d (227/50))).card

def labelReciprocal (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ l ∈ badLabels N Q d, 1/(l.prod : ℝ)

theorem pair_data {N d : ℕ} {Q : ℝ} {l : List ℕ} (hl : l ∈ pairLabels N Q d) :
    l.length=2 ∧ l.Pairwise (· < ·) ∧
      ∀ p ∈ l, p ∈ primeWindow N ((Q/d)^a0) ((Q/d)^a2) := by
  have ht := (secondFunctionalMother_tuple_mem _ _ _).mp hl
  simpa only [pairLabels,cutoff,show (1/(227/50) : ℝ)=a0 by norm_num [a0],
    show (1/(29/10) : ℝ)=a2 by norm_num [a2]] using ht

theorem pair_eq {N d : ℕ} {Q : ℝ} {l : List ℕ} (hl : l ∈ pairLabels N Q d) :
    l=[l.getD 0 0,l.getD 1 0] := by
  have hh := (pair_data hl).1
  cases l with
  | nil => simp at hh
  | cons p ps =>
    cases ps with
    | nil => simp at hh
    | cons q qs =>
      have he : qs=[] := List.length_eq_zero.mp (by simpa using hh)
      subst qs
      rfl

theorem pair_primes {N d : ℕ} {Q : ℝ} {l : List ℕ} (hl : l ∈ pairLabels N Q d) :
    (l.getD 0 0).Prime ∧ (l.getD 1 0).Prime := by
  have hh := (pair_data hl).2.2
  rw [pair_eq hl] at hh
  exact ⟨(mem_primeWindow.mp (hh _ (by simp))).1,
    (mem_primeWindow.mp (hh _ (by simp))).1⟩

theorem pair_prod_pos {N d : ℕ} {Q : ℝ} {l : List ℕ} (hl : l ∈ pairLabels N Q d) :
    0 < l.prod := by
  have hh := pair_primes hl
  rw [pair_eq hl]
  simpa using Nat.mul_pos hh.1.pos hh.2.pos

theorem original_unit_partition {N d : ℕ} {Q : ℝ} (hd : 0 < d) :
    ordinaryBad N Q d = badUnit N Q d+ordinaryBadNonunit N Q d := by
  unfold ordinaryBad badUnit ordinaryBadNonunit
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro l hl
  have hp := pair_prod_pos (mem_filter.mp hl).1
  have hD := Nat.mul_pos hd hp
  have hcap : (1 : ℝ) ≤ (N : ℝ)/(d*l.prod : ℕ) ↔ d*l.prod ≤ N := by
    rw [le_div_iff₀ (Nat.cast_pos.mpr hD),one_mul]
    exact_mod_cast Iff.rfl
  rw [InclusiveRoughUniform.card_eq_unit_add_erase_real,unit_card hD,hcap]
  split_ifs <;> norm_num

/-- The original bad equality is kept. This is an injection of LISTS,
not a presumed injection of their products. -/
theorem bad_label_mem_closed {N d : ℕ} {Q : ℝ} (hd : 0 < d) (hR : 1 < Q/d)
    {l : List ℕ} (hl : l ∈ badLabels N Q d) :
    (l.getD 0 0,l.getD 1 0) ∈ closedPairs (Q/d) := by
  obtain ⟨hl,hbad⟩ := mem_filter.mp hl
  have hdata := pair_data hl
  have hpr := pair_primes hl
  let p := l.getD 0 0
  let q := l.getD 1 0
  have he : l=[p,q] := pair_eq hl
  have hpw := mem_primeWindow.mp (hdata.2.2 p (by rw [he]; simp))
  have hqw := mem_primeWindow.mp (hdata.2.2 q (by rw [he]; simp))
  have hpc := (gamma5Mass_coordinate_mem_iff hR p).mp
    ((mem_primesIcc (rpow_nonneg (zero_lt_one.trans hR).le _)).mpr
      ⟨hpw.1,hpw.2.2.1,hpw.2.2.2.le⟩)
  have hqc := (gamma5Mass_coordinate_mem_iff hR q).mp
    ((mem_primesIcc (rpow_nonneg (zero_lt_one.trans hR).le _)).mpr
      ⟨hqw.1,hqw.2.2.1,hqw.2.2.2.le⟩)
  have hpq : p < q := by simpa [he] using hdata.2.1
  have horder := (gamma5Mass_coordinate_le_iff hR hpw.1 hqw.1).mpr hpq.le
  rw [he] at hbad
  have hg := (P2EnhancedBadGamma5ConstantCutoff.actual_bad_square hd hpw.1.pos hqw.1.pos hR).mp hbad
  change 1 ≤ 2*gamma5MassCoordinate (Q/d) p+gamma5MassCoordinate (Q/d) q at hg
  have hcorner : corner ≤ gamma5MassCoordinate (Q/d) p := by
    norm_num [corner,a2] at hqc ⊢
    linarith
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨(gamma5Mass_coordinate_mem_iff hR p).mpr
    ⟨hpw.1,hcorner,hpc.2.2⟩,(gamma5Mass_coordinate_mem_iff hR q).mpr hqc⟩,?_⟩
  exact max_le horder (by linarith)

theorem label_reciprocal_le_closed {N d : ℕ} {Q : ℝ} (hd : 0 < d) (hR : 1 < Q/d) :
    labelReciprocal N Q d ≤ reciprocalMass (Q/d) := by
  let f := fun l : List ℕ => (l.getD 0 0,l.getD 1 0)
  have hinj : Set.InjOn f (badLabels N Q d) := by
    intro l hl l' hl' hh
    rw [pair_eq (mem_filter.mp hl).1,pair_eq (mem_filter.mp hl').1]
    exact congrArg (fun pq : ℕ×ℕ => [pq.1,pq.2]) hh
  have hsub : (badLabels N Q d).image f ⊆ closedPairs (Q/d) := by
    intro pq hpq
    obtain ⟨l,hl,rfl⟩ := mem_image.mp hpq
    exact bad_label_mem_closed hd hR hl
  have hs := sum_le_sum_of_subset_of_nonneg hsub
    (fun pq _ _ => by positivity : ∀ pq ∈ closedPairs (Q/d),
      pq ∉ (badLabels N Q d).image f → 0 ≤ 1/((pq.1 : ℝ)*pq.2))
  rw [sum_image (fun l hl l' hl' hh => hinj hl hl' hh)] at hs
  have he : (∑ l ∈ badLabels N Q d, 1/(((f l).1 : ℝ)*(f l).2)) =
      labelReciprocal N Q d := by
    apply sum_congr rfl
    intro l hl
    rw [pair_eq (mem_filter.mp hl).1]
    simp [f]
  rw [he] at hs
  exact hs

theorem bad_unit_coarse : ∀ᶠ R : ℝ in atTop,
    ∀ (N d : ℕ) (Q : ℝ), 0 < d → Q/d=R → badUnit N Q d ≤ 625*R^(20/11 : ℝ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),reciprocal_mass_coarse] with R hR hm
  intro N d Q hd hQR
  have hR' : 1 < Q/d := by simpa only [hQR] using hR
  have hrec := (label_reciprocal_le_closed hd hR').trans (by simpa only [hQR] using hm)
  have hcount : badUnit N Q d ≤ ((badLabels N Q d).card : ℝ) := by
    unfold badUnit
    calc
      _ ≤ ∑ l ∈ badLabels N Q d, (1 : ℝ) := by
        apply sum_le_sum
        intro l hl
        rw [unit_card (Nat.mul_pos hd (pair_prod_pos (mem_filter.mp hl).1))]
        split_ifs <;> norm_num
      _ = _ := by simp
  have hprod (l : List ℕ) (hl : l ∈ badLabels N Q d) :
      (l.prod : ℝ) ≤ R^(20/11 : ℝ) := by
    have hpair := (mem_filter.mp hl).1
    have hdata := pair_data hpair
    have he := pair_eq hpair
    have hp := mem_primeWindow.mp (hdata.2.2 (l.getD 0 0) (by rw [he]; simp))
    have hq := mem_primeWindow.mp (hdata.2.2 (l.getD 1 0) (by rw [he]; simp))
    have hh := mul_le_mul hp.2.2.2.le hq.2.2.2.le (Nat.cast_nonneg _) (by positivity)
    rw [hQR,← rpow_add (zero_lt_one.trans hR)] at hh
    rw [he]
    simpa using hh.trans (rpow_le_rpow_of_exponent_le hR.le (by norm_num [a2]))
  calc
    _ ≤ ((badLabels N Q d).card : ℝ) := hcount
    _ ≤ R^(20/11 : ℝ)*labelReciprocal N Q d := by
      rw [labelReciprocal,mul_sum]
      calc
        _ = ∑ l ∈ badLabels N Q d, (1 : ℝ) := by simp
        _ ≤ _ := sum_le_sum fun l hl => by
          rw [mul_one_div,le_div_iff₀
            (Nat.cast_pos.mpr (pair_prod_pos (mem_filter.mp hl).1)),one_mul]
          exact hprod l hl
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hrec
      (rpow_nonneg (zero_lt_one.trans hR).le (20/11 : ℝ))]

/-- Actual quotient-one Gamma5 atoms, with the original equality square.
The threshold precedes Q,d and no positive total mass is divided out. -/
theorem actual_bad_unit_upper {eta epsilon : ℝ} (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ d : ℕ,
      0 < d → (N : ℝ)^eta ≤ Q/d → 2 ≤ trueAlpha N Q d →
      badUnit N Q d ≤ epsilon*rawScale N Q d := by
  have hlarge : ∀ᶠ R : ℝ in atTop, 6875/epsilon ≤ R^(1/11 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/11)).eventually_ge_atTop _
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp (bad_unit_coarse.and hlarge)
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop R0)
  refine ⟨max 4 T0,le_max_left _ _,?_⟩
  intro N hN Q d hd hscale ha
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hR : 1 < Q/d := (one_lt_rpow
    (by exact_mod_cast (show 1 < N by omega)) heta).trans_le hscale
  have hh := hR0 (Q/d) ((hT0 N ((le_max_right _ _).trans hN)).trans hscale)
  have hX : (Q/d)^(2 : ℝ) ≤ (N : ℝ)/d := by
    rw [← P2EnhancedUnitSourceMass.scale_identity (by omega : 0 < N) hd hR]
    exact rpow_le_rpow_of_exponent_le hR.le ha
  have hpay := P2EnhancedShortWordUnitBound.power_gap_absorption hR he hh.2
    (hh.1 N d Q hd rfl) hX
  simpa only [rawScale,div_div] using hpay

end
end ImbalancedChen.P2EnhancedBadGamma5ArithmeticGeometry
