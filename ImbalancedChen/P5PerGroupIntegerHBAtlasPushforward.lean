import ImbalancedChen.P5LicensedOriginalIntegerProfile

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Exact normalized rough Lambda-source atlas, NOT a prime-source identity.
-- Every original chart coordinate keeps its OWN y_i=(2R_i)^(1/3).
namespace ImbalancedChen.P5Z.PerGroupIntegerHBAtlasPushforward
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.Part3
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open ActualHBDyadicProductWindow ActualHBMediumBranchPartition
open SmoothChartHBDyadicPartition ExactOriginalSmoothDyadicPartition
open LicensedOriginalIntegerProfile

def hbCutoff (cj : ℕ) : ℝ := (2*R cj)^(1/3 : ℝ)
def hbCap (cj : ℕ) : ℕ := 2^(cj+1)

structure Row where
  order : ℕ
  blocks : List Block
  factors : List ℕ

def originalProducts (rows : List Row) : List ℕ := rows.map (fun r => r.factors.prod)

def singleSum (z : ℝ) (cj n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range 3, scalar j *
    ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)), blockCoefficient z (hbCutoff cj) j n bs

def singleSource (chi : ℝ → ℝ) (z : ℝ) (cj n : ℕ) : ℂ :=
  psi chi ((n : ℝ)/R cj) *
    (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)*roughOneSlot z n) /
      (Real.log (n : ℝ) : ℂ)

def sourceTuple (chi : ℝ → ℝ) (z : ℝ) : List ℕ → List ℕ → ℂ
  | [],[] => 1
  | cj::cjs,n::ns => singleSource chi z cj n * sourceTuple chi z cjs ns
  | _,_ => 0

theorem single_source_identity (chi : ℝ → ℝ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    {z : ℝ} (hz : 0 ≤ z) (cj n : ℕ) :
    singleSource chi z cj n = psi chi ((n : ℝ)/R cj)/(Real.log (n : ℝ) : ℂ) *
      singleSum z cj n := by
  by_cases hpsi : psi chi ((n : ℝ)/R cj) = 0
  · simp [singleSource,hpsi]
  have hR := R_pos cj
  have hbase : 0 < 2*R cj := by positivity
  have hy : 0 ≤ hbCutoff cj := (Real.rpow_pos_of_pos hbase (1/3 : ℝ)).le
  have hcube : (hbCutoff cj)^3 = 2*R cj := by
    unfold hbCutoff
    rw [← Real.rpow_natCast,← Real.rpow_mul hbase.le]
    norm_num
  have hquot : (n : ℝ)/R cj ≤ 2 := by
    apply le_of_not_gt
    intro h
    exact hpsi (psi_right chi hzero _ h)
  have hnReal : (n : ℝ) ≤ 2*R cj := (div_le_iff₀ hR).mp hquot
  have hcap : (hbCap cj : ℝ) = 2*R cj := by
    unfold hbCap R
    push_cast
    rw [pow_succ]
    ring
  have hn : n ≤ hbCap cj := by
    have hh : (n : ℝ) ≤ (hbCap cj : ℝ) := by rw [hcap]; exact hnReal
    exact_mod_cast hh
  have hncube : (n : ℝ) ≤ (hbCutoff cj)^3 := by rw [hcube]; exact hnReal
  have hHB := fixed_bank_HB hz hy (hbCap cj) hn hncube
  change ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)*roughOneSlot z n = singleSum z cj n at hHB
  unfold singleSource
  rw [hHB]
  ring

-- A finite dependent atlas written as iterated finite sums. Its carriers
-- are the actual order-3 words, fixed chart-cap block banks, and literal
-- ordered factorTuples. No surjectivity or final kernel equality is input.
def atlasEval (chi : ℝ → ℝ) (z : ℝ) :
    List ℕ → List ℕ → (List Row → ℂ) → ℂ
  | [],[],F => F []
  | cj::cjs,n::ns,F =>
      psi chi ((n : ℝ)/R cj)/(Real.log (n : ℝ) : ℂ) *
        ∑ j ∈ Finset.range 3, scalar j *
          ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
            ∑ fs ∈ factorTuples (2*(j+1)) n,
              assignedWeight z (hbCutoff cj) (roles j) bs fs *
                atlasEval chi z cjs ns
                  (fun rows => F ({order:=j,blocks:=bs,factors:=fs}::rows))
  | _,_,_ => 0

private theorem sum_constant (z : ℝ) (cj n : ℕ) (C : ℂ) :
    (∑ j ∈ Finset.range 3, scalar j *
      ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
        ∑ fs ∈ factorTuples (2*(j+1)) n,
          assignedWeight z (hbCutoff cj) (roles j) bs fs*C) = singleSum z cj n*C := by
  unfold singleSum blockCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp_rw [← Finset.sum_mul]
  ring

-- This is coefficient/carrier pushforward for EVERY coordinate-dependent
-- list test K, not merely a function of the complete product.
theorem atlas_coordinate_pushforward (chi : ℝ → ℝ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0) {z : ℝ} (hz : 0 ≤ z) :
    ∀ cjs ns : List ℕ, ∀ K : List ℕ → ℂ,
      atlasEval chi z cjs ns (fun rows => K (originalProducts rows)) =
        sourceTuple chi z cjs ns*K ns := by
  intro cjs
  induction cjs with
  | nil => intro ns K; cases ns <;> simp [atlasEval,sourceTuple,originalProducts]
  | cons cj cjs ih =>
    intro ns K
    cases ns with
    | nil => simp [atlasEval,sourceTuple]
    | cons n ns =>
      let C : ℂ := sourceTuple chi z cjs ns*K (n::ns)
      have hinner :
          (∑ j ∈ Finset.range 3, scalar j *
            ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
              ∑ fs ∈ factorTuples (2*(j+1)) n,
                assignedWeight z (hbCutoff cj) (roles j) bs fs *
                  atlasEval chi z cjs ns (fun rows =>
                    K (originalProducts ({order:=j,blocks:=bs,factors:=fs}::rows)))) =
          ∑ j ∈ Finset.range 3, scalar j *
            ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
              ∑ fs ∈ factorTuples (2*(j+1)) n,
                assignedWeight z (hbCutoff cj) (roles j) bs fs*C := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        apply Finset.sum_congr rfl
        intro bs hbs
        apply Finset.sum_congr rfl
        intro fs hfs
        congr 1
        change atlasEval chi z cjs ns (fun rows => K (fs.prod::originalProducts rows)) = C
        rw [ih ns (fun us => K (fs.prod::us)),(factorTuples_spec (2*(j+1)) n fs hfs).2.1]
      change psi chi ((n : ℝ)/R cj)/(Real.log (n : ℝ) : ℂ) * _ = _
      rw [hinner,sum_constant]
      rw [sourceTuple,single_source_identity chi hone hzero hz cj n]
      dsimp [C]
      ring

theorem atlasEval_add (chi : ℝ → ℝ) (z : ℝ) :
    ∀ cjs ns : List ℕ, ∀ F G : List Row → ℂ,
      atlasEval chi z cjs ns (fun rows => F rows+G rows) =
        atlasEval chi z cjs ns F + atlasEval chi z cjs ns G := by
  intro cjs
  induction cjs with
  | nil => intro ns F G; cases ns <;> simp [atlasEval]
  | cons cj cjs ih =>
    intro ns F G
    cases ns with
    | nil => simp [atlasEval]
    | cons n ns =>
      simp only [atlasEval]
      simp_rw [ih,mul_add,Finset.sum_add_distrib]

def mediumValue (A B : ℝ) (F : List Row → ℂ) (rows : List Row) : ℂ :=
  if firstMedium A B (rows.flatMap Row.blocks) = none then 0 else F rows

def typeIValue (A B : ℝ) (F : List Row → ℂ) (rows : List Row) : ℂ :=
  if firstMedium A B (rows.flatMap Row.blocks) = none then F rows else 0

theorem atlas_exact_branch_partition (chi : ℝ → ℝ) (z A B : ℝ)
    (cjs ns : List ℕ) (F : List Row → ℂ) :
    atlasEval chi z cjs ns F = atlasEval chi z cjs ns (mediumValue A B F) +
      atlasEval chi z cjs ns (typeIValue A B F) := by
  calc
    _ = atlasEval chi z cjs ns (fun rows => mediumValue A B F rows+typeIValue A B F rows) := by
      congr 1
      funext rows
      by_cases h : firstMedium A B (rows.flatMap Row.blocks) = none <;>
        simp [mediumValue,typeIValue,h]
    _ = _ := atlasEval_add chi z cjs ns _ _

-- The constructed licensed INTEGER profile and SAME complete eta are
-- pulled back exactly. Proper-prime-power and collision corrections are
-- deliberately absent: this theorem starts from the rough Lambda source.
theorem licensed_profile_atlas_identity {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0) {z : ℝ} (hz : 0 ≤ z)
    (T kappa0 : ℝ) (cjs ns : List ℕ) (F : List ℕ → ℂ) :
    atlasEval chi z cjs ns (fun rows =>
      (listExtension L (originalProducts rows) : ℂ) *
        (eta (((originalProducts rows).prod : ℝ)/T^(1-kappa0)) : ℂ) * F (originalProducts rows)) =
      sourceTuple chi z cjs ns *
        ((listExtension L ns : ℂ)*(eta ((ns.prod : ℝ)/T^(1-kappa0)) : ℂ)*F ns) :=
  atlas_coordinate_pushforward chi hone hzero hz cjs ns
    (fun us => (listExtension L us : ℂ)*(eta ((us.prod : ℝ)/T^(1-kappa0)) : ℂ)*F us)

end
end ImbalancedChen.P5Z.PerGroupIntegerHBAtlasPushforward
