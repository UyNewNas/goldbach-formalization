import ImbalancedChen.P5OriginalGroupLogAbelVariation
import ImbalancedChen.P5ActualUpperOrderedHBSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
One literal ordered HB occurrence is varied, leaving every other occurrence
and every original group in place. This proves the source dictionary for
the reciprocal-group-log Abel multiplier and derives its logarithmic floor
from the actual upper profile, uniformly over occupied individual blocks.
-/
namespace ImbalancedChen.P5Z.ActualHBGroupLogLine
noncomputable section
open Classical Filter Set MeasureTheory
open scoped BigOperators Topology
open PerGroupIntegerHBAtlasPushforward HBRightClosedDyadicRoles
open LicensedOriginalIntegerProfile ActualUpperOrderedHBSource
open ImbalancedChen.P5ActualIndependentUpperPairProfile
open ImbalancedChen.P5ActualUpperPairHBLogTransport
open OriginalGroupLogAbelVariation
open ImbalancedChen.Part3.PrimeMellinProfileVariation20261026b

def rowLine (before after : List Row) (j : ℕ) (bs : List Block)
    (left right : List ℕ) (n : ℕ) : List Row :=
  before ++ {order := j,blocks := bs,factors := left ++ n :: right} :: after

def sameGroupFactor (left right : List ℕ) : ℕ := left.prod*right.prod

def otherGroupLogs (before after : List Row) : ℝ :=
  wordLog (originalProducts before)*wordLog (originalProducts after)

def completeOtherProduct (before after : List Row) (left right : List ℕ) : ℕ :=
  (originalProducts before).prod*sameGroupFactor left right*(originalProducts after).prod

theorem rowLine_product (before after : List Row) (j : ℕ) (bs : List Block)
    (left right : List ℕ) (n : ℕ) :
    (originalProducts (rowLine before after j bs left right n)).prod =
      completeOtherProduct before after left right*n := by
  simp only [rowLine,originalProducts,List.map_append,List.map_cons,
    List.prod_append,List.prod_cons,completeOtherProduct,sameGroupFactor]
  ring

theorem wordLog_append (xs ys : List ℕ) :
    wordLog (xs++ys) = wordLog xs*wordLog ys := by
  induction xs with
  | nil => simp [wordLog]
  | cons x xs ih => simp only [List.cons_append,wordLog,ih]; ring

/-- Every OTHER original group remains in H. Inside the varying original
group, A is exactly the product of the other factors, with multiplicity. -/
theorem rowLine_wordLog (before after : List Row) (j : ℕ) (bs : List Block)
    (left right : List ℕ) (n : ℕ) :
    wordLog (originalProducts (rowLine before after j bs left right n)) =
      otherGroupLogs before after *
        Real.log ((sameGroupFactor left right : ℕ)*n : ℕ) := by
  have hprod : (left++n::right).prod = sameGroupFactor left right*n := by
    simp only [List.prod_append,List.prod_cons,sameGroupFactor]
    ring
  simp only [rowLine,originalProducts,List.map_append,List.map_cons,
    wordLog_append,wordLog,hprod,otherGroupLogs]
  ring

/-- Exact arithmetic dictionary, even at zero/unit group products. The
test can include any original sign, prefix and count/mean kernel. -/
theorem rowLine_normalized_test (before after : List Row) (j : ℕ)
    (bs : List Block) (left right : List ℕ) (Phi : ℝ → ℝ)
    (t U : ℝ) (n : ℕ) (c : ℂ) :
    physicalProfile Phi t U n*c /
      (wordLog (originalProducts (rowLine before after j bs left right n)) : ℂ) =
      normalizedProfile Phi t U (sameGroupFactor left right)
        (otherGroupLogs before after) n*c := by
  rw [rowLine_wordLog,normalizedProfile_eq_div]
  push_cast
  ring

theorem wordLog_ge_pow (ell : ℝ) (hell : 0 ≤ ell) :
    ∀ ns : List ℕ, (∀ n ∈ ns, ell ≤ Real.log (n : ℝ)) →
      ell^ns.length ≤ wordLog ns := by
  intro ns
  induction ns with
  | nil => intro h; simp [wordLog]
  | cons n ns ih =>
    intro h
    have hn := h n (by simp)
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simp only [wordLog,List.length_cons,pow_succ]
    calc
      _ = ell*ell^ns.length := by ring
      _ ≤ _ := mul_le_mul hn ht (pow_nonneg hell _) (hell.trans hn)

/-- This floor is obtained from the actual normalized upper test. It is
not a new support assertion supplied by a normalized-SW caller. -/
theorem actual_upperTest_group_lower (D : Parameters) (b : Band D)
    (N : ℕ) (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ)
    {rows : List Row} (hn : upperTest D b N kappa0 Q rho rows ≠ 0)
    {row : Row} (hrow : row ∈ rows) :
    2 ≤ N ∧ (N : ℝ)^D.theta < (row.factors.prod : ℝ) := by
  have hWc : (listExtension (ActualIndependentUpperPairLogFields.licence D b N)
      (originalProducts rows) : ℂ) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  have hW : listExtension (ActualIndependentUpperPairLogFields.licence D b N)
      (originalProducts rows) ≠ 0 := by
    intro hz
    exact hWc (by rw [hz]; rfl)
  have hlen : (originalProducts rows).length = 2 := by
    by_contra hl
    exact hW (by simp only [listExtension,dif_neg hl])
  have hnorm : ActualIndependentUpperPairLogFields.profile D b N
      (fun i => (wordVector 2 (originalProducts rows) i : ℝ)) ≠ 0 := by
    change integerExtension (ActualIndependentUpperPairLogFields.licence D b N)
      (wordVector 2 (originalProducts rows)) ≠ 0
    rw [← listExtension_ofFn,ofFn_wordVector hlen]
    exact hW
  have hdata := ActualIndependentUpperPairLogFields.actual_endpoint_product_fields D b hnorm
  have hm : row.factors.prod ∈ originalProducts rows :=
    List.mem_map.mpr ⟨row,hrow,rfl⟩
  obtain ⟨i,hi,hget⟩ := List.mem_iff_getElem.mp hm
  have hi2 : i < 2 := by omega
  have heq : wordVector 2 (originalProducts rows) ⟨i,hi2⟩ = row.factors.prod := by
    simpa only [wordVector,List.getD_eq_getElem _ _ hi] using hget
  exact ⟨hdata.1,by simpa only [heq] using hdata.2.1 ⟨i,hi2⟩⟩

/-- All frozen original-group logarithms are also uniformly positive on
the SAME source. Their multiplicity is the original row-list length. -/
theorem actual_otherGroupLogs_bound (D : Parameters) (b : Band D) (N : ℕ)
    (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ)
    (before after : List Row) (j : ℕ) (bs : List Block) (left right : List ℕ)
    (n : ℕ) (hn : upperTest D b N kappa0 Q rho
      (rowLine before after j bs left right n) ≠ 0) :
    2 ≤ N ∧
      (D.theta*Real.log (N : ℝ))^(before.length+after.length) ≤
        otherGroupLogs before after ∧ 0 < otherGroupLogs before after := by
  have hmem : ({order := j,blocks := bs,factors := left++n::right} : Row) ∈
      rowLine before after j bs left right n := by simp [rowLine]
  have hN := (actual_upperTest_group_lower D b N kappa0 Q rho hn hmem).1
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let ell := D.theta*Real.log (N : ℝ)
  have hell : 0 < ell := mul_pos D.theta_pos (Real.log_pos hN1)
  have hlog (row : Row) (hr : row ∈ rowLine before after j bs left right n) :
      ell ≤ Real.log (row.factors.prod : ℝ) := by
    dsimp [ell]
    rw [← Real.log_rpow hNp]
    exact Real.log_le_log (Real.rpow_pos_of_pos hNp _)
      (actual_upperTest_group_lower D b N kappa0 Q rho hn hr).2.le
  have hb : ell^before.length ≤ wordLog (originalProducts before) := by
    have hh := wordLog_ge_pow ell hell.le (originalProducts before) (by
      intro a ha
      obtain ⟨row,hr,rfl⟩ := List.mem_map.mp ha
      exact hlog row (List.mem_append.mpr (Or.inl hr)))
    simpa only [originalProducts,List.length_map] using hh
  have ha : ell^after.length ≤ wordLog (originalProducts after) := by
    have hh := wordLog_ge_pow ell hell.le (originalProducts after) (by
      intro a ha
      obtain ⟨row,hr,rfl⟩ := List.mem_map.mp ha
      exact hlog row (List.mem_append.mpr
        (Or.inr (List.mem_cons_of_mem _ hr))))
    simpa only [originalProducts,List.length_map] using hh
  have hbound : ell^(before.length+after.length) ≤ otherGroupLogs before after := by
    rw [pow_add,otherGroupLogs]
    exact mul_le_mul hb ha (pow_nonneg hell.le _) ((pow_pos hell _).le.trans hb)
  exact ⟨hN,hbound,(pow_pos hell _).trans_le hbound⟩

/-- One occupied point in (U,2U] forces the WHOLE coordinate interval's
original-group log away from zero. Only a factor two is lost; no new sharp
group-product wall is inserted in the rectangle. -/
theorem actual_occupied_line_floor (D : Parameters) (b : Band D) (N : ℕ)
    (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ)
    (before after : List Row) (j : ℕ) (bs : List Block) (left right : List ℕ)
    {n : ℕ} {U : ℝ} (hU : 0 < U) (hnU : (n : ℝ) ≤ 2*U)
    (hlarge : 2 ≤ (N : ℝ)^(D.theta/2))
    (hn : upperTest D b N kappa0 Q rho
      (rowLine before after j bs left right n) ≠ 0) :
    0 < (sameGroupFactor left right : ℝ) ∧
      0 < (D.theta/2)*Real.log (N : ℝ) ∧
      (D.theta/2)*Real.log (N : ℝ) ≤
        Real.log ((sameGroupFactor left right : ℝ)*U) := by
  have hmem : ({order := j,blocks := bs,factors := left++n::right} : Row) ∈
      rowLine before after j bs left right n := by simp [rowLine]
  obtain ⟨hN,hgroup⟩ := actual_upperTest_group_lower D b N kappa0 Q rho hn hmem
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hprod : ((left++n::right).prod : ℝ) =
      (sameGroupFactor left right : ℝ)*n := by
    simp only [List.prod_append,List.prod_cons,sameGroupFactor,Nat.cast_mul]
    ring
  change (N : ℝ)^D.theta < ((left++n::right).prod : ℝ) at hgroup
  rw [hprod] at hgroup
  have hA : 0 < (sameGroupFactor left right : ℝ) := by
    have hh := (Real.rpow_pos_of_pos hNp D.theta).trans hgroup
    by_contra h
    have hz : (sameGroupFactor left right : ℝ) = 0 :=
      le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    rw [hz,zero_mul] at hh
    exact (lt_irrefl 0) hh
  have hpow : (N : ℝ)^D.theta = ((N : ℝ)^(D.theta/2))^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hNp.le]
    congr 1
    ring
  have hscaled := mul_le_mul_of_nonneg_left hnU hA.le
  have hhalf : (N : ℝ)^(D.theta/2) ≤ (sameGroupFactor left right : ℝ)*U := by
    rw [hpow] at hgroup
    have hsquare := mul_le_mul_of_nonneg_right hlarge
      (Real.rpow_pos_of_pos hNp (D.theta/2)).le
    nlinarith only [hsquare,hgroup,hscaled]
  refine ⟨hA,mul_pos (by linarith [D.theta_pos]) (Real.log_pos hN1),?_⟩
  rw [← Real.log_rpow hNp]
  exact Real.log_le_log (Real.rpow_pos_of_pos hNp _) hhalf

/-- One threshold is chosen BEFORE the row, occurrence, dyadic scale,
beta/prefix, modulus and residue data. -/
theorem eventually_actual_occupied_line_floor (D : Parameters) :
    ∀ᶠ N : ℕ in atTop, ∀ (b : Band D) (kappa0 : ℝ)
      (Q : Finset ℕ) (rho : ℕ → ℂ) (before after : List Row)
      (j : ℕ) (bs : List Block) (left right : List ℕ) (n : ℕ) (U : ℝ),
      0 < U → (n : ℝ) ≤ 2*U →
      upperTest D b N kappa0 Q rho (rowLine before after j bs left right n) ≠ 0 →
      0 < (sameGroupFactor left right : ℝ) ∧
        0 < (D.theta/2)*Real.log (N : ℝ) ∧
        (D.theta/2)*Real.log (N : ℝ) ≤
          Real.log ((sameGroupFactor left right : ℝ)*U) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(D.theta/2)) atTop atTop :=
    (Real.tendsto_rpow_atTop (by linarith [D.theta_pos])).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (2 : ℝ)] with N hlarge
  intro b kappa0 Q rho before after j bs left right n U hU hnU hn
  exact actual_occupied_line_floor D b N kappa0 Q rho before after j bs left right
    hU hnU hlarge hn

/-- The genuine reciprocal-log variation on an occupied original upper
HB line. No denominator floor is supplied by the caller: it is proved
from that same original source and its physical positive-prime margin. -/
theorem actual_occupied_line_variation (D : Parameters) (b : Band D) (N : ℕ)
    (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ)
    (before after : List Row) (j : ℕ) (bs : List Block) (left right : List ℕ)
    {n : ℕ} {U u v M E : ℝ} (hU : 0 < U) (hnU : (n : ℝ) ≤ 2*U)
    (hlarge : 2 ≤ (N : ℝ)^(D.theta/2))
    (hn : upperTest D b N kappa0 Q rho
      (rowLine before after j bs left right n) ≠ 0)
    (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    (hM0 : 0 ≤ M) (hE0 : 0 ≤ E)
    (hM : ∀ x ∈ Icc (1 : ℝ) 2, |Phi x| ≤ M)
    (hE : ∀ x ∈ Icc (1 : ℝ) 2, |deriv Phi x| ≤ E)
    (hlo : U ≤ u) (huv : u ≤ v) (hhi : v ≤ 2*U) (t : ℝ) :
    let ell := (D.theta/2)*Real.log (N : ℝ)
    let f := normalizedProfile Phi t U (sameGroupFactor left right)
      (otherGroupLogs before after)
    ‖f v‖ + (∫ y in Ioc u v, ‖deriv f y‖) ≤
      |otherGroupLogs before after|⁻¹*((M+E)/ell+M/ell^2)*(1+|t|) := by
  obtain ⟨hA,hell,hfloor⟩ := actual_occupied_line_floor D b N kappa0 Q rho
    before after j bs left right hU hnU hlarge hn
  exact normalizedProfile_variation_le hPhi hM0 hE0 hM hE hU hA hell
    hlo huv hhi hfloor t

end
end ImbalancedChen.P5Z.ActualHBGroupLogLine
