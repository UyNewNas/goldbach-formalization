import ImbalancedChen.P5ActualHBGroupLogLine
import ImbalancedChen.P5OriginalBetaPrimeHalfOpenSW

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact Abel summation with a COMPUTED finite prefix maximum, followed by
the original ordered HB-row source dictionary. No bound for that maximum
and no SW estimate for a rough one/Mobius/log slot is a hypothesis here.
The genuinely missing cancellation of those prefixes remains OPEN.
-/
namespace ImbalancedChen.P5Z.ActualHBGroupLogAbelPrefix
noncomputable section
open Classical Finset Set MeasureTheory
open scoped BigOperators Topology
open ImbalancedChen.Part3
open OriginalBetaPrimeSource OriginalBetaPrimeHalfOpenSW
open OriginalGroupLogAbelVariation ActualHBGroupLogLine
open ActualRoughHeathBrownWords PerGroupIntegerHBAtlasPushforward HBRightClosedDyadicRoles
open ImbalancedChen.P5ActualUpperPairHBLogTransport
open PrimeMellinProfileVariation20261026b
open IndependentPrimeSourceWordDictionary
open ImbalancedChen.P5ActualIndependentUpperPairProfile ActualUpperOrderedHBSource

def prefix (c : ℕ → ℂ) (u : ℝ) (q b h : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc (Nat.floor u) h, c n*exactKernel q b n

/-- Finite maximum of the literal signed primitive-discrepancy prefixes.
It is a mathematical finite sup, never a numerically executed certificate. -/
def prefixNorm (c : ℕ → ℂ) (u v : ℝ) (q b : ℕ) : ℝ :=
  (Finset.range (Nat.floor v+1)).sup' (by simp)
    (fun h => ‖prefix c u q b h‖)

theorem prefixNorm_nonneg (c : ℕ → ℂ) (u v : ℝ) (q b : ℕ) :
    0 ≤ prefixNorm c u v q b := by
  exact (norm_nonneg (prefix c u q b 0)).trans
    (Finset.le_sup' _ (by simp : 0 ∈ Finset.range (Nat.floor v+1)))

theorem prefix_le (c : ℕ → ℂ) (u v : ℝ) (q b : ℕ) {y : ℝ} (hy : y ≤ v) :
    ‖prefix c u q b (Nat.floor y)‖ ≤ prefixNorm c u v q b := by
  apply Finset.le_sup'
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono hy))

/-- The exact Abel identity retains the right endpoint and has zero left
prefix by definition. The mean is the SAME c-weighted coprime mass / phi(q). -/
theorem exact_Abel (c : ℕ → ℂ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (f : ℝ → ℂ) (hfd : ∀ y ∈ Icc u v, DifferentiableAt ℝ f y)
    (hfi : IntegrableOn (deriv f) (Icc u v)) (q b : ℕ) :
    auxiliarySWError (Finset.Ioc (Nat.floor u) (Nat.floor v))
      (fun n => f n*c n) 1 q b =
      f v*prefix c u q b (Nat.floor v) -
        ∫ y in Ioc u v, deriv f y*prefix c u q b (Nat.floor y) := by
  let d : ℕ → ℂ := fun n => if Nat.floor u < n then c n*exactKernel q b n else 0
  have hs (h : ℕ) : (∑ n ∈ Finset.Icc 0 h, d n) = prefix c u q b h := by
    have heq : (Finset.Icc 0 h).filter (fun n => Nat.floor u < n) =
        Finset.Ioc (Nat.floor u) h := by
      ext n
      simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
      omega
    simp only [d,← Finset.sum_filter,heq,prefix]
  have hz : (∑ n ∈ Finset.Icc 0 (Nat.floor u), d n) = 0 := by
    rw [hs]
    simp [prefix]
  rw [error_eq_kernel]
  have hsum : (∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
      f n*c n*exactKernel q b n) =
      ∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v), f n*d n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [d,if_pos (Finset.mem_Ioc.mp hn).1,mul_assoc]
  rw [hsum,sum_mul_eq_sub_sub_integral_mul d hu huv hfd hfi,hz,mul_zero,sub_zero]
  simp_rw [hs]

/-- No cancellation hypothesis: this is a bound by the exact finite
prefix maximum. In particular no arbitrary divisor-bounded SW class is
introduced when the normalized multiplier is used. -/
theorem Abel_bound_by_actual_prefix (c : ℕ → ℂ) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (f : ℝ → ℂ)
    (hfd : ∀ y ∈ Icc u v, DifferentiableAt ℝ f y)
    (hfi : IntegrableOn (deriv f) (Icc u v)) (q b : ℕ) :
    ‖auxiliarySWError (Finset.Ioc (Nat.floor u) (Nat.floor v))
      (fun n => f n*c n) 1 q b‖ ≤
      prefixNorm c u v q b * (‖f v‖ + ∫ y in Ioc u v, ‖deriv f y‖) := by
  have hmajor : IntegrableOn (fun y => ‖deriv f y‖*prefixNorm c u v q b) (Ioc u v) :=
    (hfi.mono_set Ioc_subset_Icc_self).norm.mul_const _
  have hint : ‖∫ y in Ioc u v, deriv f y*prefix c u q b (Nat.floor y)‖ ≤
      (∫ y in Ioc u v, ‖deriv f y‖)*prefixNorm c u v q b := by
    have hh := norm_integral_le_of_norm_le hmajor (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (prefix_le c u v q b hy.2) (norm_nonneg _))
    simpa only [integral_mul_const] using hh
  rw [exact_Abel c hu huv f hfd hfi]
  calc
    _ ≤ ‖f v*prefix c u q b (Nat.floor v)‖ +
        ‖∫ y in Ioc u v, deriv f y*prefix c u q b (Nat.floor y)‖ := norm_sub_le _ _
    _ ≤ ‖f v‖*prefixNorm c u v q b +
        (∫ y in Ioc u v, ‖deriv f y‖)*prefixNorm c u v q b :=
      add_le_add (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left
        (prefix_le c u v q b le_rfl) (norm_nonneg _)) hint
    _ = _ := by ring

/-- The rough role is exactly the signed original real-cutoff HB role.
The original group denominator and every other group log are paid, with
Mellin frequency and the finite primitive prefix maximum both explicit. -/
theorem actual_role_normalized_prefix_bound (z y : ℝ) (role : Role)
    {Phi : ℝ → ℝ} (hPhi : ContDiff ℝ 1 Phi)
    {M D U A H ell u v : ℝ} (hM0 : 0 ≤ M) (hD0 : 0 ≤ D)
    (hM : ∀ x ∈ Icc (1 : ℝ) 2, |Phi x| ≤ M)
    (hD : ∀ x ∈ Icc (1 : ℝ) 2, |deriv Phi x| ≤ D)
    (hU : 0 < U) (hA : 0 < A) (hell : 0 < ell)
    (hlo : U ≤ u) (huv : u ≤ v) (hhi : v ≤ 2*U)
    (hfloor : ell ≤ Real.log (A*U)) (t : ℝ) (q b : ℕ) :
    ‖auxiliarySWError (Finset.Ioc (Nat.floor u) (Nat.floor v))
      (fun n => normalizedProfile Phi t U A H n*actual z y role n) 1 q b‖ ≤
      prefixNorm (actual z y role) u v q b *
        (|H|⁻¹*((M+D)/ell+M/ell^2)*(1+|t|)) := by
  have hfd : ∀ a ∈ Icc u v,
      DifferentiableAt ℝ (normalizedProfile Phi t U A H) a := by
    intro a ha
    exact (normalizedProfile_hasDerivAt hPhi t H hU hA
      (hU.trans_le (hlo.trans ha.1))
      (hell.trans_le (log_floor_on_interval hA hU hlo hfloor a ha)).ne').differentiableAt
  have hcont : ContinuousOn (deriv (normalizedProfile Phi t U A H)) (Icc u v) := by
    intro a ha
    have ha0 := hU.trans_le (hlo.trans ha.1)
    have hl := hell.trans_le (log_floor_on_interval hA hU hlo hfloor a ha)
    have hp : ContDiffAt ℝ 1 (physicalProfile Phi t U) a :=
      (physicalProfile_contDiffOn hPhi t hU).contDiffAt (isOpen_Ioi.mem_nhds ha0)
    have hr := reciprocalGroupLog_contDiffAt hA ha0 hl.ne'
    have hh : ContDiffAt ℝ 1 (normalizedProfile Phi t U A H) a :=
      (contDiffAt_const.mul hp).mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp a hr)
    exact (hh.derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  exact (Abel_bound_by_actual_prefix (actual z y role) (hU.le.trans hlo) huv _
    hfd hcont.integrableOn_Icc q b).trans
      (mul_le_mul_of_nonneg_left
        (normalizedProfile_variation_le hPhi hM0 hD0 hM hD hU hA hell
          hlo huv hhi hfloor t) (prefixNorm_nonneg _ _ _ _ _))

/-- Concrete actual-source consumer: the only arithmetic quantity on the
right is the literal finite prefix maximum, with no unproved estimate
assumed. The original occupied source itself supplies the log floor. -/
theorem actual_occupied_role_prefix_bound (D : Parameters) (b : Band D) (N : ℕ)
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
    (hlo : U ≤ u) (huv : u ≤ v) (hhi : v ≤ 2*U)
    (z y : ℝ) (role : Role) (t : ℝ) (q residue : ℕ) :
    let ell := (D.theta/2)*Real.log (N : ℝ)
    ‖auxiliarySWError (Finset.Ioc (Nat.floor u) (Nat.floor v))
      (fun a => normalizedProfile Phi t U (sameGroupFactor left right)
        (otherGroupLogs before after) a * actual z y role a) 1 q residue‖ ≤
      prefixNorm (actual z y role) u v q residue *
        (|otherGroupLogs before after|⁻¹*((M+E)/ell+M/ell^2)*(1+|t|)) := by
  obtain ⟨hA,hell,hfloor⟩ := actual_occupied_line_floor D b N kappa0 Q rho
    before after j bs left right hU hnU hlarge hn
  exact actual_role_normalized_prefix_bound z y role hPhi hM0 hE0 hM hE
    hU hA hell hlo huv hhi hfloor t q residue

theorem roughTupleWeight_split (z y : ℝ) :
    ∀ (rs : List Role) (ps : List ℕ), rs.length = ps.length →
    ∀ (role : Role) (tailRoles : List Role) (tailFactors : List ℕ) (n : ℕ),
    roughTupleWeight z y (rs++role::tailRoles) (ps++n::tailFactors) =
      roughTupleWeight z y rs ps * actual z y role n *
        roughTupleWeight z y tailRoles tailFactors := by
  intro rs
  induction rs with
  | nil =>
    intro ps hlen role tailRoles tailFactors n
    have hp : ps = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    subst ps
    simp only [List.nil_append,roughTupleWeight,one_mul]
  | cons r rs ih =>
    intro ps hlen role tailRoles tailFactors n
    cases ps with
    | nil => simp at hlen
    | cons p ps =>
      have hlen' : rs.length = ps.length := by simpa using hlen
      simp only [List.cons_append,roughTupleWeight,ih ps hlen']
      ring

/-- This is the literal row-line source before estimating it. The complete
multiplier d has not been inverted in a nonunit case. The SAME phi(q)
coprime mean is retained by J's proved primitive-product kernel identity. -/
theorem actual_row_normalized_discrepancy (S : Finset ℕ)
    (before after : List Row) (j : ℕ) (bs : List Block)
    (left right : List ℕ) (rs tailRoles : List Role) (role : Role)
    (hlen : rs.length = left.length) (z y : ℝ)
    (Phi : ℝ → ℝ) (t U : ℝ) (d q b : ℕ) (hb : b.Coprime q) :
    (∑ n ∈ S,
      roughTupleWeight z y (rs++role::tailRoles) (left++n::right) *
        physicalProfile Phi t U n /
          (wordLog (originalProducts (rowLine before after j bs left right n)) : ℂ) *
            exactKernel q b (d*n)) =
      if d.Coprime q then
        (roughTupleWeight z y rs left * roughTupleWeight z y tailRoles right) *
          auxiliarySWError S
            (fun n => normalizedProfile Phi t U (sameGroupFactor left right)
              (otherGroupLogs before after) n * actual z y role n)
            1 q (pulledResidue d q b)
      else 0 := by
  by_cases hd : d.Coprime q
  · rw [if_pos hd,error_eq_kernel,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [roughTupleWeight_split z y rs left hlen,
      exactKernel_product hb,if_pos hd,rowLine_wordLog,normalizedProfile_eq_div]
    push_cast
    ring
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro n hn
    rw [exactKernel_product hb,if_neg hd,mul_zero]

theorem residueKernel_eq_exactKernel (q T n : ℕ) :
    ImbalancedChen.PrimeProducts.MellinInsertion20261028.residueKernel q T n =
      exactKernel q T n := by
  rw [residueKernel_real]
  by_cases ha : Nat.ModEq q n T <;> by_cases hc : n.Coprime q <;>
    simp [exactKernel,ha,hc]

/-- The complete multiplier is the ACTUAL ordered product of the other
independent occurrences. The physical coefficient rho remains untouched,
including its beta factor, prefixes and original residual normalization. -/
theorem rowLine_wordKernel (before after : List Row) (j : ℕ) (bs : List Block)
    (left right : List ℕ) (n T : ℕ) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    wordKernel Q rho T (originalProducts (rowLine before after j bs left right n)) =
      ∑ q ∈ Q, rho q * exactKernel q T
        (completeOtherProduct before after left right*n) := by
  unfold wordKernel
  simp_rw [rowLine_product,residueKernel_eq_exactKernel]

/-- Native complete-modulus HB source, after the literal per-row split.
There is still one signed sum over the original Q and rho. In particular
no replacement of rho by an absolute or re-normalized coefficient occurs. -/
theorem actual_row_same_rho_discrepancy (S : Finset ℕ)
    (before after : List Row) (j : ℕ) (bs : List Block)
    (left right : List ℕ) (rs tailRoles : List Role) (role : Role)
    (hlen : rs.length = left.length) (hroles : roles j = rs++role::tailRoles) (z y : ℝ)
    (Phi : ℝ → ℝ) (t U : ℝ) (T : ℕ) (Q : Finset ℕ) (rho : ℕ → ℂ)
    (hprimitive : ∀ q ∈ Q, T.Coprime q) :
    (∑ n ∈ S,
      roughTupleWeight z y (roles j) (left++n::right) *
        physicalProfile Phi t U n /
          (wordLog (originalProducts (rowLine before after j bs left right n)) : ℂ) *
            wordKernel Q rho T
              (originalProducts (rowLine before after j bs left right n))) =
      ∑ q ∈ Q, rho q *
        (if (completeOtherProduct before after left right).Coprime q then
          (roughTupleWeight z y rs left * roughTupleWeight z y tailRoles right) *
            auxiliarySWError S
              (fun n => normalizedProfile Phi t U (sameGroupFactor left right)
                (otherGroupLogs before after) n * actual z y role n)
              1 q (pulledResidue (completeOtherProduct before after left right) q T)
        else 0) := by
  rw [hroles]
  simp_rw [rowLine_wordKernel,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← actual_row_normalized_discrepancy S before after j bs left right rs tailRoles
    role hlen z y Phi t U (completeOtherProduct before after left right) q T
      (hprimitive q hq),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Unit arithmetic atoms remain separate. A unit LOG occurrence vanishes;
it is not replaced by a singular division by log(1) at that occurrence. -/
theorem actual_log_role_unit (z y : ℝ) : actual z y .logarithm 1 = 0 := by
  simp only [actual,roughLog,Nat.cast_one,Real.log_one,Complex.ofReal_zero,zero_mul]

end
end ImbalancedChen.P5Z.ActualHBGroupLogAbelPrefix
