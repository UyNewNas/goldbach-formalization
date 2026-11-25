import ImbalancedChen.Part3ActualReciprocalSquarePoisson
import ImbalancedChen.Part3ActualSeparatedRowLogModeSupplier

/-!
SOURCEONLY / UNCOMPILED / ONE minimal P3 joint-beta candidate.
Proposed module: ImbalancedChen.Part3ActualCompletedSquarePushforward.
The sole direct import is a genuine actual P2 source, SHA619ad4f5; ROOT's
installation record8813b494 explicitly says P0/P1/P2 are NOT YET QUALIFIED.
Original499ad442 L8-L165 and L360-L445 plus its two final closures supply
the exact joint-beta finite pushforward and actual support proofs below.
Only two existing Real cast proofs receive explicit type annotations.
No Gram373, divisor/Gram budget, collision estimate, actual07/Mass6/M2
prefix or spectral/P8 assumption is copied or imported by this module.
ROOT alone controls actual installation, compilation and acceptance.
-/

namespace ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
noncomputable section
open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open ActualReciprocalSquarePoissonSourceOnly ActualPositiveLatticeSmoothCoverSourceOnly
open scoped BigOperators SchwartzMap FourierTransform
attribute [local instance] Classical.propDecidable

abbrev Source := ℤ × (Inner × Inner)
abbrev Output := ℕ × ℤ

def rawCarrier (T : Finset ℕ) (H : ℕ) (F : Finset ℤ) : Finset Source :=
  F ×ˢ (finiteInnerCarrier T H ×ˢ finiteInnerCarrier T H)

def carrier (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : Finset ℤ) : Finset Source :=
  (rawCarrier T H F).filter (fun s => s.1 ≠ 0 ∧ fixedUnit A a s.2.1.1 ∧ fixedUnit A a s.2.2.1)

def output (s : Source) : Output := (level s.2.1 s.2.2, outputY s.1 s.2.1 s.2.2)

def weight (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (s : Source) : ℂ :=
  atomCoeff lambda omega s.2.1 * star (atomCoeff lambda omega s.2.2)

def zeroSource (U : Finset Source) : Finset Source := U.filter (fun s => (output s).2 = 0)
def positiveSource (U : Finset Source) : Finset Source := U.filter (fun s => 0 < (output s).2)
def negativeSource (U : Finset Source) : Finset Source := U.filter (fun s => (output s).2 < 0)
def nonzeroSource (U : Finset Source) : Finset Source := U.filter (fun s => (output s).2 ≠ 0)

def fiber (U : Finset Source) (zy : Output) : Finset Source := U.filter (fun s => output s = zy)

def beta (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (zy : Output) : ℂ :=
  ∑ s ∈ fiber U zy, weight lambda omega s

/-- Exact joint coefficient pushforward. Captured fixed lambda/omega do
not acquire a b,c or future Poisson m argument. -/
theorem weighted_pushforward (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (K : Output → ℂ) :
    (∑ s ∈ U, weight lambda omega s * K (output s)) =
      ∑ zy ∈ U.image output, beta U lambda omega zy * K zy := by
  have hf := sum_fiberwise_of_maps_to (s := U) (t := U.image output) (g := output)
    (fun s hs => mem_image_of_mem _ hs) (fun s => weight lambda omega s * K (output s))
  rw [← hf]
  apply sum_congr rfl
  intro zy hzy
  unfold beta
  rw [sum_mul]
  apply sum_congr rfl
  intro s hs
  rw [(mem_filter.mp hs).2]

/-- Exact y0/nonzero split, before any estimate and independent of m0. -/
theorem sum_zero_nonzero (U : Finset Source) (g : Source → ℂ) :
    (∑ s ∈ U, g s) = (∑ s ∈ zeroSource U, g s) + ∑ s ∈ nonzeroSource U, g s := by
  simp only [zeroSource, nonzeroSource, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro s hs
  by_cases hy : (output s).2 = 0
  · simp [hy]
  · simp [hy]

theorem sum_positive_negative (U : Finset Source) (g : Source → ℂ) :
    (∑ s ∈ nonzeroSource U, g s) =
      (∑ s ∈ positiveSource U, g s) + ∑ s ∈ negativeSource U, g s := by
  simp only [nonzeroSource, positiveSource, negativeSource, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro s hs
  by_cases hz : (output s).2 = 0
  · simp only [hz, ne_eq, not_true_eq_false, if_false, lt_self_iff_false, zero_add]
  · by_cases hp : 0 < (output s).2
    · have hn : ¬(output s).2 < 0 := by omega
      simp only [if_pos hz, if_pos hp, if_neg hn, add_zero]
    · have hn : (output s).2 < 0 := by omega
      simp only [if_pos hz, if_neg hp, if_pos hn, zero_add]

/-- A grouped coefficient has no hidden support: a nonzero beta supplies
an original source witness. -/
theorem beta_ne_zero_mem_image {U : Finset Source} {lambda : ℕ → ℂ} {omega : ℤ → ℂ}
    {zy : Output} (hb : beta U lambda omega zy ≠ 0) : zy ∈ U.image output := by
  by_contra hn
  apply hb
  apply sum_eq_zero
  intro s hs
  exact False.elim (hn (mem_image.mpr ⟨s,(mem_filter.mp hs).1,(mem_filter.mp hs).2⟩))

/-- Only the residue-unit condition remains in the completed kernel;
all fixed t-unit conditions already belong to beta's source carrier. -/
def completedKernel (M N C : ℝ) (a : ℤ) (zy : Output) : ℂ :=
  ∑ c ∈ Ioc 0 (Nat.floor (10*C)), if c.Coprime zy.1 then
    (scaledDyadicCutoff N c : ℂ) * ∑' m : ℤ, frequency M c a zy.2 (zy.1 : ℤ) m else 0

private theorem ite_sum_zero {α : Type*} (p : Prop) (I : Finset α) (g : α → ℂ) :
    (if p then ∑ i ∈ I, g i else 0) = ∑ i ∈ I, if p then g i else 0 := by
  by_cases hp : p <;> simp only [hp, if_true, if_false, sum_const_zero]
/-- Exact finite source form of the TRUE completed smooth piece. -/
theorem completedPiece_eq_source (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N B C F : ℝ) :
    completedPiece A a T H lambda omega M N B C F =
      ∑ s ∈ carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F)),
        weight lambda omega s * completedKernel M N C a (output s) := by
  unfold completedPiece
  rw [sum_comm]
  simp only [carrier, rawCarrier, sum_filter, sum_product]
  apply sum_congr rfl
  intro f hf
  by_cases hfn : f ≠ 0
  · simp only [if_pos hfn, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro u hu
    rw [sum_comm]
    apply sum_congr rfl
    intro v hv
    by_cases hfu : fixedUnit A a u.1
    · by_cases hfv : fixedUnit A a v.1
      · have hgate : f ≠ 0 ∧ fixedUnit A a u.1 ∧ fixedUnit A a v.1 := ⟨hfn,hfu,hfv⟩
        simp only [if_pos hgate, completedKernel, mul_sum]
        apply sum_congr rfl
        intro c hc
        change
          (scaledDyadicCutoff N c : ℂ) *
              (if fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v) then
                (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
                  ∑' m : ℤ, frequency M c a (outputY f u v) (level u v : ℤ) m else 0) =
            (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
              (if c.Coprime (level u v) then
                (scaledDyadicCutoff N c : ℂ) *
                  ∑' m : ℤ, frequency M c a (outputY f u v) (level u v : ℤ) m else 0)
        by_cases hcz : c.Coprime (level u v)
        · have hpair : fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧
              c.Coprime (level u v) := ⟨hfu,hfv,hcz⟩
          rw [if_pos hpair, if_pos hcz]
          ring
        · have hpair : ¬(fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧
              c.Coprime (level u v)) := fun h => hcz h.2.2
          rw [if_neg hpair, if_neg hcz]
          simp only [mul_zero]
      · simp [hfn,hfu,hfv]
    · simp [hfn,hfu]
  · simp [hfn]
/-- Actual completed piece -> JOINT beta(z,y) on its literal image. -/
theorem completedPiece_eq_joint_beta (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N B C F : ℝ) :
    let U := carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))
    completedPiece A a T H lambda omega M N B C F =
      ∑ zy ∈ U.image output, beta U lambda omega zy * completedKernel M N C a zy := by
  dsimp only
  rw [completedPiece_eq_source]
  exact weighted_pushforward _ _ _ _

/-- Literal completed smooth piece split into y0, positive y and negative y,
with each ORIGINAL weighted joint beta kept on its own finite image. -/
theorem completedPiece_eq_three_joint_betas (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N B C F : ℝ) :
    let U := carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))
    let K := completedKernel M N C a
    completedPiece A a T H lambda omega M N B C F =
      (∑ zy ∈ (zeroSource U).image output, beta (zeroSource U) lambda omega zy*K zy) +
      (∑ zy ∈ (positiveSource U).image output, beta (positiveSource U) lambda omega zy*K zy) +
      (∑ zy ∈ (negativeSource U).image output, beta (negativeSource U) lambda omega zy*K zy) := by
  dsimp only
  rw [completedPiece_eq_source,sum_zero_nonzero,sum_positive_negative]
  simp only [weighted_pushforward]
  ring
private theorem carrier_data {A : ℕ} {a : ℤ} {T : Finset ℕ} {H : ℕ} {F : Finset ℤ}
    {s : Source} (hs : s ∈ carrier A a T H F) :
    s.1 ∈ F ∧ s.2.1 ∈ finiteInnerCarrier T H ∧ s.2.2 ∈ finiteInnerCarrier T H ∧
      s.1 ≠ 0 ∧ fixedUnit A a s.2.1.1 ∧ fixedUnit A a s.2.2.1 := by
  obtain ⟨hr,hg⟩ := mem_filter.mp hs
  exact ⟨(mem_product.mp hr).1,(mem_product.mp (mem_product.mp hr).2).1,
    (mem_product.mp (mem_product.mp hr).2).2,hg⟩

theorem output_residue_coprime {A : ℕ} {a : ℤ} {T : Finset ℕ} {H : ℕ} {F : Finset ℤ}
    {s : Source} (hs : s ∈ carrier A a T H F) : a.natAbs.Coprime (output s).1 := by
  have hd := carrier_data hs
  exact output_level_residue_coprime A a hd.2.2.2.2.1 hd.2.2.2.2.2

theorem output_positive_level {A : ℕ} {a : ℤ} {T : Finset ℕ} {H : ℕ} {F : Finset ℤ}
    (hT : ∀ t ∈ T, 0 < t) {s : Source} (hs : s ∈ carrier A a T H F) : 0 < (output s).1 := by
  have hd := carrier_data hs
  exact output_level_pos (hT _ (mem_product.mp hd.2.1).1) (hT _ (mem_product.mp hd.2.2.1).1)

private theorem frequency_abs_le {H : ℕ} {h : ℤ} (hh : h ∈ poissonNonzeroFrequencyWindow H) :
    |(h : ℝ)| ≤ (H : ℝ) := by
  have hwindow :
      (∃ n : ℕ, n ∈ Icc 1 H ∧ (n : ℤ) = h) ∨
        (∃ n : ℕ, n ∈ Icc 1 H ∧ -(n : ℤ) = h) := by
    simpa only [poissonNonzeroFrequencyWindow, mem_union, mem_image] using hh
  rcases hwindow with ⟨n,hn,rfl⟩ | ⟨n,hn,rfl⟩
  · simpa only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))] using
      (show (n : ℝ) ≤ H by exact_mod_cast (mem_Icc.mp hn).2)
  · simpa only [Int.cast_neg,Int.cast_natCast,abs_neg,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))] using
      (show (n : ℝ) ≤ H by exact_mod_cast (mem_Icc.mp hn).2)

private theorem factor_bounds {S : ℝ} (hS : 0 < S) {t : ℕ} (ht : t ∈ factorCarrier S) :
    0 < t ∧ S ≤ (t : ℝ) ∧ (t : ℝ) ≤ 2*S := by
  obtain ⟨hlo,hhi⟩ := mem_Icc.mp ht
  have hp : 0 < Nat.ceil S := Nat.ceil_pos.mpr hS
  exact ⟨by omega,(Nat.le_ceil S).trans (by exact_mod_cast hlo),
    (show (t : ℝ) ≤ (Nat.floor (2*S) : ℝ) by exact_mod_cast hhi).trans (Nat.floor_le (by positivity))⟩

/-- Closed ORIGINAL upper windows, not an assumed dyadic output support.
Dyadic y,z charting may be applied to this joint finite image afterwards. -/
theorem output_support {A : ℕ} {a : ℤ} {T : Finset ℕ} {H : ℕ} {Fset : Finset ℤ}
    {S F : ℝ} (hS : 0 < S) (hF : 0 ≤ F) (hT : T ⊆ factorCarrier S)
    (hFset : ∀ f ∈ Fset, |(f : ℝ)| ≤ F) {s : Source} (hs : s ∈ carrier A a T H Fset) :
    0 < (output s).1 ∧ S^2 ≤ ((output s).1 : ℝ) ∧ ((output s).1 : ℝ) ≤ 4*S^2 ∧
      |((output s).2 : ℝ)| ≤ 4*F*(H : ℝ)*S := by
  have hd := carrier_data hs
  have hu := factor_bounds hS (hT (mem_product.mp hd.2.1).1)
  have hv := factor_bounds hS (hT (mem_product.mp hd.2.2.1).1)
  have hhu := frequency_abs_le (mem_product.mp hd.2.1).2
  have hhv := frequency_abs_le (mem_product.mp hd.2.2.1).2
  have hz : ((output s).1 : ℝ) = (s.2.1.1 : ℝ)*s.2.2.1 := by simp only [output,level,Nat.cast_mul]
  have hlo := mul_le_mul hu.2.1 hv.2.1 hS.le (Nat.cast_nonneg s.2.1.1)
  have hhi := mul_le_mul hu.2.2 hv.2.2 (Nat.cast_nonneg s.2.2.1) (by positivity : 0 ≤ 2*S)
  have hk : |((difference s.2.1 s.2.2 : ℤ) : ℝ)| ≤ 4*(H : ℝ)*S := by
    have hdifference : ((difference s.2.1 s.2.2 : ℤ) : ℝ) =
        (s.2.1.2 : ℝ)*(s.2.2.1 : ℝ) - (s.2.2.2 : ℝ)*(s.2.1.1 : ℝ) := by
      simp only [difference, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    have htri := abs_add_le ((s.2.1.2 : ℝ)*(s.2.2.1 : ℝ)) (-((s.2.2.2 : ℝ)*(s.2.1.1 : ℝ)))
    have ha := mul_le_mul hhu hv.2.2 (Nat.cast_nonneg s.2.2.1) (Nat.cast_nonneg H)
    have hb := mul_le_mul hhv hu.2.2 (Nat.cast_nonneg s.2.1.1) (Nat.cast_nonneg H)
    have htri' : |((difference s.2.1 s.2.2 : ℤ) : ℝ)| ≤
        |(s.2.1.2 : ℝ)| * (s.2.2.1 : ℝ) + |(s.2.2.2 : ℝ)| * (s.2.1.1 : ℝ) := by
      rw [hdifference]
      simpa only [sub_eq_add_neg, abs_neg, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg s.2.1.1 : (0 : ℝ) ≤ (s.2.1.1 : ℝ)),
        abs_of_nonneg (Nat.cast_nonneg s.2.2.1 : (0 : ℝ) ≤ (s.2.2.1 : ℝ))] using htri
    nlinarith only [htri',ha,hb]
  refine ⟨Nat.mul_pos hu.1 hv.1,?_,?_,?_⟩
  · rw [hz]; simpa only [pow_two] using hlo
  · rw [hz]; nlinarith only [hhi]
  · change |((s.1*difference s.2.1 s.2.2 : ℤ) : ℝ)| ≤ _
    rw [Int.cast_mul,abs_mul]
    have hh := mul_le_mul (hFset _ hd.1) hk (abs_nonneg _) hF
    nlinarith only [hh]

/-- Actual closed signed f window used in completedPiece. -/
theorem actual_f_window_bound (F : ℝ) {f : ℤ}
    (hf : f ∈ Icc (Int.ceil (-F)) (Int.floor F)) : |(f : ℝ)| ≤ F := by
  obtain ⟨hlo,hhi⟩ := mem_Icc.mp hf
  exact abs_le.mpr ⟨(Int.le_ceil (-F)).trans (by exact_mod_cast hlo),
    (show (f : ℝ) ≤ (Int.floor F : ℝ) by exact_mod_cast hhi).trans (Int.floor_le F)⟩

/-- Actual quotient-image window supplied by the independentaf8f80 matcher.
This is a by-proof use of its true closed-endpoint identity, not a carrier hyp. -/
theorem actual_base_output_support (e : MediumAtom) (hS : 0 < e.Q2) (q : ℕ) (hq : 0 < q)
    {A : ℕ} {a : ℤ} {H : ℕ} {Fset : Finset ℤ} {F : ℝ} (hF : 0 ≤ F)
    (hFset : ∀ f ∈ Fset, |(f : ℝ)| ≤ F) {s : Source}
    (hs : s ∈ carrier A a (ActualSeparatedRowPacketMatchSourceOnly.baseCarrier e q) H Fset) :
    0 < (output s).1 ∧ (e.Q2/(q : ℝ))^2 ≤ ((output s).1 : ℝ) ∧
      ((output s).1 : ℝ) ≤ 4*(e.Q2/(q : ℝ))^2 ∧
        |((output s).2 : ℝ)| ≤ 4*F*(H : ℝ)*(e.Q2/(q : ℝ)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  exact output_support (div_pos hS hqR) hF
    (by
      intro t ht
      simpa only [ActualSeparatedRowPacketMatchSourceOnly.baseCarrier_eq_factorCarrier_div e hS.le hq] using ht) hFset hs

/-- Nonzero actual beta has the original residue/positive-level licence,
nonzero signed y and proved Y/Z upper windows, all on the SAME source. -/
theorem actual_beta_support (e : MediumAtom) (hS : 0 < e.Q2) (q : ℕ) (hq : 0 < q)
    {A : ℕ} {a : ℤ} {H : ℕ} {F : ℝ} (hF : 0 ≤ F)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {zy : Output}
    (hb : beta (nonzeroSource (carrier A a (ActualSeparatedRowPacketMatchSourceOnly.baseCarrier e q) H
      (Icc (Int.ceil (-F)) (Int.floor F)))) lambda omega zy ≠ 0) :
    0 < zy.1 ∧ a.natAbs.Coprime zy.1 ∧ zy.2 ≠ 0 ∧
      (e.Q2/(q : ℝ))^2 ≤ (zy.1 : ℝ) ∧ (zy.1 : ℝ) ≤ 4*(e.Q2/(q : ℝ))^2 ∧
        |(zy.2 : ℝ)| ≤ 4*F*(H : ℝ)*(e.Q2/(q : ℝ)) := by
  obtain ⟨s,hs,hout⟩ := mem_image.mp (beta_ne_zero_mem_image hb)
  have hsc := (mem_filter.mp hs).1
  have hd := actual_base_output_support e hS q hq hF (fun f hf => actual_f_window_bound F hf) hsc
  rw [← hout]
  exact ⟨hd.1,output_residue_coprime hsc,(mem_filter.mp hs).2,hd.2⟩
end
end ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
