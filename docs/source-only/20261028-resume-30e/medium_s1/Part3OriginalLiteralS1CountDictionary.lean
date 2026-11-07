import ImbalancedChen.Part3MediumActualPsiPreliminaryDispersion
import ImbalancedChen.Part3OriginalOwnedS1BlockBudget
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Start from the independently defined principalRow and samePsiS1 of the
actual preliminary Cauchy source. Sum its shared m variable exactly.
The resulting coefficient is the actual paperCommonMCount; no equality
to a newly defined candidate is used as a premise.
-/

namespace ImbalancedChen.Part3.OriginalLiteralS1CountDictionary
noncomputable section
open Classical Finset
open scoped BigOperators
open MediumActualPsiPreliminaryDispersion20261028
open MediumActualPreliminaryCauchy20261028 MediumGlobalDyadicOwnership20261028
open OriginalPaperPsiCoprimeCount OriginalSamePsiS1Remainder
open OriginalMediumS1CommonMCount OriginalMediumPhysicalE3Block
open OriginalGevreyPoissonPacket20261028

def nativeMean (atom : MediumAtom) (q d r m : ℕ) : ℂ :=
  if m.Coprime ((q * d) * r) then
    alphaCoprime atom (q * d) r / (Nat.totient ((q * d) * r) : ℂ) else 0

theorem principalRow_eq_nativeMeans (atom : MediumAtom) (z y : ℝ) (k : Key)
    (q d m : ℕ) :
    principalRow atom z y k q d m =
      ∑ r ∈ dyadicWindow k.w, lambdaTrim atom z y k d r * nativeMean atom q d r m := by
  unfold principalRow innerCarrier
  rw [sum_product]
  apply sum_congr rfl
  intro r hr
  rw [show nativeMean atom q d r m =
      ∑ n ∈ atom.alphaCarrier, atom.alpha n * literalMeanKernel atom q d r n m from
    (sum_literalMean_eq_alphaCoprime atom q d r m).symm]
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  ring

/-- The two mean gates share the same m. Their conjunction is exactly
coprimality to ell*r*s, rather than two independently chosen m values. -/
theorem common_mean_gates (m ell r s : ℕ) :
    (m.Coprime (ell * r) ∧ m.Coprime (ell * s)) ↔ m.Coprime (ell * r * s) := by
  simp only [Nat.coprime_mul_iff_right]
  tauto

theorem sum_shared_m_nativeMeans (atom : MediumAtom) (S : Finset ℕ)
    (M : ℝ) (q d r s : ℕ) :
    (∑ m ∈ S, (paperWeight M m : ℂ) *
      nativeMean atom q d r m * star (nativeMean atom q d s m)) =
    ((paperCommonMCount S M (q * d) r s /
      (((q * d * r).totient : ℝ) * ((q * d * s).totient : ℝ))) : ℝ) *
      alphaCoprime atom (q * d) r * star (alphaCoprime atom (q * d) s) := by
  unfold paperCommonMCount
  push_cast
  simp only [sum_div, sum_mul]
  apply sum_congr rfl
  intro m hm
  by_cases hr : m.Coprime ((q * d) * r)
  · by_cases hs : m.Coprime ((q * d) * s)
    · have hrs := (common_mean_gates m (q * d) r s).mp ⟨hr, hs⟩
      simp only [nativeMean, if_pos hr, if_pos hs, if_pos hrs]
      simp only [star_div₀, star_natCast, div_eq_mul_inv, mul_inv_rev]
      ring
    · have hrs : ¬m.Coprime (q * d * r * s) :=
        fun h => hs ((common_mean_gates m (q * d) r s).mpr h).2
      simp [nativeMean, hr, hs, hrs]
  · have hrs : ¬m.Coprime (q * d * r * s) :=
      fun h => hr ((common_mean_gates m (q * d) r s).mpr h).1
    simp [nativeMean, hr, hrs]

/-- Actual coefficients of the literal original source after its shared
m has been summed. This is a derived arithmetic dictionary, not an atlas
definition or an assumed original-term identification. -/
def nativePurePair (atom : MediumAtom) (z y : ℝ) (k : Key) (q d r s : ℕ) : ℂ :=
  lambdaTrim atom z y k d r * star (lambdaTrim atom z y k d s) *
    ((paperCommonMCount (paperPsiNaturalCarrier atom.V) atom.V (q * d) r s /
      (((q * d * r).totient : ℝ) * ((q * d * s).totient : ℝ))) : ℝ) *
    alphaCoprime atom (q * d) r * star (alphaCoprime atom (q * d) s)

theorem sum_shared_m_principal_square (atom : MediumAtom) (z y : ℝ) (k : Key)
    (q d : ℕ) :
    (∑ m ∈ paperPsiNaturalCarrier atom.V, (paperWeight atom.V m : ℂ) *
      principalRow atom z y k q d m * star (principalRow atom z y k q d m)) =
    ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
      nativePurePair atom z y k q d r s := by
  simp_rw [principalRow_eq_nativeMeans, star_sum]
  simp only [sum_mul_sum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  rw [sum_comm]
  apply sum_congr rfl
  intro s hs
  calc
    _ = (lambdaTrim atom z y k d r * star (lambdaTrim atom z y k d s)) *
        ∑ m ∈ paperPsiNaturalCarrier atom.V,
          (paperWeight atom.V m : ℂ) * nativeMean atom q d r m *
            star (nativeMean atom q d s m) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      simp only [star_mul]
      ring
    _ = _ := by
      rw [sum_shared_m_nativeMeans]
      unfold nativePurePair
      ring

private theorem complex_cast_norm_square (v : ℂ) : ((‖v‖ : ℂ) ^ 2) = v * star v :=
  (Complex.mul_conj' v).symm

/-- Full original same-profile S1, with its independently defined q,d,m
carrier, is converted to the literal shared-m count coefficient. -/
theorem samePsiS1_cast_eq_native_pure_pairs (atom : MediumAtom) (z y : ℝ) (k : Key) :
    (samePsiS1 atom z y k : ℂ) =
      ∑ q ∈ paperPsiNaturalCarrier atom.Q1, ∑ d ∈ dyadicWindow k.d,
        (paperQWeight atom q : ℂ) *
          ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
            nativePurePair atom z y k q d r s := by
  calc
    _ = ∑ q ∈ paperPsiNaturalCarrier atom.Q1, ∑ d ∈ dyadicWindow k.d,
        (paperQWeight atom q : ℂ) *
          ∑ m ∈ paperPsiNaturalCarrier atom.V, (paperWeight atom.V m : ℂ) *
            principalRow atom z y k q d m * star (principalRow atom z y k q d m) := by
      unfold samePsiS1 smoothOuterCarrier jointPsi
      simp only [sum_product, Complex.ofReal_sum, Complex.ofReal_mul,
        Complex.ofReal_pow, mul_sum]
      apply sum_congr rfl
      intro q hq
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro m hm
      rw [complex_cast_norm_square]
      change (paperQWeight atom q : ℂ) * (paperWeight atom.V m : ℂ) *
          (principalRow atom z y k q d m * star (principalRow atom z y k q d m)) = _
      ring
    _ = _ := by simp_rw [sum_shared_m_principal_square]

end
end ImbalancedChen.Part3.OriginalLiteralS1CountDictionary
