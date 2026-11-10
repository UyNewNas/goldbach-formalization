import ImbalancedChen.Part3ActualOriginalProperPowerChartBridge
import ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT / ready=false.

Finite signed count-minus-exact-coprime-mean transport on one labelled
proper-power chart. The original integer HB atlas acts on the SAME source
word in both terms. The chart's eta, psi and licensed ambient W are retained.
The target t is independent of the word u; in particular u.prod=t is a
separate diagonal, not a zero-error convention. The signed rho is arbitrary.

This is an exact finite transform of the rough Lambda source, not an
identification of that source with primes plus proper powers, nor an
asymptotic signed estimate. The actual W_N licence, Lambda/log arithmetic,
signed modulus budget and full22 actual active cap remain open.
-/

namespace ImbalancedChen.P5Z.ProperPowerSignedMeanHBTransport

noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.P5Z.LicensedOriginalIntegerProfile
open ImbalancedChen.P5Z.PerGroupIntegerHBAtlasPushforward
open ImbalancedChen.Part3.OriginalProperPowerActualChart

def signedKernel (q t b : ℕ) : ℂ :=
  (if Nat.ModEq q b t then (1 : ℂ) else 0) -
    (if Nat.Coprime b q then (1 : ℂ) else 0) / (Nat.totient q : ℂ)

def signedRow (Q : Finset ℕ) (rho : ℕ → ℂ) (t b : ℕ) : ℂ :=
  ∑ q ∈ Q, rho q * signedKernel q t b

def markedWords {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ)
    (T kappa0 : ℝ) (cap : ℕ) (js : List ℕ) (bad : Fin k) :
    Finset (List ℕ) :=
  badChartWords chi eta (fun us => ((listExtension L us : ℝ) : ℂ))
    T kappa0 cap k js bad

-- The q-first sum is the exact signed residual of the integer HB source.
-- Its mean uses phi(q) and coprimality of the SAME complete word product.
def signedSource {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ) (z T kappa0 : ℝ)
    (cap : ℕ) (js : List ℕ) (bad : Fin k)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (t : ℕ) : ℂ :=
  ∑ q ∈ Q, rho q *
    ∑ us ∈ markedWords L chi eta T kappa0 cap js bad,
      sourceTuple chi z js us *
        ((listExtension L us : ℂ) *
          (eta ((us.prod : ℝ) / T ^ (1-kappa0)) : ℂ) *
            signedKernel q t us.prod)

-- HB is applied occurrencewise on the original marked integer words;
-- F sees the product after all per-group rows are pushed forward.
def signedAtlas {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ) (z T kappa0 : ℝ)
    (cap : ℕ) (js : List ℕ) (bad : Fin k)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (t : ℕ) : ℂ :=
  ∑ us ∈ markedWords L chi eta T kappa0 cap js bad,
    atlasEval chi z js us (fun rows =>
      (listExtension L (originalProducts rows) : ℂ) *
        (eta (((originalProducts rows).prod : ℝ) /
          T ^ (1-kappa0)) : ℂ) *
          signedRow Q rho t (originalProducts rows).prod)

theorem signed_source_eq_tuple_first {k : ℕ}
    {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ) (z T kappa0 : ℝ)
    (cap : ℕ) (js : List ℕ) (bad : Fin k)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (t : ℕ) :
    signedSource L chi eta z T kappa0 cap js bad Q rho t =
      ∑ us ∈ markedWords L chi eta T kappa0 cap js bad,
        sourceTuple chi z js us *
          ((listExtension L us : ℂ) *
            (eta ((us.prod : ℝ) / T ^ (1-kappa0)) : ℂ) *
              signedRow Q rho t us.prod) := by
  unfold signedSource
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro us hus
  unfold signedRow
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- Exact HB transform of the signed residue count and its coprime mean
in one step. The two terms therefore cannot acquire different chart
cutoffs, target variables or rho families during the pushforward. -/
theorem signed_source_eq_HB_atlas {k : ℕ}
    {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ)
    (hone : ∀ x : ℝ, x ≤ 1 → chi x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → chi x = 0)
    {z : ℝ} (hz : 0 ≤ z) (T kappa0 : ℝ)
    (cap : ℕ) (js : List ℕ) (bad : Fin k)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (t : ℕ) :
    signedSource L chi eta z T kappa0 cap js bad Q rho t =
      signedAtlas L chi eta z T kappa0 cap js bad Q rho t := by
  rw [signed_source_eq_tuple_first]
  unfold signedAtlas
  apply Finset.sum_congr rfl
  intro us hus
  exact (licensed_profile_atlas_identity L chi eta hone hzero hz
    T kappa0 js us (fun vs => signedRow Q rho t vs.prod)).symm

/-- On the complete-product collision, every q counts the residue but
the exact coprime mean remains. In particular q=1 cancels exactly. -/
theorem signedKernel_diagonal (q t : ℕ) :
    signedKernel q t t =
      1 - (if Nat.Coprime t q then (1 : ℂ) else 0) /
        (Nat.totient q : ℂ) := by
  simp [signedKernel]

theorem signedKernel_diagonal_one (t : ℕ) :
    signedKernel 1 t t = 0 := by
  simp [signedKernel]

theorem signedRow_diagonal (Q : Finset ℕ) (rho : ℕ → ℂ) (t : ℕ) :
    signedRow Q rho t t =
      ∑ q ∈ Q, rho q *
        (1 - (if Nat.Coprime t q then (1 : ℂ) else 0) /
          (Nat.totient q : ℂ)) := by
  unfold signedRow
  apply Finset.sum_congr rfl
  intro q hq
  rw [signedKernel_diagonal]

end
end ImbalancedChen.P5Z.ProperPowerSignedMeanHBTransport
