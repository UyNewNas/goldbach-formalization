import ImbalancedChen.P5ZU11MeasurableEnvelope
import ImbalancedChen.ActualPrimeBoxTestFunctions

/-!
Common approximation errors for the original finite-minimum construction.
A single error is paid after taking the minimum: there is no factor equal
to the number of ordinary alternatives. The actual prime sum may then be
restricted by ANY tuple mask, including an N-dependent last-pair gainmask
or a priority mask. No convergence for such a moving masked sum is claimed.

The uniform eventual constant comes from the actual four-prime Mertens
box mass. Pointwise candidate errors are local approximation data, not a
whole mean, Rosser estimate, distribution bound, or convergence supplier.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011AdaptivePrimeError

open Set Filter Topology
open Classical
open U11Integral
open scoped BigOperators

noncomputable section

/-- The least winner supplies a candidate, so a common one-sided error
passes through a finite minimum without adding the alternatives. -/
theorem envelope_le_add (bank : Finset ℕ) (f g : ℕ → LogFour → ℝ)
    (v : LogFour) (delta : ℝ)
    (hfg : ∀ c ∈ tags bank, f c v ≤ g c v + delta) :
    envelope bank f v ≤ envelope bank g v + delta := by
  obtain ⟨c, hc, hv⟩ := exists_winner (Set.univ : Set LogFour) bank g v (Set.mem_univ v)
  calc
    envelope bank f v ≤ f c v := envelope_le bank f v c hc
    _ ≤ g c v + delta := hfg c hc
    _ = envelope bank g v + delta := by rw [hv.2.1]

/-- Candidatewise uniform errors remain a single error at the envelope. -/
theorem envelope_abs_sub_le (bank : Finset ℕ) (f g : ℕ → LogFour → ℝ)
    (v : LogFour) (delta : ℝ)
    (hfg : ∀ c ∈ tags bank, |f c v - g c v| ≤ delta) :
    |envelope bank f v - envelope bank g v| ≤ delta := by
  have hf := envelope_le_add bank f g v delta (fun c hc => by
    have h := (abs_le.mp (hfg c hc)).2
    linarith)
  have hg := envelope_le_add bank g f v delta (fun c hc => by
    have h := (abs_le.mp (hfg c hc)).1
    linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Eligibility may vary at every point. Only eligible ordinary options
need an approximation bound; ineligible options read the same switched
fallback. No geometric cell is assumed to have a constant gainmask. -/
theorem guarded_envelope_abs_sub_le (bank : Finset ℕ)
    (eligible : ℕ → LogFour → Prop) (switchedA switchedB : LogFour → ℝ)
    (ordinaryA ordinaryB : ℕ → LogFour → ℝ) (v : LogFour) (delta : ℝ)
    (hs : |switchedA v - switchedB v| ≤ delta)
    (ho : ∀ j ∈ bank, eligible j v → |ordinaryA j v - ordinaryB j v| ≤ delta) :
    |envelope bank (guarded eligible switchedA ordinaryA) v -
      envelope bank (guarded eligible switchedB ordinaryB) v| ≤ delta := by
  apply envelope_abs_sub_le
  intro c hc
  rcases Finset.mem_insert.mp hc with rfl | hc
  · simpa only [guarded, if_pos rfl] using hs
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    by_cases helig : eligible j v
    · simpa [guarded, helig] using ho j hj helig
    · simpa [guarded, helig] using hs

/-- The mask is evaluated on the actual four labelled primes, not just
on their logarithmic image or on a chosen mesh representative. -/
def maskedTestSum (N : ℕ) (a b : Fin 4 → ℝ)
    (keep : (Fin 4 → ℕ) → Prop) (f : LogFour → ℝ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N a b,
    if keep p then (∏ i, 1 / ((p i : ℝ) - 1)) * f (actualPrimeTupleLog N p) else 0

/-- Uniformity over every mask follows from positive actual weights. -/
theorem maskedTestSum_error (N : ℕ) (a b : Fin 4 → ℝ)
    (keep : (Fin 4 → ℕ) → Prop) (f g : LogFour → ℝ)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hfg : ∀ p ∈ actualPrimeBoxTuples N a b,
      |f (actualPrimeTupleLog N p) - g (actualPrimeTupleLog N p)| ≤ delta) :
    |maskedTestSum N a b keep f - maskedTestSum N a b keep g| ≤
      delta * actualPrimeBoxMass N a b := by
  unfold maskedTestSum actualPrimeBoxMass
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ actualPrimeBoxTuples N a b,
        |(if keep p then (∏ i, 1 / ((p i : ℝ) - 1)) *
            f (actualPrimeTupleLog N p) else 0) -
          (if keep p then (∏ i, 1 / ((p i : ℝ) - 1)) *
            g (actualPrimeTupleLog N p) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      have hw := actualPrimeBoxWeight_nonneg hp
      by_cases hk : keep p
      · simp only [if_pos hk, ← mul_sub, abs_mul, abs_of_nonneg hw]
        exact (mul_le_mul_of_nonneg_left (hfg p hp) hw).trans_eq (mul_comm _ _)
      · simp only [if_neg hk, sub_self, abs_zero]
        exact mul_nonneg hdelta hw

/-- The SAME bank and eligibility guard are used on both sides. Thus
this statement applies after common refinement, with all original tests
retained in the candidate functions, and with arbitrary adaptive masks. -/
theorem masked_minimum_error (N : ℕ) (a b : Fin 4 → ℝ)
    (keep : (Fin 4 → ℕ) → Prop) (bank : Finset ℕ)
    (f g : ℕ → LogFour → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hfg : ∀ p ∈ actualPrimeBoxTuples N a b, ∀ c ∈ tags bank,
      |f c (actualPrimeTupleLog N p) - g c (actualPrimeTupleLog N p)| ≤ delta) :
    |maskedTestSum N a b keep (envelope bank f) -
      maskedTestSum N a b keep (envelope bank g)| ≤
      delta * actualPrimeBoxMass N a b := by
  exact maskedTestSum_error N a b keep _ _ delta hdelta
    (fun p hp => envelope_abs_sub_le bank f g _ delta (hfg p hp))

/-- A constant for the genuine original four-prime logarithmic cube. -/
def originalCubeMassBound : ℝ :=
  1 + |∏ _i : Fin 4, Real.log ((59 / 250 : ℝ) / (417 / 5000 : ℝ))|

/-- This eventual threshold is chosen before any mask or candidates. -/
theorem eventually_originalCube_mass_bounded :
    ∀ᶠ N : ℕ in atTop,
      actualPrimeBoxMass N (fun _ : Fin 4 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ)) ≤ originalCubeMassBound := by
  have ht := tendsto_actualPrimeBoxMass
    (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
    (fun _ => by norm_num) (fun _ => by norm_num)
  have hgap : (∏ _i : Fin 4, Real.log ((59 / 250 : ℝ) / (417 / 5000 : ℝ))) <
      originalCubeMassBound := by
    unfold originalCubeMassBound
    linarith [le_abs_self (∏ _i : Fin 4,
      Real.log ((59 / 250 : ℝ) / (417 / 5000 : ℝ)))]
  exact (ht.eventually (gt_mem_nhds hgap)).mono (fun _ h => h.le)

/-- One common approximation budget covers every moving gainmask and
every finite bank. The only candidate hypothesis is its literal local
pointwise approximation error; no masked mean is supplied as a premise. -/
theorem eventually_uniform_masked_minimum_error (delta : ℝ) (hdelta : 0 ≤ delta) :
    ∀ᶠ N : ℕ in atTop, ∀ (keep : (Fin 4 → ℕ) → Prop) (bank : Finset ℕ)
      (f g : ℕ → LogFour → ℝ),
      (∀ p ∈ actualPrimeBoxTuples N
        (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ)),
        ∀ c ∈ tags bank,
          |f c (actualPrimeTupleLog N p) - g c (actualPrimeTupleLog N p)| ≤ delta) →
      |maskedTestSum N (fun _ : Fin 4 => (417 / 5000 : ℝ))
          (fun _ => (59 / 250 : ℝ)) keep (envelope bank f) -
        maskedTestSum N (fun _ : Fin 4 => (417 / 5000 : ℝ))
          (fun _ => (59 / 250 : ℝ)) keep (envelope bank g)| ≤
        delta * originalCubeMassBound := by
  filter_upwards [eventually_originalCube_mass_bounded] with N hN
  intro keep bank f g hfg
  exact (masked_minimum_error N _ _ keep bank f g delta hdelta hfg).trans
    (mul_le_mul_of_nonneg_left hN hdelta)

end

end ImbalancedChen.P5Z.U1011AdaptivePrimeError
