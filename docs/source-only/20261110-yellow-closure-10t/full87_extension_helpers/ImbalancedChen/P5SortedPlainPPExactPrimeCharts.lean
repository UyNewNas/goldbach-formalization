import ImbalancedChen.P5TypedLabelledPlainPrimeProductTensor
import ImbalancedChen.P5ActualLabelledPrimeSmoothCharts

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Exact carrier/coefficient PREFIX of the requested bridge. This reaches
-- the retained ORIGINAL PRIME psi/eta charts, not the unrestricted HB
-- integer branch tensor. The latter still needs the recorded constructor.
-- Original AP TEST u and W(u) stay independent of physical rho(q)/mark t.
namespace ImbalancedChen.P5Z.SortedPlainPPExactPrimeCharts
noncomputable section
open Classical
open scoped BigOperators
open ActualSortedWeightPrimeGroupTensor TypedLabelledPlainPrimeProductTensor
open ExactOriginalSmoothDyadicPartition ActualLabelledPrimeSmoothCharts

private theorem member_le_list_sum {p : ℕ} : ∀ ps : List ℕ, p ∈ ps → p ≤ ps.sum := by
  intro ps
  induction ps with
  | nil => intro hp; simp at hp
  | cons a ps ih =>
    intro hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp only [List.sum_cons]
      omega
    · have h := ih hp
      simp only [List.sum_cons]
      omega

-- The bank cap is fixed by the native sorted carrier before inspecting
-- a tuple, a discrepancy sign, a chart or any HB decomposition.
def carrierCap (S : Finset (List ℕ)) : ℕ := ∑ ps ∈ S, ps.sum

theorem carrierCap_bound (S : Finset (List ℕ)) {ps : List ℕ} (hps : ps ∈ S)
    {p : ℕ} (hp : p ∈ ps) : p ≤ carrierCap S := by
  have hsum : ps.sum ≤ ∑ qs ∈ S, qs.sum :=
    Finset.single_le_sum (fun qs hqs => Nat.zero_le qs.sum) hps
  exact (member_le_list_sum ps hp).trans hsum

theorem finite_prime_carrier_charts (chi eta : ℝ → ℝ) (W F : List ℕ → ℂ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (S : Finset (List ℕ)) (k : ℕ) (T kappa0 : ℝ)
    (hS : ∀ ps ∈ S, ps.length = k ∧ ∀ p ∈ ps, p.Prime) :
    (∑ ps ∈ S, trimmedWeight eta W T kappa0 ps*F ps) =
      ∑ js ∈ chartBank (carrierCap S) k, ∑ ps ∈ S,
        chartTerm chi eta W T kappa0 js ps*F ps := by
  calc
    _ = ∑ ps ∈ S, ∑ js ∈ chartBank (carrierCap S) k,
        chartTerm chi eta W T kappa0 js ps*F ps := by
      apply Finset.sum_congr rfl
      intro ps hps
      have hp := hS ps hps
      have hcarrier : ps ∈ primeTuples (carrierCap S) k :=
        primeTuples_mem (carrierCap S) k ps hp.1
          (fun p hpm => ⟨hp.2 p hpm,carrierCap_bound S hps hpm⟩)
      exact prime_tuple_expansion chi eta W F hone hzero (carrierCap S) k T kappa0 hcarrier
    _ = _ := Finset.sum_comm

theorem sortedWord_prime_data (N : ℕ) (tau : ℝ) (input : List ℕ)
    {ps : List ℕ} (hps : ps ∈ sortedWord N tau input) :
    ps.length = input.length ∧ ∀ p ∈ ps, p.Prime := by
  obtain ⟨hbox,hsorted⟩ := Finset.mem_filter.mp hps
  exact ⟨actualPrimeSlotBox_length (actualPrimeFineLabelFinset N tau) input ps hbox,
    actualPrimeSlotBox_prime (actualPrimeFineLabelFinset N tau) input
      (fun _ _ p hp => (mem_actualPrimeFineLabelFinset.mp hp).1) ps hbox⟩

def realTrim (eta : ℝ → ℝ) (W : List ℕ → ℝ) (T kappa0 : ℝ) (ps : List ℕ) : ℝ :=
  eta ((ps.prod : ℝ)/T^(1-kappa0))*W ps

def realDiscard (eta : ℝ → ℝ) (W : List ℕ → ℝ) (T kappa0 : ℝ) (ps : List ℕ) : ℝ :=
  (1-eta ((ps.prod : ℝ)/T^(1-kappa0)))*W ps

-- Exact smooth trim decomposition; bounding the discarded part is a
-- separate transfer task. The full M_J scalar and rank sign are inherited
-- from sortedPlainPP_eq_group without changing its native coefficient.
theorem plainGroupPP_exact_trim_split
    {N : ℕ} (hN : 1 ≤ N) {tau : ℝ} (htau : 0 ≤ tau)
    (T : ℕ) (D A : ℝ) (yz : Bool) (p : Fin 3 → ℕ) (tail : List ℕ)
    (horder : (p 0::p 1::p 2::tail).Pairwise (· ≥ ·))
    (eta : ℝ → ℝ) (W : List ℕ → ℝ) (kappa0 c : ℝ) (q : ℕ) :
    plainGroupPP T N tau D A yz p tail W c q =
      plainGroupPP T N tau D A yz p tail (realTrim eta W T kappa0) c q +
        plainGroupPP T N tau D A yz p tail (realDiscard eta W T kappa0) c q := by
  let input := p 0::p 1::p 2::tail
  calc
    _ = c*∑ u ∈ sortedWord N tau input, W u*primeProductAPDifference T q u.prod :=
      (sortedPlainPP_eq_group hN htau T D A yz p tail horder W c q).symm
    _ = c*∑ u ∈ sortedWord N tau input,
        (realTrim eta W T kappa0 u*primeProductAPDifference T q u.prod +
          realDiscard eta W T kappa0 u*primeProductAPDifference T q u.prod) := by
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      unfold realTrim realDiscard
      ring
    _ = c*(∑ u ∈ sortedWord N tau input,
          realTrim eta W T kappa0 u*primeProductAPDifference T q u.prod) +
        c*(∑ u ∈ sortedWord N tau input,
          realDiscard eta W T kappa0 u*primeProductAPDifference T q u.prod) := by
      rw [Finset.sum_add_distrib,mul_add]
    _ = _ := by
      rw [sortedPlainPP_eq_group hN htau T D A yz p tail horder
        (realTrim eta W T kappa0) c q,
        sortedPlainPP_eq_group hN htau T D A yz p tail horder
        (realDiscard eta W T kappa0) c q]

-- Exact native sorted-word -> retained ORIGINAL PRIME chart equality.
-- W is coordinate dependent; no product-only assumption is introduced.
-- No prime carrier is identified with the unrestricted HB integer source.
theorem trimmed_plainGroupPP_eq_prime_charts
    {N : ℕ} (hN : 1 ≤ N) {tau : ℝ} (htau : 0 ≤ tau)
    (T : ℕ) (D A : ℝ) (yz : Bool) (p : Fin 3 → ℕ) (tail : List ℕ)
    (horder : (p 0::p 1::p 2::tail).Pairwise (· ≥ ·))
    (chi eta : ℝ → ℝ) (W : List ℕ → ℝ) (kappa0 c : ℝ) (q : ℕ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0) :
    let input := p 0::p 1::p 2::tail
    let S := sortedWord N tau input
    ((plainGroupPP T N tau D A yz p tail (realTrim eta W T kappa0) c q : ℝ) : ℂ) =
      ∑ js ∈ chartBank (carrierCap S) input.length, ∑ u ∈ S,
        (c : ℂ)*chartTerm chi eta (fun u => (W u : ℂ)) T kappa0 js u *
          (primeProductAPDifference T q u.prod : ℂ) := by
  dsimp only
  let input := p 0::p 1::p 2::tail
  let S := sortedWord N tau input
  let F : List ℕ → ℂ := fun u => (primeProductAPDifference T q u.prod : ℂ)
  have hreal := sortedPlainPP_eq_group hN htau T D A yz p tail horder
    (realTrim eta W T kappa0) c q
  have hcast := congrArg (fun a : ℝ => (a : ℂ)) hreal
  have hstart : ((plainGroupPP T N tau D A yz p tail (realTrim eta W T kappa0) c q : ℝ) : ℂ) =
      (c : ℂ)*(∑ u ∈ S, trimmedWeight eta (fun u => (W u : ℂ)) T kappa0 u*F u) := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_sum,realTrim,trimmedWeight] using hcast.symm
  have hcharts := finite_prime_carrier_charts chi eta (fun u => (W u : ℂ)) F hone hzero
    S input.length T kappa0 (fun u hu => sortedWord_prime_data N tau input hu)
  rw [hstart,hcharts,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro js hjs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  ring

end
end ImbalancedChen.P5Z.SortedPlainPPExactPrimeCharts
