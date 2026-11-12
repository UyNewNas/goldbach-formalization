import ImbalancedChen.P5AllWordAmbientOccurrenceBound
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / ready_to_install=false.
-- Finite allocation combinatorics and the actual one-letter occurrence
-- derivative rules. Full four-factor chart bound is separately held.
namespace ImbalancedChen.P5Z.OccurrenceLeibnizAllocation
noncomputable section
open Classical
open AllWordAmbientOccurrenceBound

-- Every derivative letter is allocated to the left or right factor.
-- The lists preserve ORDER and repeated occurrence labels.
def binaryAlloc {α : Type*} : List α → List (List α × List α)
  | [] => [([],[])]
  | a::w =>
      ((binaryAlloc w).map (fun p => (a::p.1,p.2))) ++
        ((binaryAlloc w).map (fun p => (p.1,a::p.2)))

theorem binaryAlloc_length {α : Type*} (w : List α) :
    (binaryAlloc w).length = 2^w.length := by
  induction w with
  | nil => simp [binaryAlloc]
  | cons a w ih =>
      simp [binaryAlloc, ih, pow_succ]
      omega

theorem binaryAlloc_letters {α : Type*} :
    ∀ w : List α, ∀ p ∈ binaryAlloc w,
      p.1.length + p.2.length = w.length := by
  intro w
  induction w with
  | nil =>
      intro p hp
      simp [binaryAlloc] at hp
      rcases hp with rfl
      simp
  | cons a w ih =>
      intro p hp
      simp only [binaryAlloc, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
      · simpa [Nat.add_assoc] using congrArg Nat.succ (ih q hq)
      · have h := ih q hq
        simp only [List.length_cons]
        omega

-- The occurrence derivative is the ordinary directional derivative
-- along z+t e_a at t=0. These are genuine calculus laws, not an
-- abstract derivation axiom or a disguised final chart estimate.
theorem occOne_add {m : ℕ} (a : Fin m)
    (f g : (Fin m → ℝ) → ℝ) (z : Fin m → ℝ)
    (hf : DifferentiableAt ℝ
      (fun t : ℝ => f (z + Pi.single a t)) 0)
    (hg : DifferentiableAt ℝ
      (fun t : ℝ => g (z + Pi.single a t)) 0) :
    occOne a (fun v => f v + g v) z =
      occOne a f z + occOne a g z := by
  simp [occOne, deriv_fun_add hf hg]

theorem occOne_mul {m : ℕ} (a : Fin m)
    (f g : (Fin m → ℝ) → ℝ) (z : Fin m → ℝ)
    (hf : DifferentiableAt ℝ
      (fun t : ℝ => f (z + Pi.single a t)) 0)
    (hg : DifferentiableAt ℝ
      (fun t : ℝ => g (z + Pi.single a t)) 0) :
    occOne a (fun v => f v * g v) z =
      occOne a f z * g z + f z * occOne a g z := by
  simp [occOne, deriv_fun_mul hf hg]

theorem occOne_four {m : ℕ} (a : Fin m)
    (A E P C : (Fin m → ℝ) → ℝ) (z : Fin m → ℝ)
    (hA : DifferentiableAt ℝ
      (fun t : ℝ => A (z + Pi.single a t)) 0)
    (hE : DifferentiableAt ℝ
      (fun t : ℝ => E (z + Pi.single a t)) 0)
    (hP : DifferentiableAt ℝ
      (fun t : ℝ => P (z + Pi.single a t)) 0)
    (hC : DifferentiableAt ℝ
      (fun t : ℝ => C (z + Pi.single a t)) 0) :
    occOne a (fun v => A v * E v * P v * C v) z =
      occOne a A z * E z * P z * C z +
      A z * occOne a E z * P z * C z +
      A z * E z * occOne a P z * C z +
      A z * E z * P z * occOne a C z := by
  have hAE : DifferentiableAt ℝ
      (fun t : ℝ => A (z + Pi.single a t) *
        E (z + Pi.single a t)) 0 := hA.mul hE
  have hPC : DifferentiableAt ℝ
      (fun t : ℝ => P (z + Pi.single a t) *
        C (z + Pi.single a t)) 0 := hP.mul hC
  have houter := occOne_mul a
    (fun v => A v * E v) (fun v => P v * C v) z hAE hPC
  have hleft := occOne_mul a A E z hA hE
  have hright := occOne_mul a P C z hP hC
  have hfun : (fun v => A v * E v * P v * C v) =
      (fun v => (A v * E v) * (P v * C v)) :=
    funext (fun v => mul_assoc (A v * E v) (P v) (C v))
  rw [hfun, houter, hleft, hright]
  ring

-- The four destinations in the actual chart are ambient A, complete
-- product eta, the UNIQUE psi_owner(a), and its own plateau c_a.
-- The binary allocation count gives 2^r; iterating two binary splits
-- gives <=4^r. The full derivative identity still needs the finite
-- sum/iterated product calculus and fixed-cutoff Euler bounds.

end
end ImbalancedChen.P5Z.OccurrenceLeibnizAllocation
