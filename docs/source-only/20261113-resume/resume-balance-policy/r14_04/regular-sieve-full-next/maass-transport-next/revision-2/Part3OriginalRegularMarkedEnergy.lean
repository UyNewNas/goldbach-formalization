import ImbalancedChen.Part3OriginalRegularPhysicalTransport
import ImbalancedChen.Part3OriginalHolomorphicInfinityPacket

/-! Exact compact spatial energies of the original signed coefficient
row at either observation, including the real-length zero extension. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularMarkedEnergy20261113
open Real Set Filter MeasureTheory Finset
open scoped MatrixGroups Topology Classical
open OriginalRegularPhysicalTransport20261113 (phase phase_norm negative_norm fricke_norm)
open OriginalRegularPacketTest20261113 (mark mark_ne Dyadic energy)
open OriginalRegularCompactCoordinates20261113 (spatial positive_vector block row index nonzero)
open OriginalRegularCompactGram20261113 (vector)
open OriginalRegularCutoffPlane20261113 (compact)
open OriginalRegularPreKuznetsovGaussian20261113 (weight)
open OriginalHolomorphicInfinityPacket20261113 (start extension extension_energy)
open OriginalRegularCompactEnergy20261113 (limitEnergy)
open OriginalContinuousPoincarePackets20261110 (packet packet_L2 scaledSeed)
open ActualContinuousPoincarePairing20261110 (originalPoincare)
open ActualInfinityCuspAnnihilator20261026b (HeightSeed)
open Gamma0QuotientCellPushforward20261025a
open private extend_sum from ImbalancedChen.Part3OriginalHolomorphicInfinityPacket

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

def twist (q : ℕ+) (one neg : Bool) (a : ℕ→ℂ) (n : ℕ) : ℂ :=
  if one then phase q (mark neg n)*a n else a n

def transported (q : ℕ+) (one neg : Bool) (a : ℕ→ℂ) (n : ℕ) : ℂ :=
  if neg then star (twist q one neg a n) else twist q one neg a n

theorem transported_energy (q : ℕ+) (one neg : Bool) (S : Finset ℕ) (a : ℕ→ℂ) :
    energy S (transported q one neg a)=energy S a := by
  cases one <;> cases neg <;> simp [energy,transported,twist,norm_mul,phase_norm]

private theorem extend_vector (q : ℕ+) {L : ℝ} (hL : 1/2≤L) (S : Finset ℕ) (a : ℕ→ℂ)
    (bd : Dyadic L S) (h : ∀ n∈S,mark false n≠0) (ψ : HeightSeed) :
    spatial q false S a (mark false) h ψ=vector q (start L) (extension S a) ψ := by
  let M := start L
  have hM : 0<M := Nat.succ_pos _
  rw [←positive_vector q hM (extension S a) ψ]
  let P := fun n : ℕ => originalPoincare q.val false (n:ℤ) (scaledSeed (n:ℤ) ψ.toFun)
  have e (u) : (∑ i∈block M,star (extension S a (M+i))*P (M+i) u)=∑ n∈S,star (a n)*P n u := by
    have entry (n : ℕ) : star (extension S a n)*P n u=(if n∈S then star (a n)*P n u else 0) := by
      by_cases hi : n∈S <;> simp [extension,hi]
    simp_rw [entry]
    exact extend_sum hL S bd (fun n => star (a n)*P n u)
  have x := packet_L2 q.val false S a (mark false) h ψ.toFun ψ.continuous ψ.compact ψ.positive
  have y := packet_L2 q.val false (block M) (row M (extension S a)) (index M) (nonzero hM)
    ψ.toFun ψ.continuous ψ.compact ψ.positive
  apply Lp.ext
  filter_upwards [x.coeFn_toLp,y.coeFn_toLp] with u hu hv
  exact hu.trans ((e u).symm.trans hv.symm)

private theorem reduced_norm (q : ℕ+) (one neg : Bool) {L : ℝ} (hL : 1/2≤L)
    (S : Finset ℕ) (a : ℕ→ℂ) (bd : Dyadic L S) (r : ℝ) (j : ℕ) :
    ‖spatial q one S a (mark neg) (mark_ne (by linarith only [hL]) S bd neg) (compact r j)‖=
    ‖vector q (start L) (extension S (transported q one neg a)) (compact (if neg then -r else r) j)‖ := by
  have lp : 0<L := by linarith only [hL]
  have prep : ‖spatial q one S a (mark neg) (mark_ne lp S bd neg) (compact r j)‖=
      ‖spatial q false S (twist q one neg a) (mark neg) (mark_ne lp S bd neg) (compact r j)‖ := by
    cases one
    · rfl
    · exact fricke_norm q S a (mark neg) (mark_ne lp S bd neg) (compact r j)
  rw [prep]
  cases neg
  · exact congrArg norm (extend_vector q hL S (twist q one false a) bd (mark_ne lp S bd false) (compact r j))
  · let b := twist q one true a
    have n := negative_norm q S b (mark false) (mark_ne lp S bd false) r j
    exact n.trans (congrArg norm (extend_vector q hL S (fun i => star (b i)) bd
      (mark_ne lp S bd false) (compact (-r) j)))

def mass (q : ℕ+) (one neg : Bool) {L : ℝ} (hL : 1/2≤L) (S : Finset ℕ) (a : ℕ→ℂ)
    (bd : Dyadic L S) (K : ℝ) (j : ℕ) (r : ℝ) : ℝ :=
  weight K r*‖spatial q one S a (mark neg) (mark_ne (by linarith only [hL]) S bd neg) (compact r j)‖^2

def limit (q : ℕ+) (one neg : Bool) (L : ℝ) (S : Finset ℕ) (a : ℕ→ℂ) (K : ℝ) : ℝ :=
  limitEnergy q (start L) (extension S (transported q one neg a)) K

theorem energy_limit {K : ℝ} (kp : 0<K) (q : ℕ+) (one neg : Bool) {L : ℝ}
    (hL : 1/2≤L) (S : Finset ℕ) (a : ℕ→ℂ) (bd : Dyadic L S) :
    (∀ j,Integrable (mass q one neg hL S a bd K j)) ∧
    Tendsto (fun j : ℕ => ∫ r : ℝ,mass q one neg hL S a bd K j r) atTop (𝓝 (limit q one neg L S a K)) := by
  let b := extension S (transported q one neg a)
  let f := OriginalRegularCompactEnergy20261113.mass q (start L) b K
  have hM : 0<start L := Nat.succ_pos _
  obtain ⟨int,tend⟩ := OriginalRegularCompactEnergy20261113.energy_limit kp q hM b
  have red (r : ℝ) (j : ℕ) : mass q one neg hL S a bd K j r=f j (if neg then -r else r) := by
    rw [mass,reduced_norm q one neg hL S a bd]
    have ev : weight K (if neg then -r else r)=weight K r := by
      cases neg <;> simp [weight,neg_div]
    dsimp only [f,OriginalRegularCompactEnergy20261113.mass]
    rw [ev]
  constructor
  · intro j
    simp_rw [red]
    cases neg
    · exact int j
    · exact (int j).comp_neg
  · have E (j : ℕ) : (∫ r : ℝ,mass q one neg hL S a bd K j r)=∫ r : ℝ,f j r := by
      simp_rw [red]
      cases neg
      · rfl
      · exact MeasureTheory.integral_neg_eq_self (f:=f j) (μ:=volume)
    simp_rw [E]
    exact tend

theorem energy_bound {e K : ℝ} (he : 0<e) (hK : 2≤K) (q : ℕ+) (one neg : Bool) {L : ℝ}
    (hL : 1/2≤L) (S : Finset ℕ) (a : ℕ→ℂ) (bd : Dyadic L S) :
    limit q one neg L S a K≤((π*sqrt π/8)*K^3+
      OriginalRegularGaussianOffDiagonal20261113.cost e*K*((start L:ℝ)^(1+e)/q.val))*energy S a := by
  have hM : 0<start L := Nat.succ_pos _
  have h := OriginalRegularCompactEnergy20261113.energy_bound he hK q hM
    (extension S (transported q one neg a))
  rw [extension_energy hL S bd,transported_energy] at h
  exact h

end ImbalancedChen.Part3.OriginalRegularMarkedEnergy20261113
end

