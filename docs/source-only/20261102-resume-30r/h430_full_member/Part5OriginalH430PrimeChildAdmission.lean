import ImbalancedChen.Part5OriginalH430FullMemberStrips
import ImbalancedChen.P2EnhancedLowerPrimeChildGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact missing source conversion: the EXISTING finite integer prime-child
carriers provide positive physical coordinates, normalized bank domains,
the physical ceiling and both new squares.  They do not contain the
parent query/cutoff tests, which remain explicit in the theorem below.
Those tests are strictly smaller than LocalDomain: every child test is
derived from the actual integer membership.  No full Member, source
count licence or domain equivalence is postulated.

CAUTION ON SCOPE: these production carriers both use Coprime (N*B).
For W2 this is the strict non-repeat subfamily.  The manuscript's restored
N-window repeat/diagonal occurrences are not represented by this carrier
and are not licensed by the conversion below.
-/

namespace ImbalancedChen.Part5OriginalH430PrimeChildAdmission

noncomputable section
open Set Classical
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildGeometry
open P2EnhancedLowerPrimeChildCarriers (SingleRule physicalPrime)

def singleShape : SingleRule → StepShape
  | .buchstab true _ => .buchstabUpper
  | .buchstab false _ => .buchstabLower
  | .w1 i j => .w1Singleton i j
  | .w2 j piece => .w2Singleton j piece

def singleCoordinates (N prime : ℕ) : Point := ![physicalPrime N prime, 0]
def pairCoordinates (N small large : ℕ) : Point :=
  ![physicalPrime N small, physicalPrime N large]

/-- These are the actual parent tests absent from singleChildren.
Buchstab's argument is already a parameter of its integer carrier. -/
def SingleParentTests (p : PhysicalNode) : SingleRule → Prop
  | .buchstab _ s => p.argument=s
  | .w1 i _ => p.argument≤W1Target i ∧ residual p/W1Target i≤p.ceiling
  | .w2 j _ => p.argument≤(originalW2At j).s ∧ residual p/(originalW2At j).s≤p.ceiling

def PairParentTests (p : PhysicalNode) (j : Fin 36) : Prop :=
  p.argument≤(originalW2At j).s ∧ residual p/(originalW2At j).s≤p.ceiling

theorem physicalPrime_pos {N q : ℕ} (hN : 1 < N) (hq : q.Prime) :
    0 < physicalPrime N q := by
  exact div_pos (Real.log_pos (by exact_mod_cast hq.one_lt))
    (Real.log_pos (by exact_mod_cast hN))

theorem physicalPrime_strictMono {N small large : ℕ} (hN : 1 < N)
    (hs : small.Prime) (h : small < large) :
    physicalPrime N small < physicalPrime N large := by
  apply div_lt_div_of_pos_right _ (Real.log_pos (by exact_mod_cast hN))
  exact Real.log_lt_log (by exact_mod_cast hs.pos) (by exact_mod_cast h)

theorem actual_normalized_single {N prime : ℕ} {Q chi : ℝ} {old : List ℕ}
    {p : PhysicalNode} (hw : P2EnhancedLowerPrimeChildCarriers.parentWindow N Q old chi)
    (hL : residual p=physicalLevel N Q old) :
    normalized p (singleCoordinates N prime) 0 =
      P2EnhancedLowerPrimeChildCarriers.relativePrime Q old prime := by
  have hp := relativePrime_physical (p := prime) hw
  have hpos := (parentWindow_logs hw).2.2
  dsimp [normalized, singleCoordinates]
  rw [hL, ← hp]
  exact mul_div_cancel_left₀ _ hpos.ne'

theorem actual_normalized_pair {N small large : ℕ} {Q chi : ℝ} {old : List ℕ}
    {p : PhysicalNode} (hw : P2EnhancedLowerPrimeChildCarriers.parentWindow N Q old chi)
    (hL : residual p=physicalLevel N Q old) :
    normalized p (pairCoordinates N small large) =
      P2EnhancedLowerPrimeChildCarriers.pairPoint Q old small large := by
  funext i
  fin_cases i <;>
    simpa [normalized, pairCoordinates, P2EnhancedLowerPrimeChildCarriers.pairPoint,
      singleCoordinates] using (actual_normalized_single (prime := _) hw hL)

theorem actual_buchstab_argument {N prime : ℕ} {Q chi : ℝ} {old : List ℕ}
    {p : PhysicalNode} (hw : P2EnhancedLowerPrimeChildCarriers.parentWindow N Q old chi)
    (hprime : prime.Prime) (hL : residual p=physicalLevel N Q old) :
    P2EnhancedLowerPhysicalTransition.buchstabArgument p (singleCoordinates N prime) =
      P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old prime := by
  have hN := (parentWindow_logs hw).1
  have hp : 0 < Real.log (prime : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
  dsimp [P2EnhancedLowerPhysicalTransition.buchstabArgument, singleCoordinates]
  rw [hL]
  dsimp [physicalLevel, physicalPrime, P2EnhancedLowerPrimeChildCarriers.buchstabArgument]
  field_simp [hN.ne', hp.ne']
  ring

/-- Every new one-prime physical gate is supplied by the literal carrier.
No extra square/ceiling/bank-domain hypothesis is left to its caller. -/
theorem singleChild_LocalDomain {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {p : PhysicalNode} {rule : SingleRule} {prime : Fin (N+1)}
    (hprime : prime ∈ P2EnhancedLowerPrimeChildCarriers.singleChildren rule N Q old chi)
    (hL : residual p=physicalLevel N Q old) (hC : p.ceiling=chi)
    (hparent : SingleParentTests p rule) :
    LocalDomain p (singleShape rule) (singleCoordinates N prime.val) := by
  have h := P2EnhancedLowerPrimeChildCarriers.mem_singleChildren.mp hprime
  have hpos : 0 < residual p := by
    rw [hL]
    exact (parentWindow_logs h.2.1).2.2
  have hgate : OneGate p (physicalPrime N prime.val) := by
    refine ⟨physicalPrime_pos h.2.1.1 h.1.1, ?_, ?_⟩
    · rw [hC]
      exact h.2.2.2.1.le
    · rw [hL]
      exact single_residual_square hprime
  have hn := actual_normalized_single (prime := prime.val) h.2.1 hL
  have hb := actual_buchstab_argument h.2.1 h.1.1 hL
  cases rule with
  | buchstab up s =>
      change p.argument=s at hparent
      cases up with
      | false =>
          refine ⟨hpos, ?_, hgate, ?_⟩
          · simpa only [hparent] using h.2.2.1.1
          · simpa only [hb, hparent] using h.2.2.1.2
      | true =>
          refine ⟨hpos,hgate,?_⟩
          simpa only [hb,hparent] using h.2.2.1.2
  | w1 i j =>
      exact ⟨hpos,hgate,by simpa only [hn] using h.2.2.1,hparent⟩
  | w2 j piece =>
      exact ⟨hpos,hgate,by simpa only [hn] using h.2.2.1,hparent⟩

/-- Pair append order remains [larger,smaller].  Both full/selected new
square inequalities are derived from the same original D5+..D8 member. -/
theorem pairChild_LocalDomain {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {p : PhysicalNode} {bank : Fin 36} {piece : Fin 4}
    {primes : Fin (N+1) × Fin (N+1)}
    (hprimes : primes ∈ P2EnhancedLowerPrimeChildCarriers.pairChildren bank piece N Q old chi)
    (hL : residual p=physicalLevel N Q old) (hC : p.ceiling=chi)
    (hparent : PairParentTests p bank) :
    LocalDomain p (.w2Pair bank piece)
      (pairCoordinates N primes.1.val primes.2.val) := by
  have h := P2EnhancedLowerPrimeChildCarriers.mem_pairChildren.mp hprimes
  have hpos : 0 < residual p := by
    rw [hL]
    exact (parentWindow_logs h.2.1).2.2
  have hs := pair_residual_squares hprimes
  have hn := actual_normalized_pair h.2.1 hL
  refine ⟨hpos, ?_, ?_, hparent⟩
  · refine ⟨physicalPrime_pos h.2.1.1 h.1.1.1,
      physicalPrime_strictMono h.2.1.1 h.1.1.1 h.2.2.1, ?_, ?_, ?_⟩
    · simpa only [hC] using h.2.2.2.2.2.1.le
    · simpa only [hL] using hs.1.le
    · simpa only [hL] using hs.2.le
  · simpa only [hn] using h.2.2.2.1

theorem singleChild_gates {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {p : PhysicalNode} {rule : SingleRule} {prime : Fin (N+1)}
    (hprime : prime ∈ P2EnhancedLowerPrimeChildCarriers.singleChildren rule N Q old chi)
    (hL : residual p=physicalLevel N Q old) (hC : p.ceiling=chi)
    (hparent : SingleParentTests p rule) (hf : fullGates p) (hs : selectedGates p) :
    fullGates (perform p (singleShape rule) (singleCoordinates N prime.val)) ∧
      selectedGates (perform p (singleShape rule) (singleCoordinates N prime.val)) :=
  perform_gates hf hs (singleChild_LocalDomain hprime hL hC hparent)

theorem pairChild_gates {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {p : PhysicalNode} {bank : Fin 36} {piece : Fin 4}
    {primes : Fin (N+1) × Fin (N+1)}
    (hprimes : primes ∈ P2EnhancedLowerPrimeChildCarriers.pairChildren bank piece N Q old chi)
    (hL : residual p=physicalLevel N Q old) (hC : p.ceiling=chi)
    (hparent : PairParentTests p bank) (hf : fullGates p) (hs : selectedGates p) :
    fullGates (perform p (.w2Pair bank piece) (pairCoordinates N primes.1.val primes.2.val)) ∧
      selectedGates (perform p (.w2Pair bank piece)
        (pairCoordinates N primes.1.val primes.2.val)) :=
  perform_gates hf hs (pairChild_LocalDomain hprimes hL hC hparent)

end
end ImbalancedChen.Part5OriginalH430PrimeChildAdmission
