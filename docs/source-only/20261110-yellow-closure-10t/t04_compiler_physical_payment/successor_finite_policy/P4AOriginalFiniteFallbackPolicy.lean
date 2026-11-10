import ImbalancedChen.P4AOriginalFiniteFallbackBank
import ImbalancedChen.P4AOrderedThirdCommonSchedule

namespace ImbalancedChen.P4AOriginalFiniteFallbackPolicy
noncomputable section
open scoped Classical
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFiniteFallbackBank (Bank read)
open P4AOriginalOrderedThirdFullPolicy (current)
open P4AOriginalNewFifthUnion (data)

abbrev Rule := Bool → List ℕ → Bool

def point (N : ℝ) (k : ℕ) (p : List ℕ) := primeHistoryLogCoordinates N k (rosserAncestor k p)

def high (N : ℝ) (p : List ℕ) : Prop := VariableEnvelope.mu < point N 1 p 0

def dispatch (N : ℝ) (upper lower : Rule) (pos : Bool) (p : List ℕ) : Bool :=
  if high N p then upper pos p else lower pos p

def choose (a : Option ℚ) (inherited : ℝ) : ℝ :=
  match a with | some c => (c:ℝ) | none => inherited

def secondLevel (B : Bank) (d : OriginalData) (w N : ℝ) (p : List ℕ) :=
  choose (read B.mesh B.second (point N 2 p)) (current d w N p).scalar

def level (B : Bank) (d : OriginalData) (w N : ℝ) (p : List ℕ) :=
  if p.length≤3 then secondLevel B d w N p else
    choose (read B.mesh B.third (point N 3 p)) (secondLevel B d w N p)

def upper (B : Bank) (d : OriginalData) (w N : ℝ) : Rule := fun pos p =>
  if p.length≤2 then HistoricalThirdCoarse.initialPolicy d.e d.m N pos p else
    ordinaryParityRosserPolicy false (N^level B d w N p) pos p

def policy (B : Bank) (delta : ℝ) (n : ℕ) (d : OriginalData) (w N : ℝ) : Rule :=
  dispatch N (upper B d w N) (P4AOriginalOrderedThirdFullPolicy.policy delta n d w N)

abbrev F (B : Bank) (delta : ℝ) (n : ℕ) (d : OriginalData) (w : ℝ) (N : ℕ) :=
  policy B delta n d w N false

def rho (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a w : ℝ) (N : ℕ) (tau L : ℝ) :=
  P4AUpperTaggedBetaAttachment.rho (F B (P4AOriginalFull87HistoryCore.width r) n (data e q a) w N)
    (fun _ => []) N N ((N:ℝ)^w) (P4AOriginalFull87RawChronology.cutoff N) tau L

theorem lower_history (B : Bank) (delta : ℝ) (n : ℕ) (d : OriginalData) (w N : ℝ)
    (pos : Bool) (p : List ℕ) (h : point N 1 p 0≤VariableEnvelope.mu) :
    policy B delta n d w N pos p=P4AOriginalOrderedThirdFullPolicy.policy delta n d w N pos p := by
  exact if_neg (not_lt.mpr h)

theorem rank_three (B : Bank) (d : OriginalData) (w N : ℝ) (p : List ℕ) (hp : p.length=3) :
    upper B d w N false p=decide (ordinaryRosserPrefixAdmissible false (N^secondLevel B d w N p) p) := by
  simp [upper,level,hp,ordinaryParityRosserPolicy,oddFirstExitPolicy]

theorem inherited (B : Bank) (d : OriginalData) (w N : ℝ) (p : List ℕ)
    (h2 : read B.mesh B.second (point N 2 p)=none)
    (h3 : read B.mesh B.third (point N 3 p)=none) : level B d w N p=(current d w N p).scalar := by
  simp [level,secondLevel,choose,h2,h3]

theorem third_hit (B : Bank) (d : OriginalData) (w N : ℝ) (p : List ℕ) (hp : 3<p.length)
    {c : ℚ} (h : read B.mesh B.third (point N 3 p)=some c) : level B d w N p=(c:ℝ) := by
  simp [level,not_le.mpr hp,h,choose]

theorem policy_cut (B : Bank) (delta : ℝ) (n : ℕ) (d : OriginalData) {N : ℕ} (hN : 1≤N)
    {w : ℝ} (hw : 0≤w) (p : List ℕ) (hp : ∀ x∈p,(N:ℝ)^w≤(x:ℝ)) :
    F B delta n d w N p=F B delta n d 0 N p := by
  simp only [F,policy,dispatch,upper,level,secondLevel,P4AOriginalOrderedThirdFullPolicy.policy,
    P4AOrderedThirdRoughCutTransport.root_cut (by exact_mod_cast hN) hw d p hp]

end
end ImbalancedChen.P4AOriginalFiniteFallbackPolicy
