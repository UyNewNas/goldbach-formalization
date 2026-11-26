import ImbalancedChen.Certificates.P2OriginalP160DirectDivision

open ImbalancedChen.OriginalThirdClippedChordSourceOnly
open ImbalancedChen.OriginalThirdRoundedNewSourceOnly
open ImbalancedChen.Certificates.P2OriginalP160DirectDivision

example (x y : IV) (hp : 0 < y.lo) (ho : y.lo ≤ y.hi) :
    toEnclosure (directDiv x y) =
      ((toEnclosure x).divisionBounds (toEnclosure y)).round 160 :=
  directDiv_eq_round160 x y hp ho

example (x y : IV) (v w : ℝ) (hx : Encloses x v) (hy : Encloses y w) (hp : 0 < y.lo) :
    Encloses (directDiv x y) (v / w) :=
  directDiv_contains hx hy hp

private def two : IV := ⟨2 * P160, 2 * P160⟩
private def three : IV := ⟨3 * P160, 3 * P160⟩

-- The paired producer divides directly. Its upper endpoint is one unit below
-- the upper endpoint obtained by rounding 1/3 before multiplying by 2.
example : ((directDiv two three).lo, (directDiv two three).hi) =
    (974334424887268612135789888477522013103955028650,
     974334424887268612135789888477522013103955028651) := by decide

example : ((divide two three).lo, (divide two three).hi) =
    (974334424887268612135789888477522013103955028650,
     974334424887268612135789888477522013103955028652) := by decide

#print axioms directDiv_eq_round160
#print axioms directDiv_contains
