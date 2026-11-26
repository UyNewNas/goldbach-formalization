import P24RecursionRepairs20261126.ScopeAttempt003.ArrayTable
open ImbalancedChen.P2OriginalCompactQ80EncloserSourceOnly
open ImbalancedChen.P2OriginalCompactQ80ArrayTableSourceOnly
example (g : ℕ) (nodes : Array Node) : buildFrom g 0 nodes = nodes := by rfl
example (g remaining : ℕ) (nodes : Array Node) :
    buildFrom g (remaining+1) nodes = buildFrom g remaining (appendNode g nodes) := by rfl
