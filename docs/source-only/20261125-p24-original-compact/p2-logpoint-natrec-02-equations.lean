import «p24-logpoint-natrec-20261126».«attempt-002».LogPoint
open ImbalancedChen.Certificates.P2HistoricLogPointInterpreter
example : ∀ square ul uh, oddLoop square ul uh 0 = oddStart ul uh := by
  intros; rfl
example : ∀ square ul uh n, oddLoop square ul uh (n+1) = oddStep square n (oddLoop square ul uh n) := by
  intros; rfl
