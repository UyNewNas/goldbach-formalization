import P24RecursionRepairs20261126.ScopeAttempt003.Encloser
open ImbalancedChen.P2OriginalCompactQ80EncloserSourceOnly
open ImbalancedChen.Certificates.P2HistoricQ80DefectLookup
example (square : I80) (ul uh : ℤ) :
    logLoop square ul uh 0 = ⟨⟨ul,uh⟩,I80.raw 0⟩ := by rfl
example (square : I80) (ul uh : ℤ) (n : ℕ) :
    logLoop square ul uh (n+1) = logStep square n (logLoop square ul uh n) := by rfl
example : firstSeries 0 = (1/2,0) := by rfl
example (n : ℕ) : firstSeries (n+1) =
    (let prev := firstSeries n
     let k := n+1
     let coefficient := if k = 1 then (1/2 : ℚ)
       else prev.1/2 + 1/(2*(k : ℚ))
     let term := coefficient * (theta/rho-3)^(k+1)/((k+1 : ℕ) : ℚ)
     (coefficient,prev.2 + if k % 2 = 1 then term else -term)) := by rfl
