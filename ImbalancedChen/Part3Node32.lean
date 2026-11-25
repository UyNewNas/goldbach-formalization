import ImbalancedChen.Part3ComplexCRTFiniteFourier
import ImbalancedChen.Part3SharedFirstFactorEnergyNonzeroReduction
import ImbalancedChen.Part3ActualCompletedZeroDifferencePayment
import ImbalancedChen.Part3ActualNonzeroChartEpsilonTagPayment
import ImbalancedChen.Part3ActualZeroTagFreeEpsilonPayment
import ImbalancedChen.Part3ActualKPacketAdapter

/-!
# P3.2 selected manuscript proof interfaces

This entrypoint composes existing proofs; it does not redeclare their theorems.
The six selected terminals retain their historical source and declaration
identities. See docs/part3-distribution/node32-20261125 for provenance and the
current verification result.

The shared-first-factor endpoint pays the initial Poisson zero covariance and
the original primitive U/V terms, leaving the complete same-p nonzero sum.
The completed-square endpoint separates y = 0, with the original tags and
physical factors retained. The K adapter reconstructs its explicitly selected
K/q kernel and proves the absolute interchange budget.

Finite sampled Fourier zero frequency is not the integral Poisson zero
frequency. The complete progression identities connect the two expansions.
Neither an arbitrary transposed atom's admissibility nor a full nonzero
spectral estimate is supplied by this module. The later reciprocal kernel's
m = 0 physical return and all remaining outer physical payments must retain
their own explicit verification boundaries.
-/
