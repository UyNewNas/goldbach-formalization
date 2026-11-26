# Historical singleton Fourier invoice — source only

P1OriginalHistoricalSingletonFourier.lean derives the original normalized
amplitude L1 budget C * log(N+2)^72 / 2^r and the complete historical Q mass.
It separately pays the exact-product collision and omitted-frequency tail.

P1OriginalSingletonRetainedFourierInvoice.lean combines that budget with the
previous native two-long proof for the original selected remaining row.
The actual dimension r=2*(j+1)<=6 is retained. The common cutoff is
(1+log(896*N))^(tailAccuracy+4245); the native frequency order is
tailAccuracy+4246. Both long frequencies remain in their original slots.

These files add no derivative, L1, mass, tail, error-payment or Family premise.
They do not yet perform the original outer chart/order/block sum.
INDEPENDENT_FOURIER_REVIEW.json binds the final source hashes. The historical
implementation notes precede a single reviewed local tactic spelling fix;
the review records both that prior hash and the final hash.

No Lean or kernel acceptance is claimed. Missing original sources, dependency
postimages, medium physical families and full P1.5 closure remain outstanding.
