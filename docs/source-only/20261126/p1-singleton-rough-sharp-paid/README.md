# Historical singleton sharp-strip and local rough sharp norm

SOURCE ONLY / NOT ELABORATED / ZERO NEW FORMAL CREDIT.

These three candidates retain the original historical moduli, rho, shortSupport and signed shortSequence. They reuse the existing generic sharp-pair/strip-mean lemmas and the already written singleton smooth rough estimate. No target error, mass, mean, P2 or payment assumption is added.

`P1OriginalHistoricalTwoLongSharpComparison.lean` proves a finite historical endpoint invoice and the four explicit prices. The leading strip term retains its small integral 32 delta U V L^2 / phi(q); it is not replaced by the derivative price delta^(-2). The other terms are separately summed with the historical tau^0, tau^1 and tau^2 / phi moments, preserving the one totient denominator and exact mean structure.

With ell = log X0, M U V = X0, B = accuracy+30 and delta = ell^(-B), the four prices are:

- dominant: 256 * 8^16 * sizeConstant * pairCost * M Y^2 D^(3/2) * ell^24;
- leading strip: 262144 * 8^16 * sizeConstant * X0 delta * ell^26;
- cross: 4096 * 8^16 * sizeConstant * stripPrice * M(U+V)Y * ell^(25+2B);
- square: 256 * 8^16 * sizeConstant * stripPrice^2 * M Y^2 * ell^(24+4B).

`P1OriginalSingletonSharpComparisonPaid.lean` pays these via the actual P1 dominant and bare secondary suppliers plus the inverse-log supplier. It uses the real P1 one-quarter reserve. It does not invoke the P4 one-third or A+40 terminal. Each price is paid to accuracy+1, then ell>=4 combines the four terms. The endpoint difference needs no frequency window because the auxiliary positive strip profiles have zero frequency.

`P1OriginalSingletonRoughSharpPaid.lean` combines that endpoint difference and the complete local smooth rough norm at accuracy+1. Both calls use B=stripSmoothingOrder(accuracy+1)=accuracy+31, the same original cutoffOrder, and the same N/Q/rho/short sequence. The smooth call has label 0, so its two Mellin profiles are exactly the upper profiles in the endpoint difference. Its original two-long logarithmic frequency window is retained. With ell>=2, the two contributions give the complete local rough sharp-profile norm at accuracy.

Accuracy, smoothing/frequency/cutoff orders and manuscript parameters are fixed before the single eventual physical N threshold. Active singleton, HB rows, history parameters and frequencies are quantified afterwards.

Independent mathematical/source reviews found no concrete obstruction in the frozen files. These reviews are not Lean elaboration. The registered FixedM original source is still unavailable; the existing import/unique-owner closures remain unresolved. Native rectangle equality, full Fourier retained/tail reconstruction, outer HB/selector summation and the complete signed medium branch are not supplied by this local norm. Whole P1.5 remains open.
