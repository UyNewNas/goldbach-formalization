# Actual singleton complete rough smooth payment candidate

This source-only module continues `P1OriginalSingletonRoughComparisonPaid`. It proves the complete smooth historical rough discrepancy bound, including its unchanged exact coprime mean, on the existing wideWindow profiles. Independent static review found no additional mathematical break or definite Lean signature mismatch; no elaboration or owner acceptance has occurred.

The public theorem `eventually_actual_singleton_rough_smooth_paid` retains all original profile conditions and explicitly assumes the original logarithmic band for the two long frequencies, `abs(t1), abs(t2) <= (log X0)^frequencyOrder`. The short frequencies remain arbitrary. All fixed accuracy/smoothing/frequency/cutoff orders precede the same physical N threshold.

The proof uses the existing historical upper-core P2 bound. The existing moment and short-log bounds give the constant `128*8^16` and logarithmic exponent 22; a larger fixed threshold supplies one more logarithm, so the existing dominant payment with `extraLog=23` pays the core at accuracy+1. The previously reviewed comparison pays rough-minus-upper at accuracy+1. Their triangle sum is paid at accuracy because `log X0 >= 2`. It adds no target-error, short-mass, P2 or asymptotic-payment premise.

This does not yet transfer the smooth wideWindow profiles to sharp rectangles, pay the small-integral endpoint strips, restore Fourier tails or sum outer HB/selector occurrences. Existing original-source and unique-owner closure boundaries remain. The file is outside the 360-source correction acceptance inventory and does not close P1.5.
