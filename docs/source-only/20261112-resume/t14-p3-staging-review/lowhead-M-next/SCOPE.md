# Four medium inequalities on the actual finite coefficient

The October 10 prime-product source, lines 51–63, uses the first individual medium HB length \(U\), the complete scale \(x=UV\), and residue \(a=T\). At \(\theta=7/32\), the four strict tests are

\[
 Q_1<Ux^{-\sigma},\quad U^2Q_2Q_3^2<x^{1-8\sigma},\quad
 |T|^{7/32}UQ_1Q_2^5Q_3^2<x^{2-15\sigma},\quad
 U^{23/16}Q_1Q_2^{73/16}Q_3^{39/16}<x^{2-15\sigma}.
\]

These are the middle four conjuncts of `Part3.MediumAdmissible`. The signed convolution bound itself, the moving residue range, the roughness and auxiliary Siegel–Walfisz estimate are distinct obligations. For the free finite signed fibre, `Index.atom` binds \(Q_i\) to the lower endpoints of the three actual dyadic owners. `all_free_words` uses `boxedErrors`, whose owner fields range over the images of the first two rough product sets and the actual third support. That support includes the original small Rosser factor. Merely supplying `Index.live` accounts for the HB fibre and places no restriction on the three arbitrary owner fields. Quantifying over the owner images in this sum supplies actual arithmetic witnesses even if a normalized coefficient cancels.

## Which partition the finite sum uses

`Index.groups` is `splitAt` on the word and the physical complete scale, HB length and width. Its source is `P4AOriginalFiniteFallbackGroupedAtoms.slots`. When the two above-\(\mu\) lookups miss, it calls `P4BUpperSelectedBoxCapacity.groups` with `J.take 1`, `J.drop 1`, and `J` itself. With \(A=U/x^\eta\) and \(D=x^{\text{old}+4\eta}\), the branch \(D/(A B_{\mathrm{selected}})\ge1\) puts the selected first slot in group 2, then assigns the remaining ordered list to groups 1 and 3. The other branch processes the whole word into groups 1 and 2 and leaves the rough part of group 3 empty. `actualTwoCapacityStep` accepts a slot into group 1 exactly when its new endpoint product fits \(A\). Starting at one, this gives the first endpoint bound whenever \(A\ge1\). Using an occupied owner gives \(Q_1\) at most that endpoint. For \(x>1\), \(0<\eta\) and \(\sigma<\eta\), the first strict test follows.

The original coefficient manuscript makes a length-dependent assignment on the whole marked box. Sections 3–5 retain the selected prefix and its selected-square conditions in the ordinary case. In the W case the first two slots initialize three capacities and a later first failure can change group 2. The physical exponent \(\lambda\) continues to determine \(Q=T^\lambda\) and the signed coefficient used in the count and coprime mean. An auxiliary exponent licenses the covering box independently. Replacing the group lists in the final convolution requires transporting the original coefficient, including marked multiplicities, restoring scalars, signs and the small Rosser attachment, through the new finite regrouping.

## A limitation of the deterministic endpoint rules in isolation

Consider an abstract ordered list of 28 equal endpoint exponents \(1/50\), with complete rough cover exponent \(59/100\). Its full square at slot \(j\) has exponent \((j+1)/50\); every such square is at most \(29/50\). Every odd-slot cube is at most \(29/50\) as well. Set \(U=x^{9/50}\), \(A=x^{9/50-1/1000}\), \(D=x^{59/100}\) and select the first singleton. Then \(D/(A x^{1/50})>1\). Among the other 27 slots precisely eight fit the left bin under the deterministic rule. The endpoint exponents of the three groups are \(8/50,1/50,19/50\). At these endpoints the second monomial has exponent \(2(9/50)+1/50+2(19/50)=57/50>1\), before any small-factor enlargement. This arithmetic illustrates why the full squares alone do not certify that particular three-group assignment. It concerns abstract endpoint data. An occupied original HB fibre, integer prime word, actual normalized gamma owners and a signed nonzero coefficient would all need separate witnesses for any counterexample to a physical statement.

`Chen7BelowMuBaseline.actual_belowMu_baseline_frozen_license` has hypotheses on the full low cell, winning index zero, the HB exponent interval, fine inflation and dwell support. `P4BOriginalHighRankMediumHeads.eventually_high_heads` has a strictly high first coordinate. Neither source by itself identifies the W or nonleading ordinary winner in every low word of the finite free sum.
