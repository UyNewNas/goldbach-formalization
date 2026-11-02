# P20 / enhanced_switch_mass

Status: **OPEN; source only; uncompiled; kernel_verified=false; formal_credit=0**.

This packet supplies the two actual enhanced-Q unsifted unit upper masses, plus the receiver-level purification and scalar Buchstab step needed before the remaining nonunit masses can be integrated. It does not reprove O's finite-Q comparison, assume a switched mass/count licence, assert a positive-product density, or close either broad yellow node.

## Source inspection and difficulty

Read BRIEF.md and this directory's PRIOR_TASK.json, then both complete files in O/enhanced_switch_mass. That frozen O directory contains exactly its two Lean files; REPORT.md and REGISTRY.json were absent when inspected. O proves the arbitrary-Q finite comparisons, full word multiplicities, unit/nonunit partition, physical alpha algebra and continuous envelopes. It explicitly does not prove an arithmetic source mass limit.

Read the current manuscript lines 795–855 (SHA256 ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd), the source extension lines 106–128, and completion lines 173–237. The relevant requirements are the positive finite sigma and original Theta at 795–806, actual alpha and unchanged Q at 808–817, bad Gamma5 exclusion at 850–852, and separate unit masses and uniform omega envelope at 852–855.

The first obstacle is **(2) a fillable omitted source deduction**, not just Lean syntax. O's roughCarrier uses Sifted(d*N), so a prime dividing d*N is exempt. Removing receiver primality and then declaring this raw carrier to be ordinary roughNumbers is unjustified. The native definition is GoldbachWeights.lean:18. For example, when 2 divides N, the old mask does not exclude the quotient 2 even if z>2; ordinary Rough z 2 does. This is evidence against the carrier identification, not a numerical counterexample to the manuscript theorem. The native high and lower-triple purification sources separately retain square-raw and bad-N PRIME errors, which confirms that this conversion requires work.

The unit obstacle is also **(2)** and is supplied here. The native HighUnitSource.geometry20/21 and prefix_le20/21 consume the prime-receiver unit carrier. O's unitWordMass is larger: it has already removed receiver primality. Reusing the native source inequality directly would be unsound. The new geometry instead derives last-prime physical membership from d*l.prod<=N, retaining the full source list. It reuses the native structural/color/slab API and the actual physical prime-fibre limit, rather than copying or extending the classical-Q arithmetic receiver.

There remains **(1) Lean elaboration/API verification**: no compiler was run. Static review corrected a list-equality head projection and made the final conversion algebra explicit. No **(3) substantive manuscript contradiction** is claimed. The missing aggregate nonunit/exception suppliers below remain a source-level gap. If an asserted theorem were interpreted as allowing arbitrary small-prime factors of d with no source roughness, its exceptional-payment argument would need additional justification; this packet does not add such a claim.

## New actual source suppliers

P2EnhancedUnitSourceGeometry.lean:
- physical_of_product and geometry20/geometry21 embed the literal O product-bounded source lists into the native physical last-prime fibres. Gamma20 has five source primes and a four-prime prefix; Gamma21 has six source primes and a five-prime prefix.
- product_count_le_physical is an injection of complete lists. Equal products do not merge different labels.
- actual_unit_masses_le_physical applies O.unitWordMass_eq_product_count to both actual unsifted unit sources. It does not introduce a fictitious prime receiver.

P2EnhancedUnitSourceMass.lean:
- scale_identity proves (Q/d)^trueAlpha=N/d for the genuine logarithmic alpha.
- physical_pair_uniform uses native HighUnit.physical_pair_uniform, whose threshold is before every R, window and phi. A fixed eta>0 and R=Q/d>=N^eta choose one N threshold before Q and d.
- actual_unit_upper_uniform proves, separately for i=20,21,
  U_i(N,Q,d) <= N/(d*log(Q/d)) * J_i(trueAlpha(N,Q,d))
                + epsilon*N/(d*log(Q/d)).
  Here U_i is O's actual unitWordMass, not a closed physical envelope substituted for the source. The envelope is used only as a proved upper bound. No bilateral source limit is needed for this upper-mass obligation.
- actual_unit_theta_upper proves the two independent positive sigma-weighted converted upper bounds, allocating epsilon/2 to each and epsilon to their sum. It uses the exact O thetaConversion and original thetaAtom, singular factor C(dN), phi(d), true li(N), and common Q.
- convertedUnit20/21 explicitly mean sum sigma(d)*thetaConversion(N,d)*U_i. This is a mathematically defined conversion of the raw mass. It is **not** a claim that an actual PP count has this density or a K/4 coefficient.
- zero_theta_units proves both converted unit sources and both integral payloads are exactly zero when the original Theta is zero, using existing primitive positivity. No mass division or positive-total premise is used.

The new unit upper theorem requires only fixed positive eta, positive d, and Q/d>=N^eta at sufficiently large N. It does not require a classical-Q source box, even N, a mass/count estimate, or alpha=2. The original unit charts are identified with the already existing first-coordinate J20 and last-coordinate J21 masses; no factor or unit component is merged.

## Purification and the remaining nonunit step

P2EnhancedReceiverRoughPurification.lean proves:
- The literal sieveCarrier splits above by its ordinary-rough receiver part plus two exact exceptions: not Coprime d ((N-ell)/D), and not Coprime ((N-ell)/D) N.
- For even N>=4, the ordinary-rough receiver injects into actual roughNumbers (N/D) z.
- The exact bad-N quotient event is a subset of N.primeFactors in receiver labels. The broader event ell|N is not equated with it.
- The old-prefix repeat event is bounded by the existing finite floor sum over prime factors of the COMPLETE labelled divisor D, when d divides D.
- Both exact exceptions exclude quotient one. No unit is silently assigned to these errors.
- receiver_buchstab_upper uses the existing InclusiveRoughUniform.uniform_upper. Its threshold precedes D,d,z; it retains the unit term separately and the closed nonunit gate z<=N/D.
- physical_buchstab_argument identifies its exact argument as
  (trueAlpha - log(l.prod)/log(Q/d)) / (log(z)/log(Q/d)).
- quotient_word_upper and original_word_upper bind this purification to every literal original colour word, retaining the additional selected-prime collision already exposed by the previous production source.
- original_badPair_upper binds it to the actual excluded Gamma5 pair source, its equality-inclusive bad-square gate, original ordered labels and inherited a0 cutoff.

These are genuine finite/scalar suppliers. They do not yet pay the newly exposed repeatWordMass/centerWordMass uniformly over the actual positive marked family. The native fixed-positive-cutoff floor and label-multiplicity tools are available for that next step, but their old-prefix roughness and source multiplicity premises must be derived from the actual marks. Positivity of d alone is insufficient.

The earlier selected-prime collision is different: production P2EnhancedCollisionThetaPayment.collision_theta_payment:50 already pays weightedCollisions at the same Theta, using its actual weighted floor/reciprocal budget, Q<=N and fixed lower cutoffs for old and new prime factors. That existing chain is reused and not redone. Its actual-mark support prerequisites and the newly exposed repeat/center event payments must not be conflated.

The remaining analytic work is the actual ordinary rough nonunit prime-sum to the Gamma5/Gamma9–21 integral dictionaries at varying enhanced Q, including endpoint/tail errors, compact uniformity, original word multiplicities and positive same-Theta lifting. The native NonunitRoughUniform and closed-quadrature proofs were inspected; this packet supplies the scalar input and genuine-alpha argument, not the full arithmetic quadrature. O's omega envelope and full20/full21 continuous caps remain valid reusable downstream steps. No new omega constant or manuscript range is introduced.

The alpha>=2 premise remains an actual source condition where the nonunit envelope needs it. O.trueAlpha_ge_two_iff proves it is equivalent to 2*nu<=1+log_N d when L>0. Positive residual L alone does not imply it at enhanced nu>1/2. The unit upper supplier here is stronger and needs no artificial alpha lower bound.

## Exact reuse and installation

All raw SHA256 values, new declaration line numbers, direct imports, actual native source paths and intended install targets are in REGISTRY.json. Key reused sources are:

| Actual source | Reused declaration / role | SHA256 |
|---|---|---|
| O/enhanced_switch_mass/P2EnhancedSwitchedUnsiftedSource.lean | unitWordMass_eq_product_count:150, labels and original word/pair sources | 0996a926dd43a4b017d21393c97ae51f5df47f9ebe8ec14fa7c4d190fc05ac91 |
| O/enhanced_switch_mass/P2EnhancedSwitchedTrueNormalization.lean | trueAlpha, rawMainAtom_to_thetaAtom:103, thetaPayload | 1082e7e6ed3b23a9828aeb68cf2a2072a0b13e377799988825fb4fd8ebb1a11d |
| O/h247_moving_mass/P2OriginalPositiveSameQMassLift.lean | thetaAtom_nonneg:32 | bec25f9fdca24ffaba071b8f49aaeb3a21fec454f3088543f04f9b1544a6e565 |
| M/h247_w2_mass_license/P2OriginalChildPhysicalNormalization.lean | Theta_eq_sum_atoms:26, thetaAtom | 5203b9a60fc2890ec3f3b0a1f31a5d726f293643f59a3eedf8c461d0c802e04d |
| Native SecondFunctionalHighUnitLimit.lean | HighUnit.physical_pair_uniform:43 | acb888fc47cc52367c05da21b0c95e2cdd19b968ff3cc6acb8e458bcecdfbc9c |
| Native SecondFunctionalHighUnitBoxedLimit.lean | HighUnit.unnormalize:59 | cf3451b3aa0898bde5f858bb66533468e02dd98887b6a36fffbfcbf470a102a4 |
| Native SecondFunctionalHighUnitSourceGeometry.lean | length_five:8 and length_six:17; structural provenance | d3a5251b8aa46b5506df199e7a1c412ad991fdb557abe8c1c7c16b19090f7bd7 |
| Native SecondFunctionalHighUnitSourceCore.lean | fullList, colour_two:100, colour_three:105, slab_of_window:111 | ed869b5e373b40be26539f8fcae184e27b938c70a1a8872528483b5c47d44cb4 |
| Native InclusiveRoughUniform.lean | uniform_upper:53, with independent unit | a0cc25326c20fcc9e26c69f57d267c02c55593cc617025ffc92ca8fe2e591896 |
| Native Omega3FiniteError.lean | omega3_bad_complements_card_le:22 | 20ee1353c70fbdcd761f848abb5ec53c1b111d23873cb81ff4dba1acec6b3ca0 |

O means docs/source-only/20261102-resume-30o; M means docs/source-only/20261102-resume-30m. Native files were actually read at //wsl.localhost/Debian/home/slava/codex-lean-ve/native-packages/goldbach/research/wu2008/src/MathlibNt/Wu2008DoubleSieve/. The native proof statements, not just their names, were inspected.

The earlier production P2SeedOmegaSwitchedArithmeticFour.original_Gamma12_to_15_uniform_threshold remains classical-Q with coefficient 2/(1-2delta); P2SeedOmegaActualUnitCountReceiver.actual_unit_counts_receiver remains tied to the classical source box. Neither is renamed at enhanced Q. P2SeedOmegaLastFullMassBounds.full_masses_le_original is a continuous cap, not an arithmetic mass supplier.

The two O enhanced files and M normalization must be installed before the new files. The O positive-lift dependency chain remains pinned by its existing REGISTRY (SHA256 272b9b5683b879041d23c4ff977e5751c970d95edea50a45f5f6caa78136669e). Nothing has been installed or modified outside the assigned P directory.

## Checks and final status

Only source reads, text searches, declaration/import inventory, JSON parsing and SHA256 checks were performed. No Lean/lake/compiler, CI, kernel replay, finite guard evaluation, numerical producer/replay/search, Git operation or child agent was used. New proof bodies contain no sorry/admit/axiom or target mass/count/PP assumption. Every finite guard remains UNEVALUATED.

Unit upper-mass source and normalization sub-obligations are supplied at source level, subject to compilation. Full enhanced switched mass, exception payment, positive PP/count licensing and the broad nodes P2.9.bank_endpoint_licences and P5.6.eight_suppliers remain **OPEN**.

