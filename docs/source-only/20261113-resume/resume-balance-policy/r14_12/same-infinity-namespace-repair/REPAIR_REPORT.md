# Same-infinity compact trace: intended-symbol qualification

**SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.** Compiled modules: **0**;
kernel-verified modules: **0**. This successor makes one namespace repair in
`eisenstein`, by qualifying its two references to the existing native Fourier
coefficient. It does not redefine that coefficient.

The exact input is commit `a6aec20e831aa7f905533bec69fd0f86cd2bf9b1`, path
`docs/source-only/20261113-resume/resume-balance-policy/r14_09/avgj-reciprocity-next/same-infinity-pretrace/Part3OriginalSameInfinityCompactTrace.lean`:
3570 bytes, Git blob `c17935df92c9a7da67899b542d7413d2b4497e73`, SHA256
`c77d23a921bae65a1af855be96a9e544497ce9377dfca63f30d80e58542d9fe5`.
The original author freeze, publication source selection and independent
pretrace allowlist all identify these same bytes. The source and three
supporting anchors were read from exact Git objects, without choosing a
main-branch same-name file.

At a6's exact path
`docs/source-only/20261110-yellow-closure-10t/t08_actual_spectral_supplier/Part3ActualContinuousClassFourier.lean`,
line 6 opens namespace
`ImbalancedChen.Part3.ActualContinuousClassFourier20261110`; line 139 declares:

```lean
def nativeR {N : ℕ} [NeZero N] (a : Parameters N)
    (one : Bool) (n : ℤ) (t : ℝ) : ℂ :=
  ∑ ξ : DirichletCharacter ℂ (band N a.1.1),
    inverseWeight a.1 a.2 ξ*channelR ⟨a.1,ξ⟩ one n t
```

That module has Git blob `cb7fdff1839edb0a6c5d18c1e6b9a75ada427e42`, SHA256
`568cfdc089473872bee5db22e25a07c51ab7f75f9236c9d56965b4ba0e5b53f1`.
It declares no export of `nativeR`. The imported compact-spectrum file opens
`ActualContinuousClassFourier20261110` locally at line 17, and uses `nativeR`
inside that scope. Such an `open` does not become an open namespace in the
importing compact-trace source. CompactTrace's own namespace/open list does
not include this namespace; its two bare references occur at lines 41–42.
The compact pair contains no `nativeR` definition, alias or export, and the
bounded published-source search found no global export supplying this name.
No later same-path published corrected version was found in the local Git
history examined before this repair. ROOT selected this complete qualification
as the canonical successor; the separately proposed local-open alternative is
not part of this delivery.

The two references in the single definition `eisenstein` are changed to:

```lean
ImbalancedChen.Part3.ActualContinuousClassFourier20261110.nativeR
```

Everything else in the source is byte-identical. In particular both lambdas
retain the same `a`, `false`, frequency integer cast and real parameter `t`.
The same `nativeProduct q.val`, `radialProbe 1`, compact probes, actual Γ0
quotient, infinity observing frame and Fourier normalization are retained.
No namespace is opened for other declarations and no alternate object or
hypothesis is introduced. This is an intended-symbol binding repair, with no
new mathematical argument.

The five named declaration headers and the local instance are unchanged.
Static reconstruction by replacing precisely the two bare symbol occurrences
reproduces the whole postimage; no other bytes are changed. The new source is
3686 bytes, Git blob `9c7cdea7057b66c65ab32df0a58659d368ee8610`, SHA256
`390a1c64a67fb8eedf0aecae7d1258dbe3f2a4b4f3f59d21d5e49b6f4e570620`.
`NAMESPACE_ONLY.patch` is the minimal unified diff, and
`SOURCE_PINS_AND_STATIC_CHECKS.json` contains all source/anchor pins.
The unchanged a6 CompactSpectrum source is reused by its exact pin and is not
copied into or republished by this repair package.

Only this successor directory was written. The a6 original source, its freeze,
all P2 and height repair freezes, production and protected dirty continuation
were not changed. No local Lean/Lake/LSP, environment/setup, project helper,
proofguard, fixture, runtime, certificate, CI, Git/GitHub mutation, quota check
or agent spawn occurred. All verification is static source/hash/read-only Git
work. Independent 05 source review and any required validation remain.
