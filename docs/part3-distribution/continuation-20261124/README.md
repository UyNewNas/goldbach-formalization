# Accepted P3 continuation inventory

The accepted continuation, through source commit
`198f777f25d5a236f9456e0dbb16fafc8fc823b7`, comprises
**ten modules and 204 complete serialized declarations** with
strict compilation, kernel replay and full transitive-axiom acceptance.
The baseline c509267's 80 modules and 1,774 declarations are unchanged.
Combined, these inventories cover 90 modules and 1,978 declarations.
**P3 as a whole remains open.**

| Evidence | Selected modules | Selected declarations |
| --- | ---: | ---: |
| [Proper-power at 60cf3d49](proper-power-60cf3d49/README.md), excluding superseded LogSaving | 4 | 68 |
| [Spectral at 80d7eeb](spectral-80d7eeb/README.md) | 2 | 88 |
| [LogSaving and ChartSum at 70e8f69c](chart-sum-70e8f69c/README.md) | 2 | 20 |
| [ActualPair and compatible Core at 198f777f](actual-pair-198f777f/README.md) | 2 | 28 |
| Total continuation | 10 | 204 |

[aggregate.json](aggregate.json) selects the last complete inventory for
each defining module, validates all recorded stage logs, literal kernel
replay messages, original serialized inventory, source hashes and local
import closures. It is a deterministic aggregation of existing accepted
evidence, not a new Lean audit. Superseded declarations are not counted.
The only allowed transitive axioms are `propext`, `Classical.choice` and
`Quot.sound`.

The [original baseline report](baseline-c509267-report.json) was read
from `/workspace/goldbach-p3/.lake/p3-fourth-verification/report.json` in
the user-selected Workspace Compile environment and copied byte-for-byte.
No full baseline recompilation was performed.

To reproduce the receipt aggregation from the repository root:

```sh
python3 -B verification/aggregate_part3_continuation.py \
  --receipt docs/part3-distribution/continuation-20261124/proper-power-60cf3d49 \
  --receipt docs/part3-distribution/continuation-20261124/spectral-80d7eeb \
  --receipt docs/part3-distribution/continuation-20261124/chart-sum-70e8f69c \
  --receipt docs/part3-distribution/continuation-20261124/actual-pair-198f777f \
  --output .lake/p3-continuation-aggregate.json
```

The full original proper-power chart bank is now paid. The actual
full-range spectral suppliers and the remaining actual-source / medium /
prime-product assembly are documented in the
[continuation ledger](../CONTINUATION-20261124.md).
