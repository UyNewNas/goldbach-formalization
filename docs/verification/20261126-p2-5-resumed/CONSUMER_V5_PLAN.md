# Cell00 consumer v5: disk-space recovery

Prepare a fresh attempt005 using the unchanged five consumer sources, 40 accepted dependencies and all v4 proof/source/object/receipt/gate predicates. Actual consumer attempt004 failed with ENOSPC before any normal, replay or audit gate. Its complete receipt and exception log remain evidence of a failure; no failed target object is imported and no accepted target gate is repeated.

1. Check the actual failed004 receipt identity, exact disk error, five unaccepted owners, empty stage dictionaries and preserved accepted006 prerequisite.
2. Keep v4 and every accepted/failed historical artifact unchanged. Bind failed004 receipt/exception/source/context identities in v5.
3. Check at least 1 GiB free before creating the fresh output; account for the actual 40 dependency copy sizes plus 256 MiB working headroom. Recheck the full copy budget immediately before the first dependency-copy loop, after the long context validation. Recheck the 256 MiB floor before each owner directory and each fresh compiler gate. Do not infer current capacity from a historical inventory.
4. Run the local accepted006 artifact suite plus actual failed004/space negative checks. Confirm every v4 top-level helper and every nested gate/object/audit helper remains AST-identical.
5. Freeze v5 for independent review and root publication. No Lean, cloud job or storage mutation is performed by this agent. Resume Cell01 only after actual Cell00 consumer success.

P3 currently reports 2,370,244,608 bytes free after an environment change. All actions made to inspect it were read-only. No sparse omission is needed or authorized by this driver.
