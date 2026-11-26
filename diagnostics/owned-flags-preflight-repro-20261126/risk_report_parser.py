def parse_flags(path, modules):
    records = {kind: [] for kind in ("IMPORTS", "INVENTORY", "DECL_ISSUE", "BAD", "MODULE", "COMPLETE")}
    starts = []
    with path.open(encoding="utf-8") as stream:
        for line in stream:
            if line.startswith("P24_FLAGS_START "):
                starts.append(line.removeprefix("P24_FLAGS_START ").strip())
            for kind in records:
                prefix = "P24_FLAGS_" + kind + " "
                if line.startswith(prefix):
                    records[kind].append(json.loads(line[len(prefix):]))
                    break
    for kind, filename in (("INVENTORY", "inventories.json"), ("DECL_ISSUE", "declaration-issues.json"),
                           ("BAD", "bad-records.json"), ("MODULE", "module-counts.json")):
        write_json(OUT / filename, records[kind])
    mismatches = [row for row in records["INVENTORY"] if row.get("inventory_ok") is False]
    write_json(OUT / "inventory-mismatches.json", mismatches)
    write_json(OUT / "protocol.json", {"imports": records["IMPORTS"], "starts": starts, "complete": records["COMPLETE"]})
    require(len(records["IMPORTS"]) == 1 and isinstance(records["IMPORTS"][0], list), "Missing import list")
    imported = records["IMPORTS"][0]
    actual = [name for name in imported if name.startswith("ImbalancedChen.")]
    require(len(actual) == len(set(actual)) and set(actual) == set(modules), "Wrong project scope")
    require(starts == modules, "Incomplete module-start coverage")
    require([row["module"] for row in records["INVENTORY"]] == modules, "Incomplete inventories")
    require([row["module"] for row in records["MODULE"]] == modules, "Incomplete module scans")
    require(len(records["COMPLETE"]) == 1, "Missing complete marker")
    inv = {row["module"]: row for row in records["INVENTORY"]}
    issues = {name: [] for name in modules}
    bads = {name: [] for name in modules}
    for kind, table in (("DECL_ISSUE", issues), ("BAD", bads)):
        for row in records[kind]:
            require(row["module"] in inv, "Record outside scope")
            table[row["module"]].append(row)
    totals = Counter()
    all_checked = set()
    all_bad = set()
    for row in records["MODULE"]:
        name = row["module"]
        i = inv[name]
        ser, env = i["serialized"], i["environment"]
        union = set(ser) | set(env)
        idx = i["module_index"]
        require(type(idx) is int and 0 <= idx < len(imported) and imported[idx] == name, "Wrong module index")
        require(row["module_index"] == idx, "Module index changed")
        entries = i["header_entries"]
        data_ok = all(not e["data_is_module"] and e["import_all"] and e["has_data"] for e in entries)
        expected_ok = len(entries) == 1 and data_ok and bool(env) and sorted(env) == sorted(ser)
        require(i["legacy_data_ok"] is data_ok and i["inventory_ok"] is expected_ok
                and row["inventory_ok"] is expected_ok, "Inventory result misreported")
        require(sorted(i["serialized_only"]) == sorted(n for n in ser if n not in set(env))
                and sorted(i["environment_only"]) == sorted(n for n in env if n not in set(ser)), "Wrong inventory difference")
        checked, missing = row["checked_names"], row["missing_names"]
        require(len(checked) == len(set(checked)) and len(missing) == len(set(missing))
                and not set(checked).intersection(missing) and set(checked) | set(missing) == union,
                "Union candidates not fully classified")
        require(row["candidate_count"] == len(union) and row["checked"] == len(checked)
                and row["missing"] == len(missing), "Wrong scan counts")
        by_issue = {r["name"]: r for r in issues[name]}
        require(len(by_issue) == len(issues[name]) == row["declaration_issues"], "Duplicate/wrong issue count")
        for decl, r in by_issue.items():
            require(decl in union, "Issue outside candidate union")
            require(r["in_serialized"] is (decl in ser) and r["in_environment"] is (decl in env), "Wrong membership")
            owner = r["owner_index"]
            require(r["owner_module"] == (imported[owner] if owner is not None and 0 <= owner < len(imported) else None),
                    "Wrong actual owner module")
            require(r["owner_matches"] is (owner == idx), "Wrong owner-match flag")
            require(r["missing_constant_info"] is (decl in missing), "Wrong missing ConstantInfo flag")
            require(not r["in_serialized"] or not r["in_environment"] or not r["owner_matches"]
                    or r["missing_constant_info"], "Spurious declaration issue")
        require((set(i["serialized_only"]) | set(i["environment_only"]) | set(missing)) <= set(by_issue),
                "Unreported inventory difference or missing declaration")
        bad = bads[name]
        require(len({r["name"] for r in bad}) == len(bad) == row["bad_declarations"], "Duplicate/wrong bad count")
        for r in bad:
            require(r["name"] in checked, "Bad record was not examined")
            require(all(type(r[k]) is bool for k in ("unsafe", "partial", "axiom")), "Malformed flags")
            require(r["forbidden_axioms"] == [ax for ax in r["axioms"] if ax not in AXIOMS], "Wrong axiom classification")
            require(any(r[k] for k in ("unsafe", "partial", "axiom")) or r["forbidden_axioms"], "Spurious bad record")
            owner = r["owner_index"]
            require(r["owner_module"] == (imported[owner] if owner is not None and 0 <= owner < len(imported) else None)
                    and r["owner_matches"] is (owner == idx), "Bad record owner mismatch")
            require(r["in_serialized"] is (r["name"] in ser) and r["in_environment"] is (r["name"] in env), "Bad membership mismatch")
            all_bad.add(r["name"])
        expected_counts = {"unsafe_count": sum(r["unsafe"] for r in bad),
                           "partial_count": sum(r["partial"] for r in bad),
                           "axiom_count": sum(r["axiom"] for r in bad),
                           "forbidden_axiom_declarations": sum(bool(r["forbidden_axioms"]) for r in bad)}
        require(all(row[k] == v for k, v in expected_counts.items()), "Flag totals disagree")
        totals.update({"candidate_occurrences": len(union), "checked_occurrences": len(checked),
                       "missing_occurrences": len(missing), "bad_occurrences": len(bad),
                       "declaration_issue_occurrences": len(by_issue), "inventory_mismatch_modules": int(not expected_ok)})
        all_checked.update(checked)
    final = records["COMPLETE"][0]
    require(final["modules"] == 321 and all(final[k] == v for k, v in totals.items()), "Final coverage/count mismatch")
    require(final["all_inventory_ok"] is (totals["inventory_mismatch_modules"] == 0)
            and final["all_flags_axioms_clear"] is (totals["bad_occurrences"] == 0)
            and final["all_candidates_examined"] is (totals["missing_occurrences"] == 0), "Wrong final risk status")
    require(final["diagnostic_only"] is True and all(final[k] is False for k in
            ("full_type_audit", "independent_replay", "original_owned_accepted", "acceptance_credit")), "Acceptance boundary changed")
    return {**final, "unique_declarations_checked": len(all_checked), "unique_bad_declarations": sorted(all_bad),
            "mismatch_modules": [row["module"] for row in mismatches],
            "bad_modules": [name for name in modules if bads[name]],
            "all_requested_module_reports_complete": True}
