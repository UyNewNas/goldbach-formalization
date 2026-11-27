#!/usr/bin/env python3
"""Stock leanchecker and the original complete-owned template for fresh outputs.

This consumes explicit new normal receipts. It never creates historical audit
records, modifies an original verifier, or represents this evidence as R19.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys

import prepare_halfopen as p
import run_scoped_normal as n

NORMAL_DRIVER_SHA = "eb5537499e396ac28e04520e5a2948aefdad361f731d02bfc32fe9fdfb10b93d"


def run(args):
    root = args.root.resolve(strict=True)
    out = args.out_dir.absolute()
    p.require(out.is_relative_to(root) and not out.exists() and not out.is_symlink(),
              "Output must be a new directory inside the isolated repo")
    p.read_regular(Path(n.__file__), NORMAL_DRIVER_SHA)
    p.read_regular(Path(p.__file__), n.PREPARER_SHA)
    plan = p.build_manifest(root)
    _, original = p.original_helpers(root)
    boundary = n.ExecutionBoundary(root, args.snapshot or root / (p.RESUMED + "p2-round14-context/EXTERNAL_SNAPSHOT.json.xz"), plan)
    fresh = {}
    if args.chronology_normal:
        p.require(args.chronology_normal_sha256 is not None, "Chronology normal receipt SHA required")
        prior = n.load_normal(args.chronology_normal, args.chronology_normal_sha256, root, plan, boundary)
        p.require(prior["module"] == p.CHRONOLOGY, "Wrong prior fresh owner")
        fresh[p.CHRONOLOGY] = prior
    normal = n.load_normal(args.normal_receipt, args.normal_sha256, root, plan, boundary, fresh)
    target = normal["module"]
    fresh[target] = normal
    p.require(target != p.TARGET or p.CHRONOLOGY in fresh, "HalfOpen requires its fresh Chronology normal receipt")
    template_path = root / "verification/part2/winner9_private_audit_template.lean"
    template_bytes = p.read_regular(template_path, p.HELPERS[template_path.name])
    template = template_bytes.decode()
    p.require(template.count(original.TEMPLATE_TARGET) == 2, "Original template target count differs")
    env = boundary.environment()
    driver_sha = p.sha(p.read_regular(Path(__file__)))

    def frozen():
        p.read_regular(Path(n.__file__), NORMAL_DRIVER_SHA)
        p.read_regular(Path(__file__), driver_sha)
        return dict(**n.freeze(root, plan, target, fresh, boundary, include_target=True),
                    audit_driver_sha256=driver_sha, original_template_sha256=p.sha(template_bytes))

    receipt = dict(schema="p25-fresh-scoped-replay-owned-v1", **p.CREDIT, module=target,
                   fresh_stock_replay_passed=False, fresh_complete_owned_audit_passed=False,
                   normal_receipt=dict(path=str(args.normal_receipt), sha256=args.normal_sha256),
                   source_sha256=normal["source_sha256"], object_sha256=normal["object_sha256"],
                   fresh_normal_signature=normal["fresh_signature"], runtime=boundary.binding,
                   audit_driver_sha256=driver_sha, normal_driver_sha256=NORMAL_DRIVER_SHA,
                   original_template_sha256=p.sha(template_bytes))
    p.publish_new(out / "INPUT_BINDING.json", p.encoded(receipt))
    try:
        before = frozen()
        receipt["input_snapshot"] = before
        replay_command = [boundary.runtime["leanchecker"], "--verbose", target]
        if args.replay_receipt:
            p.require(args.replay_sha256 is not None, "Existing fresh replay receipt SHA required")
            replay = json.loads(p.read_regular(args.replay_receipt, args.replay_sha256))
            p.require(replay["schema"] == "p25-fresh-scoped-replay-stage-v1"
                      and replay["module"] == target and replay["fresh_stock_replay_passed"] is True
                      and replay["input_snapshot"] == before and replay["inputs_unchanged"] is True
                      and replay["process"]["command"] == replay_command and replay["process"]["exit_code"] == 0,
                      "Fresh replay evidence does not bind this exact current context")
            p.read_regular(root / replay["process"]["log"], replay["process"]["log_sha256"])
            receipt["replay"] = dict(replay, reused_fresh_receipt=str(args.replay_receipt),
                                     reused_fresh_receipt_sha256=args.replay_sha256)
        else:
            replay = dict(schema="p25-fresh-scoped-replay-stage-v1", **p.CREDIT, module=target,
                          input_snapshot=before, fresh_stock_replay_passed=False)
            print("SCOPED_STOCK_REPLAY", target, flush=True)
            replay["process"] = original.run_process(replay_command, out / "replay.log", root, env)
            after = frozen()
            replay["inputs_unchanged"] = after == before
            replay["fresh_stock_replay_passed"] = replay["process"]["exit_code"] == 0 and after == before
            p.publish_new(out / "REPLAY_RESULT.json", p.encoded(replay))
            receipt["replay"] = replay
        p.require(receipt["replay"]["fresh_stock_replay_passed"], "Stock independent replay failed or inputs drifted")
        receipt["fresh_stock_replay_passed"] = True
        if args.through == "replay":
            receipt["status"] = "FRESH_SCOPED_STOCK_REPLAY_PASSED"
            return 0
        source = out / "Audit.lean"
        source_bytes = template.replace(original.TEMPLATE_TARGET, target).encode()
        p.publish_new(source, source_bytes)
        command = [boundary.runtime["lean"], *n.STRICT_FLAGS, str(source.relative_to(root))]
        print("SCOPED_COMPLETE_OWNED_AUDIT", target, flush=True)
        owned = dict(schema="p25-fresh-scoped-owned-stage-v1", **p.CREDIT, module=target,
                     input_snapshot=before, source=str(source.relative_to(root)),
                     source_sha256=p.sha(source_bytes), original_template_sha256=p.sha(template_bytes),
                     fresh_complete_owned_audit_passed=False)
        try:
            owned["process"] = original.run_process(command, out / "owned.log", root, env)
            after = frozen()
            owned["inputs_unchanged"] = after == before and p.read_regular(source) == source_bytes
            p.require(owned["process"]["exit_code"] == 0, "Complete-owned Lean audit failed")
            p.require(owned["inputs_unchanged"], "Inputs changed during complete-owned audit")
            parsed = original.parse_audit(out / "owned.log", target, n.module_closure(plan, target))
            declaration_bytes = p.encoded(parsed["declarations"])
            p.publish_new(out / "OWNED_DECLARATIONS.json", declaration_bytes)
            fulltypes = "\n\n".join(
                row["name"] + "\n" + row["type"] + "\naxioms: " + ", ".join(row["axioms"])
                for row in parsed["declarations"]
            ).encode()
            p.publish_new(out / "OWNED_FULL_TYPES.txt", fulltypes)
            owned.update(fresh_complete_owned_audit_passed=True,
                         declaration_count=parsed["declaration_count"], inventory=parsed["inventory"],
                         imports=parsed["imports"], axiom_counts=parsed["axiom_counts"],
                         declarations_sha256=p.sha(declaration_bytes), full_types_sha256=p.sha(fulltypes))
        except Exception as error:
            owned["error"] = str(error)
            raise
        finally:
            p.publish_new(out / "OWNED_RESULT.json", p.encoded(owned))
            receipt["owned"] = owned
        receipt.update(fresh_complete_owned_audit_passed=True,
                       status="FRESH_SCOPED_STOCK_REPLAY_AND_COMPLETE_OWNED_PASSED")
    except Exception as error:
        receipt.update(status="FRESH_SCOPED_REPLAY_OWNED_INCOMPLETE", error=str(error))
        raise
    finally:
        p.publish_new(out / "AUDIT_RESULT.json", p.encoded(receipt))
        print(json.dumps(dict(status=receipt.get("status", "INCOMPLETE"), module=target,
                              fresh_stock_replay_passed=receipt["fresh_stock_replay_passed"],
                              fresh_complete_owned_audit_passed=receipt["fresh_complete_owned_audit_passed"],
                              result=str(out / "AUDIT_RESULT.json"), R19_accepted=False, P2_5_proved=False)))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=p.ROOT)
    parser.add_argument("--snapshot", type=Path)
    parser.add_argument("--normal-receipt", type=Path, required=True)
    parser.add_argument("--normal-sha256", required=True)
    parser.add_argument("--chronology-normal", type=Path)
    parser.add_argument("--chronology-normal-sha256")
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--through", choices=("replay", "owned"), default="owned")
    parser.add_argument("--replay-receipt", type=Path)
    parser.add_argument("--replay-sha256")
    return run(parser.parse_args())


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print("SCOPED_AUDIT_REFUSED " + str(error), file=sys.stderr)
        sys.exit(2)
