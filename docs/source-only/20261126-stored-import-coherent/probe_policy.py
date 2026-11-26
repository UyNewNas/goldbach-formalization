"""Narrow an already reviewed cache preexec policy; this does not install or run it."""
import copy
from pathlib import Path
from plan_probe import BLOCKS, PARENT, POLICY_FLAGS, need, physical, sha

PROBE_SHA="914bda77fd5b9f978e271af71c3916ad575ca3ce10d1b926f0cd5d6e3782f8d3"

def narrow(original, overlay_root, probe_source):
    policy=copy.deepcopy(original)
    project=physical(Path(policy["project"]))
    overlay=physical(overlay_root)
    probe=physical(probe_source)
    need(not overlay.is_relative_to(project) and not project.is_relative_to(overlay), "overlay and project overlap")
    need(probe==project/"StoredImportProbe.lean", "unexpected single allowed source path")
    data=probe.read_bytes()
    need(sha(data)==PROBE_SHA,"unexpected import probe bytes")
    protected=set(policy["deny_exact_paths"])
    for name in (PARENT,*BLOCKS):
        stem=name.replace(".","/")
        for root in (project, overlay/"source"):
            protected.add(str(root/(stem+".lean")))
        for root in (project/".lake/build/lib/lean",overlay/"lib"):
            for ext in (".olean",".olean.private",".olean.server",".olean.hash",".ilean",".ir",".ir.sig",".trace"):
                protected.add(str(root/(stem+ext)))
        for ext in (".c",".bc",".setup.json"):
            protected.add(str(project/".lake/build/ir"/(stem+ext)))
    existing=policy["admitted_commands"]
    new=[r for r in existing if r["phase"]=="bootstrap"]
    need(new and all(r["phase"] in ("bootstrap","qualified-project") for r in existing), "unexpected baseline command phase")
    # Override only the old scope's project commands; the shared guard keeps
    # bootstrap reuse-only, same-run stock qualification and default deny.
    new.append(dict(tool="lean",phase="qualified-project",classification="EXACT_STORED_IMPORT_ONLY_PROBE",
                    argv=POLICY_FLAGS+[str(probe)],source=dict(path=str(probe),bytes=len(data),sha256=PROBE_SHA)))
    policy["admitted_commands"]=new
    policy["deny_exact_paths"]=sorted(protected)
    return policy

def verify_environment(plan_path, plan_sha256, shadow_sysroot, official_core, env):
    """Call at preexec for the admitted probe, with digest from its bound caller receipt."""
    import json
    from plan_probe import read_pinned
    plan=json.loads(read_pinned(plan_path,plan_sha256))
    need(plan["status"]=="PHYSICAL_INPUT_PLAN_ONLY_NOT_IMPORTED", "unexpected physical input status")
    need(plan["official_core_root_expected_in_dist"]==official_core, "unexpected official core location")
    need(env.get("LEAN_SYSROOT")==shadow_sysroot, "actual preexec sysroot differs")
    need(env.get("LEAN_PATH")==plan["lean_path"], "actual preexec search path differs")
    need(not env.get("LEAN_SRC_PATH"), "unnecessary Lean source path present")
    return dict(lean_path=env["LEAN_PATH"],sysroot=env["LEAN_SYSROOT"],plan_sha256=plan_sha256)
