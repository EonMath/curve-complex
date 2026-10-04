#!/usr/bin/env python3
"""Strict Lean native snapshots and before/after comparison. Does not build sources.

snapshot --project PROJECT --entry MainTheorems --roots roots.json --out DIR
compare before/snapshot.json after/snapshot.json --allow-proof-changes manifest.json
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tomllib
from pathlib import Path

SCHEMA = "fl-native-comparator-v1"
BASE = {"propext", "Classical.choice", "Quot.sound"}


def require(value, message):
    if not value:
        raise ValueError(message)


def read(path):
    def unique_pairs(pairs):
        result = {}
        for k, v in pairs:
            require(k not in result, f"duplicate JSON key/owner: {k}")
            result[k] = v
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=unique_pairs)


def write(path, data):
    Path(path).write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


def canonical(data):
    return json.dumps(data, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()


def content_hash(data):
    return hashlib.sha256(canonical(data)).hexdigest()


def file_hash(path):
    with Path(path).open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def node_hash(payload, children):
    return content_hash(["Lean.Expr/full-native/v1", payload, children])


def project_modules(project):
    path = Path(project) / "lakefile.toml"
    require(path.is_file(), "provide --modules for a non-TOML Lake project")
    lake = tomllib.loads(path.read_text())
    sources = {Path(project)}
    for lib in lake.get("lean_lib", []):
        sources.add(Path(project) / lib.get("srcDir", "."))
    # A conservative superset: only actual imported module identities are exported.
    # Each explicit srcDir contributes its exact relative module paths.
    result = set()
    for src in sources:
        for p in src.rglob("*.lean"):
            rel = p.relative_to(src)
            if any(part.startswith(".") for part in rel.parts):
                continue
            result.add(".".join(rel.with_suffix("").parts))
    return sorted(result)


def map_expr_slots(row, hashes):
    require(isinstance(row["type"], int), "missing type DAG root")
    row["type_hash"] = hashes[row.pop("type")]
    value = row.pop("value")
    row["value_hash"] = None if value is None else hashes[value]
    row["recursor_rhs_hashes"] = [hashes[i] for i in row.pop("recursor_rhs")]
    if row["structure"]:
        for field in row["structure"]["fields"]:
            i = field.pop("autoParam")
            field["autoParam_hash"] = None if i is None else hashes[i]
    row.pop("event")
    row["dependencies"] = sorted(set(row["dependencies"]))
    row["axioms"] = sorted(set(row["axioms"]))
    require(set(row["axioms"]) <= BASE, f"unexpected axioms for {row['name']}: {row['axioms']}")
    require(row["kind"] not in {"theorem", "definition", "opaque"} or row["value_hash"] is not None,
            f"missing native value: {row['name']}")
    return row


def semantic_record(row):
    # Explicit structural fields only. Object bytes and numbering are provenance.
    return {k: row[k] for k in ["raw_name", "nominal_owner", "storage_owner", "kind", "ordered_universes",
                               "type_hash", "native", "structure", "projection", "instance", "proof_valued",
                               "recursor_rhs_hashes"]}


def instance_ranks(records):
    classes = {}
    for n, row in records.items():
        inst = row["instance"]
        if inst:
            key = content_hash([inst["keys"], inst["priority"], inst["attrKind"]])
            classes.setdefault(key, []).append((inst["synthOrder"], n))
    for entries in classes.values():
        for rank, (_, n) in enumerate(sorted(entries)):
            inst = records[n]["instance"]
            inst["synthOrder_diagnostic"] = inst.pop("synthOrder")
            inst["relative_synth_rank"] = rank


def finish_snapshot(records, roots, modules, aliases, provenance):
    require(records, "empty native census")
    require(len(roots) == len(set(roots)), "duplicate roots")
    for root in roots:
        require(root in records and records[root]["root"], f"missing root: {root}")
    for n, r in records.items():
        require(n == r["name"], "name-key disagreement")
        require(set(r["axioms"]) <= BASE, f"unexpected axioms: {n}")
    instance_ranks(records)
    for r in records.values():
        # Absolute synthesizer positions are diagnostics. Effective relative order stays strict.
        if r["instance"]:
            diagnostic = r["instance"].pop("synthOrder_diagnostic")
            r["instance_position_diagnostic"] = diagnostic
        r["contract_hash"] = content_hash(semantic_record(r))
    return dict(schema=SCHEMA, status="PASS_NATIVE_SNAPSHOT", roots=roots, records=records,
                modules=modules, export_aliases=aliases, provenance=provenance,
                strict_contract="full Expr constructors/fields; literal raw Names; native metadata; no alpha normalization",
                source_build_claim=False)


def snapshot(args):
    project = Path(args.project).resolve()
    out = Path(args.out).resolve()
    require(not out.exists(), "snapshot output must be a new directory")
    require(project != out and project not in out.parents, "snapshot output must be outside project")
    out.mkdir(parents=True)
    roots = read(args.roots)
    modules = read(args.modules) if args.modules else project_modules(project)
    overrides = read(args.storage_overrides) if args.storage_overrides else {}
    require(isinstance(roots, list) and roots, "explicit nonempty root list required")
    write(out / "config.json", dict(roots=roots, modules=modules, storage_overrides=list(overrides.items())))
    backend = Path(__file__).with_name("ComparatorBackend.lean")
    code = backend.read_text()
    backend_sha = hashlib.sha256(code.encode()).hexdigest()
    require(code.startswith("import Lean\n"), "backend header changed")
    imports = "\n".join("import " + entry for entry in args.entry)
    # Names are Lean syntax inputs, never shell inputs; restrict them to module components.
    require(all(entry and all(c.isalnum() or c in "_." for c in entry) for entry in args.entry), "invalid entry name")
    env = os.environ.copy()
    env["ELAN_TOOLCHAIN"] = (project / "lean-toolchain").read_text().strip()
    # A standalone native runner avoids evaluating run_cmd against enormous IR
    # contexts. It imports the exact compiler environment with extensions loaded.
    runner = Path(__file__).with_name("ComparatorRunner.lean.part").read_text()
    runner_sha = hashlib.sha256(runner.encode()).hexdigest()
    cache_key = content_hash(["native-exec-export-v2", backend_sha, runner_sha, env["ELAN_TOOLCHAIN"]])
    cache = out.parent / ".comparator-native" / cache_key
    cache.mkdir(parents=True, exist_ok=True)
    executable = cache / "ComparatorExecutable"
    if not (cache / "READY.json").exists():
        (cache / "ComparatorExecutable.lean").write_text(code + runner)
        with (cache / "build.log").open("w") as log:
            subprocess.run(["lean", "-c", "ComparatorExecutable.c", "ComparatorExecutable.lean"],
                           cwd=cache, env=env, stdout=log, stderr=log, check=True)
            subprocess.run(["leanc", "-O2", "-rdynamic", "-DLEAN_EXPORTING", "ComparatorExecutable.c", "-o", str(executable)],
                           cwd=cache, env=env, stdout=log, stderr=log, check=True)
        write(cache / "READY.json", {"backend_sha256": backend_sha, "runner_sha256": runner_sha,
                                    "toolchain": env["ELAN_TOOLCHAIN"], "executable_sha256": file_hash(executable)})
    ready = read(cache / "READY.json")
    require(ready["backend_sha256"] == backend_sha and ready["runner_sha256"] == runner_sha and ready["toolchain"] == env["ELAN_TOOLCHAIN"], "native backend cache identity")
    require(ready["executable_sha256"] == file_hash(executable), "native backend cache drift")
    if args.lean_path:
        project_path = args.lean_path
    else:
        project_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=project, env=env, text=True).strip()
    env["LEAN_PATH"] = project_path
    command = [str(executable), str(out / "config.json"), *args.entry]
    query = imports + "\n-- Standalone native export request; no source elaboration.\n"
    (out / "query.lean").write_text(query)
    records, module_rows, aliases, hashes = {}, {}, [], []
    complete = None
    with (out / "stderr.log").open("w") as errors, (out / "stdout.log").open("w") as log:
        proc = subprocess.Popen(command, cwd=project, env=env, stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE, stderr=errors, text=True, bufsize=1)
        proc.stdin.close()
        try:
            for line in proc.stdout:
                if not line.startswith("FL_CMP "):
                    log.write(line)
                    continue
                row = json.loads(line[7:])
                event = row["event"]
                if event == "node":
                    require(row["id"] == len(hashes), "duplicate or non-topological DAG node")
                    require(all(0 <= i < len(hashes) for i in row["children"]), "invalid DAG child")
                    hashes.append(node_hash(row["payload"], [hashes[i] for i in row["children"]]))
                    if len(hashes) % 100000 == 0:
                        write(out / "progress.json", dict(constants=len(records), nodes=len(hashes), modules=len(module_rows)))
                elif event == "constant":
                    row = map_expr_slots(row, hashes)
                    n = row["name"]
                    require(n not in records, f"duplicate owner: {n}")
                    records[n] = row
                    if len(records) % 100 == 0:
                        write(out / "progress.json", dict(constants=len(records), nodes=len(hashes)))
                elif event == "module":
                    n = row["module"]
                    require(n not in module_rows, f"duplicate module: {n}")
                    obj = Path(row["object"])
                    paths = [obj, obj.with_suffix(".olean.server"), obj.with_suffix(".olean.private")]
                    row["artifacts"] = [dict(path=str(p), resolved=str(p.resolve()), sha256=file_hash(p)) for p in paths if p.is_file()]
                    row.pop("event")
                    module_rows[n] = row
                    if len(module_rows) % 100 == 0:
                        write(out / "progress.json", dict(constants=len(records), nodes=len(hashes), modules=len(module_rows), current_module=n))
                elif event == "export_alias":
                    row.pop("event")
                    aliases.append(row)
                elif event == "complete":
                    require(complete is None, "duplicate completion marker")
                    complete = row
                else:
                    raise ValueError(f"unknown exporter event: {event}")
        except BaseException:
            proc.terminate()
            proc.wait()
            raise
        code = proc.wait()
    require(code == 0, f"Lean exporter failed; see {out}/stdout.log and stderr.log")
    require(complete and complete["constants"] == len(records) and complete["nodes"] == len(hashes), "incomplete export")
    provenance = dict(project=str(project), entries=args.entry, toolchain=env["ELAN_TOOLCHAIN"], lean_path=args.lean_path,
                      backend_sha256=backend_sha, runner_sha256=runner_sha, executable_sha256=ready["executable_sha256"], config_sha256=file_hash(out / "config.json"),
                      query_sha256=file_hash(out / "query.lean"), command=command, context_label=args.context_label,
                      node_count=len(hashes), compiler_export_exit=code)
    doc = finish_snapshot(records, roots, module_rows, aliases, provenance)
    write(out / "snapshot.json", doc)
    print(json.dumps(dict(status=doc["status"], constants=len(records), nodes=len(hashes), snapshot=str(out / "snapshot.json"))))


def validate_snapshot(doc):
    require(doc.get("schema") == SCHEMA and doc.get("status") == "PASS_NATIVE_SNAPSHOT", "invalid snapshot")
    require(isinstance(doc["records"], dict), "invalid constant registry")
    for n, r in doc["records"].items():
        require(n == r["name"], "duplicate/name-key owner disagreement")
        require(r["contract_hash"] == content_hash(semantic_record(r)), f"snapshot contract integrity: {n}")
        require(set(r["axioms"]) <= BASE, f"unexpected axioms: {n}")
    for root in doc["roots"]:
        require(root in doc["records"] and doc["records"][root]["root"], f"missing root: {root}")


def compare(before_path, after_path, manifest=None, generated_binders=None):
    a, b = read(before_path), read(after_path)
    validate_snapshot(a)
    validate_snapshot(b)
    require(a["roots"] == b["roots"], "root contract differs")
    require(a["provenance"]["toolchain"] == b["provenance"]["toolchain"], "toolchain differs")
    require(a["provenance"]["backend_sha256"] == b["provenance"]["backend_sha256"], "backend serializer differs")
    require(a["provenance"].get("runner_sha256") == b["provenance"].get("runner_sha256"), "native runner differs")
    policy = read(manifest) if manifest else {}
    allowed = set(policy.get("theorems", []))
    proof_defs = set(policy.get("proof_definitions", []))
    removed_allow = set(policy.get("removals", []))
    added_allow = set(policy.get("additions", []))
    removed = set(a["records"]) - set(b["records"])
    added = set(b["records"]) - set(a["records"])
    require(removed <= removed_allow, f"unlisted removed helpers: {sorted(removed-removed_allow)[:20]}")
    require(added <= added_allow, f"unlisted added helpers: {sorted(added-added_allow)[:20]}")
    require(not removed.intersection(a["roots"]), "removed protected root")
    for n, r in b["records"].items():
        require(not removed.intersection(r["dependencies"]), f"retained dependency on removed helper: {n}")
    # External boundaries must keep exact object contents. Project object bytes may change.
    external_a = {n: [x["sha256"] for x in r["artifacts"]] for n, r in a["modules"].items() if not r["project"]}
    external_b = {n: [x["sha256"] for x in r["artifacts"]] for n, r in b["modules"].items() if not r["project"]}
    for n in external_a.keys() | external_b.keys():
        require(external_a.get(n) == external_b.get(n), f"external boundary changed: {n}")
    generated, generated_pins = {}, {}
    if generated_binders:
        import binder_accounting
        generated, generated_pins = binder_accounting.admit(generated_binders,a,b,before_path,after_path)
    changes = []
    for n in sorted(a["records"].keys() & b["records"].keys()):
        x, y = a["records"][n], b["records"][n]
        require(x["contract_hash"] == y["contract_hash"] or n in generated, f"strict type/native/operative contract mismatch: {n}")
        require(x["axioms"] == y["axioms"], f"axiom dependency set changed: {n}")
        if x["value_hash"] != y["value_hash"] and n not in generated:
            permit = x["kind"] == "theorem" and n in allowed
            permit = permit or (n in proof_defs and x["kind"] in {"definition", "opaque"} and x["proof_valued"] and y["proof_valued"])
            require(permit, f"operative/unlisted proof body changed: {n}")
            changes.append(dict(name=n, kind=x["kind"], status="PERMITTED_PROOF_BODY_CHANGE",
                                before_hash=x["value_hash"], after_hash=y["value_hash"],
                                before_axioms=x["axioms"], after_axioms=y["axioms"]))
    gate_pins = {}
    if changes or removed or added or generated:
        require(policy.get("after_snapshot_sha256") == file_hash(after_path), "change manifest not bound to after snapshot")
        gates = policy.get("checked_gates", {})
        for name in ["compile", "scan", "axioms", "guard"]:
            g = gates.get(name, {})
            require(g.get("status") == "PASS" and g.get("path") and g.get("sha256"), f"missing checked gate: {name}")
            require(file_hash(g["path"]) == g["sha256"], f"gate receipt drift: {name}")
            gate_pins[name] = g
    return dict(status="PASS_COMPARISON_WITH_PERMITTED_CHANGES" if changes or removed or added or generated else "PASS_STRICT_NATIVE_IDENTITY",
                before_sha256=file_hash(before_path), after_sha256=file_hash(after_path),
                roots=a["roots"], compared_constants=len(a["records"].keys() & b["records"].keys()),
                permitted_proof_changes=changes, permitted_generated_binder_changes=list(generated.values()),
                generated_binder_accounting_pins=generated_pins, normal_strict_mode="FAIL_RETAINED" if generated else "PASS",
                removed_helpers=sorted(removed), added_helpers=sorted(added),
                checked_gate_receipts=gate_pins, source_build_claim=False,
                owner_changed=False, operative_definitions_strict=not any(r['kind']=='definition' for r in generated.values()),
                theorem_types_strict=not bool(generated), source_authored_types_strict=True,
                axiom_sets_unchanged=True, proof_bodies_strict=not bool(changes or generated))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="mode", required=True)
    s = sub.add_parser("snapshot")
    s.add_argument("--project", required=True)
    s.add_argument("--entry", action="append", required=True)
    s.add_argument("--roots", default=str(Path(__file__).with_name("curve_complex_roots.json")), help="JSON array of exact compiler names; default is beside the tool")
    s.add_argument("--out", required=True)
    s.add_argument("--modules", help="explicit project module names JSON; otherwise enumerate TOML srcDir paths")
    s.add_argument("--lean-path", help="explicit accepted/build overlay instead of lake env; recorded in receipt")
    s.add_argument("--context-label", default="project-entry")
    s.add_argument("--storage-overrides", help="reviewed exact name-to-storage-module mapping JSON; no renaming")
    s = sub.add_parser("compare")
    s.add_argument("before")
    s.add_argument("after")
    s.add_argument("--allow-proof-changes", help="explicit theorem/proof-definition/removal lists and four checked-gate receipts")
    s.add_argument("--out", help="comparison receipt JSON; generated outside source repo")
    s.add_argument("--allow-generated-binders", help="explicit finite sealed raw binder audit and final source/extension consumer receipt")
    args = p.parse_args()
    try:
        if args.mode == "snapshot":
            snapshot(args)
        else:
            result = compare(args.before, args.after, args.allow_proof_changes, args.allow_generated_binders)
            if args.out:
                write(args.out, result)
            print(json.dumps(result, ensure_ascii=False, indent=2))
    except (ValueError, KeyError, OSError, IndexError, subprocess.CalledProcessError) as e:
        print(json.dumps(dict(status="FAIL", error=str(e)), ensure_ascii=False), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
