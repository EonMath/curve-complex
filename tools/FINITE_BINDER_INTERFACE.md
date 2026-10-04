# Optional finite binder accounting

Ordinary comparison stays strict. This interface is only for an explicitly authorized, individually named compiler-generated family whose raw changes are independently audited. It does not normalize expressions, types, or definitions.

`binder_accounting.py` accepts caller-supplied immutable evidence paths; it has no required historical workspace path. Its raw DAG format records exact native Expr constructor arrays and declaration type/value roots. The adapter hashes that data using the same strict serializer contract as ordinary snapshots. A scope binds individual names, before/after source hashes, sealed raw DAGs, compiler/parser command parentage, and native matcher/splitter lineage. Every field except the observed raw hygienic binder Name must match. Splitter values stay literally exact.

```sh
python tools/binder_accounting.py --authorization route.json \
  --before-dag before-native-dag.json --after-dag after-native-dag.json \
  --lineage compiler-parser-lineage.json --roots tools/curve_complex_roots.json \
  --out /tmp/raw-binder-audit.json
```

For extended parser/native lineage, also supply `--supplement-seal bounded-handoff-seal.json`. The handoff must hash-bind the route, its source, and all supplied lineage inputs. Parentage is checked through actual parsed command ownership plus native matcher registration/splitter-head metadata; prefixes or absent source ranges alone cannot admit a helper. Source-authored and protected declarations are excluded from the scope. The audit is qualified evidence only and never final release admission.

After the complete after-source snapshot and full source/extension reference census, create a policy:

```json
{
  "groups": [
    {
      "raw_audit": {"path":"/absolute/raw-binder-audit.json", "sha256":"..."},
      "source_consumer_receipt": {"path":"/absolute/final-source-consumers.json", "sha256":"..."}
    }
  ]
}
```

One group can be supplied without the outer `groups` array. Multiple groups must have disjoint exact helper names. The source consumer receipt must contain:

```json
{
  "status":"PASS",
  "outside_consumers":[],
  "before_snapshot_sha256":"...",
  "after_snapshot_sha256":"...",
  "exact_names":["Exact.Generated.Name"],
  "exact_family":["Exact.Parent", "Exact.Generated.Name"],
  "source_before_sha256":"...",
  "source_after_sha256":"...",
  "checked_source_spellings":true,
  "checked_applicable_extensions":true
}
```

The external audit must check actual source-language identifier references and applicable extension consumers on the exact final source/config state. The comparator verifies its pins and bindings, then independently checks every supplied before/after first-party native dependency against the exact helper family. It rejects outside consumers, changed raw payload hashes, extra names, changed native fields, and stale evidence. Source-reference and extension audit execution is a caller gate, just as the four compiler/scan/axiom/statement-guard receipts are caller gates; a JSON flag alone must never be described as executing that audit.

```sh
python tools/comparator.py compare /tmp/before/snapshot.json /tmp/after/snapshot.json \
  --allow-proof-changes release-change-manifest.json \
  --allow-generated-binders finite-binder-policy.json --out /tmp/comparison.json
```

The release change manifest still requires all four actual checked gates and binds the exact after snapshot. The parent theorem proof change is listed separately. Reports retain `normal_strict_mode: FAIL_RETAINED`, record every raw binder field and before/after type/value hash, and classify helpers as `PERMITTED_COMPILER_GENERATED_BINDER_RENUMBERING`. They set literal type/definition identity flags false when applicable; this exception is distinct from `PERMITTED_PROOF_BODY_CHANGE`. Diagnostic extension counts, such as lint logs, are not claimed equal by this tool.

Current adapters validate two explicit pinned compiler/parser lineage schemas used by this release. Other schemas are rejected until reviewed; no generic prefix or alpha-equality fallback exists. Tests and synthetic gate/census receipts remain outside the source project and never authorize release changes.
