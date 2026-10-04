# Strict Lean comparator

Run after building the exact sources (`lake build MainTheorems`). Snapshots inspect imported compiled environments; they do not build sources or replace the compiler/scan/axiom/statement-guard gates. Keep generated outputs outside the source repository.

```sh
python tools/comparator.py snapshot --project /path/to/project \
  --entry MainTheorems --roots tools/curve_complex_roots.json --out /tmp/before
python tools/comparator.py snapshot --project /path/to/project \
  --entry MainTheorems --roots tools/curve_complex_roots.json --out /tmp/after
python tools/comparator.py compare /tmp/before/snapshot.json /tmp/after/snapshot.json
```

The project supplies `lean-toolchain` and TOML `lean_lib.srcDir` paths. For a Lean lakefile, pass `--modules modules.json`, an array of logical project module names. Each output directory must be new. The tool compiles its checked backend natively into a content-pinned cache beside the snapshot, with the project's Lean toolchain. The standalone executable loads the imported environment and its extensions directly, avoiding frontend command evaluation over huge IR contexts. It uses `lake env` for the existing compiled module search path. `--lean-path` instead selects an explicit runtime overlay and records that choice. `--context-label` labels reference/provenance contexts. Backend compilation and queries only write outside the project.

Observable import stages and declaration/module counters are flushed to `stderr.log`; content node counters are also recorded in `progress.json`. Actual native storage is indexed once per module, and alias candidate owners are indexed once per environment.

Each snapshot includes literal compiler names, nominal and actual native storage owners, complete native expression DAG hashes, ordered universes, native declaration metadata, recursor RHS, structure/projection/instance metadata, complete project proof and definition values, dependency names, compiler axiom sets, and imported object pins. Node identifiers and declaration enumeration do not affect content hashes. Expressions preserve binder names/info, metadata, let flags, literals, projections, and all children; ordinary Lean `BEq Expr` is never used. External modules are pinned by exact `.olean`/server/private artifact bytes. Compiler-generated private names receive no renaming or alpha normalization.

Filename aliases sometimes store a declaration outside its nominal compiler owner. The backend accepts only a unique storage candidate with an exact complete active/native payload match; ambiguity fails. `--storage-overrides exact-map.json` permits a reviewed name-to-storage-module mapping, still requiring exact active/native equality. It does not rename declarations.

Default comparison requires strict native identity. A retained definition's body must match even if its name and all four theorem types match. Every project's axiom set is contained in `propext`, `Classical.choice`, `Quot.sound`; each retained declaration's set must also remain exactly unchanged. Root omission, unexpected axioms, duplicate owners, missing native values, or placeholders fail.

For intended proof rewrites and unused helper deletions, supply `--allow-proof-changes manifest.json`:

```json
{
  "theorems": ["Exact.TheoremName"],
  "proof_definitions": [],
  "removals": ["Exact.UnusedHelper"],
  "additions": [],
  "after_snapshot_sha256": "SHA256_OF_AFTER_SNAPSHOT_FILE",
  "checked_gates": {
    "compile": {"status":"PASS", "path":"/absolute/compile-receipt.json", "sha256":"..."},
    "scan": {"status":"PASS", "path":"/absolute/scan-receipt.json", "sha256":"..."},
    "axioms": {"status":"PASS", "path":"/absolute/axiom-receipt.json", "sha256":"..."},
    "guard": {"status":"PASS", "path":"/absolute/guard-receipt.json", "sha256":"..."}
  }
}
```

The caller runs the four gates on the exact after sources and supplies their hashed receipts. The comparator verifies receipt pins and the snapshot binding; it does not independently execute those gates. Types, nonproof values, native metadata, and axiom sets stay strict. Only listed theorem values may differ. Proof-valued `def`/`opaque` values require their own explicit list and compiler `isProp` classification; a definition returning `Prop` is data and cannot receive this waiver. Reports list distinct before/after proof hashes and checked receipts, and explicitly mark proof bodies as changed. Helpers require individual removal/addition names, roots cannot disappear, and no retained native dependency may refer to a removed helper.

Pure source relocation preserving module identities needs no rename map. Regenerated private names require separate exact reviewed tooling; this command conservatively rejects them. New external imports and changes in instance ordering may require a separately reviewed boundary policy; this version fails rather than silently accepting them.

The release keeps two distinct comparison contexts. The historical accepted-object snapshot records independently selected compiled objects; its strict comparison with the freshly built delivery remains a reported mismatch. It is not evidence that the relocated sources were freshly rebuilt, and the tool does not normalize away its private-name, binder, provider, or object-byte differences.

Source-edit validation uses bounded witnesses: the original versions of the
five mathematically edited modules are freshly compiled against the same pinned
dependency objects as the delivered versions, with the audited C0 heartbeat
setting common to both. Their complete owned declaration slices are compared.
Source-authored theorem types, source-authored computational definitions, and
axiom sets are preserved; the report explicitly accounts for the listed
deletions, intended proof rewrites, and binder labels in the listed
compiler-generated helpers. Whole-project source/compiled-reference and
applicable registration audits bound outside consumers. This is a source-delta
comparison; it does not claim a fully re-elaborated historical repository or
global native identity of all unchanged proof objects. The delivered sources
separately passed the complete 2,814-module fresh build and ordinary `lake
build`.

For the exact finite compiler-generated binder-label accounting, use
`--allow-generated-binders scope.json`; see
[FINITE_BINDER_INTERFACE.md](FINITE_BINDER_INTERFACE.md) for its pinned schema,
lineage and outside-consumer requirements. Ordinary comparison remains strict.
The interface permits no global binder, private-name, or provider
normalization.
