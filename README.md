# Curve complex formalization

Start with [MainTheorems.lean](MainTheorems.lean). This single public entry imports the four original article results: genus-two C₁ contractibility, genus-two integral acyclicity, C₁ simple connectivity in every genus at least two, and the genus-two hyperelliptic dictionary.

The necessary proof sources are grouped under `curve-complex/`. The existing mathematical namespaces retain foundations, topology, hyperbolic geometry, and surface classification. Previously loose proof files are grouped into curve topology, covering spaces, hyperbolic geometry, surface geometry, and the main theorem proofs. Source module names, definitions, theorem statements, and proof text are preserved.

## Build

Lean is pinned to 4.35.0-rc3 and Mathlib to `3f6737de4761ec7bf368491fe9faccc991ebd6ca`. Schoenflies is included as a local source dependency.

```sh
lake update
lake exe cache get
lake build
```

The normal Lake import graph resolves. The source closure is free of `sorry` and `admit`; the four original theorem files retain their accepted source hashes and statement guards. Intermediate import and named-axiom checks pass with the accepted object cache, using exactly `propext`, `Classical.choice`, and `Quot.sound`. A fresh full source build, declaration cleanup, and final comparison remain in progress.

See [THIRD_PARTY.md](THIRD_PARTY.md) for attribution. Build objects and historical proof-workflow artifacts are excluded from Git.
