# Curve complex formalization

Lean sources for the four original article results: contractibility of C₁ in genus two, integral acyclicity of C₁ in genus two, simple connectivity of C₁ in every genus at least two, and the genus-two hyperelliptic dictionary.

The original four theorem files are preserved byte for byte from the accepted development. Their earlier accepted proofs used Lean 4.35.0-rc3 and the classical axiom base `propext`, `Classical.choice`, and `Quot.sound`.

## Source package status

The repository starts a fresh Git history. The source closure now includes all 2,813 project and Schoenflies modules selected by the accepted runtimes, including the 36 providers previously stored outside the canonical module paths. The normal Lake import graph resolves and the entire source closure is free of `sorry` and `admit`. Original theorem source hashes and statement guards are preserved.

Intermediate import and named-axiom checks pass using the previously accepted object cache. A fresh source build, declaration pruning, proof cleanup, and final comparison remain in progress; this package does not yet claim a clean `lake build` result. Seven historical source/import aliases now have ordinary source module paths, with their proof text preserved.

`CurveComplex.lean` imports the four original theorem modules. The project pins Lean 4.35.0-rc3 and Mathlib commit `3f6737de4761ec7bf368491fe9faccc991ebd6ca`. Schoenflies source is vendored as a local Lake dependency, without its old Git history.

The portable build recipe is:

```sh
lake update
lake exe cache get
lake build
```

See [THIRD_PARTY.md](THIRD_PARTY.md) for dependency attribution. Build objects, prior histories, scratch workspaces, proof logs, and historical workflow records are excluded.
