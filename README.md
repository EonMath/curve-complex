# Curve complex formalization

Lean sources for the four original article results: contractibility of C₁ in genus two, integral acyclicity of C₁ in genus two, simple connectivity of C₁ in every genus at least two, and the genus-two hyperelliptic dictionary.

The original four theorem files are preserved byte for byte from the accepted development. Their earlier accepted proofs used Lean 4.35.0-rc3 and the classical axiom base `propext`, `Classical.choice`, and `Quot.sound`.

## Initial source snapshot

This first commit starts a fresh Git history and contains the canonical source modules selected by the accepted runtimes. Portable source-provider reconciliation and a fresh project build are still in progress; this snapshot does not claim that a clean `lake build` has passed. Required providers previously stored outside the canonical project are being added in subsequent commits.

`CurveComplex.lean` imports the four original theorem modules. The project pins Lean 4.35.0-rc3 and Mathlib commit `3f6737de4761ec7bf368491fe9faccc991ebd6ca`. Schoenflies source is vendored as a local Lake dependency, without its old Git history.

The intended build command after source reconciliation is:

```sh
lake update
lake exe cache get
lake build
```

See [THIRD_PARTY.md](THIRD_PARTY.md) for dependency attribution. Build objects, prior histories, scratch workspaces, proof logs, and historical workflow records are excluded.
