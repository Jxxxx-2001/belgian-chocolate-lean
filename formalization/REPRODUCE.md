# Reproduce the Lean proof

Install [Elan](https://github.com/leanprover/elan) and Git. From the repository root, run

```sh
cd formalization
lake build
lake env lean -DwarningAsError=true BelgianChocolateThresholdAudit.lean
```

The first command run through Lake resolves the Lean toolchain and the dependencies from the pinned files. The Mathlib cache can shorten dependency builds. Run `lake exe cache get Mathlib` before `lake build` to use it.

| Dependency | Pinned version |
| --- | --- |
| Lean | [`v4.36.0-rc2`](https://github.com/leanprover/lean4/releases/tag/v4.36.0-rc2) |
| Mathlib | [`1b1ccf4b088b32fa3f23f2de1127433254a81e1e`](https://github.com/leanprover-community/mathlib4/tree/1b1ccf4b088b32fa3f23f2de1127433254a81e1e) |
| Tau Ceti | [`ed6c0aa3acc0a3cb56901dc406167cdbad593f59`](https://github.com/TauCetiProject/TauCeti/tree/ed6c0aa3acc0a3cb56901dc406167cdbad593f59) |

[`lake-manifest.json`](lake-manifest.json) records the transitive dependency commits. On Windows, a short checkout path helps keep dependency paths within Windows limits. If needed, set `LEAN_NUM_THREADS` to `1` in the shell before building.

## Expected audit

The [audit file](BelgianChocolateThresholdAudit.lean) checks the type of `BelgianChocolate.belgian_chocolate_threshold` and lists the axioms used by 31 declarations. For the main theorem, the expected output is `[propext, Classical.choice, Quot.sound]`.

| Result | Lean statement |
| --- | --- |
| Original strictly stable polynomial controller problem | [`ControlWitness.Feasible`](ControllerFeasible.lean#L11) |
| Unique balanced slit | [`existsUnique_balanced_slit`](BalancedSlitRoot.lean#L101) |
| Global disk comparison | [`disk_threshold_of_certified_witness`](MarkedCompetitorComparison.lean#L236) |
| Finite-order controller threshold | [`controller_threshold_of_candidate`](ControllerCandidateThreshold.lean#L115) |
| Main theorem | [`BelgianChocolate.belgian_chocolate_threshold`](BelgianChocolateThreshold.lean#L89) |
