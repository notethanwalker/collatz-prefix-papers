# Pinned formal dependencies

This isolated project uses Lean `leanprover/lean4:v4.35.0-rc3`.
The independently checked entropy project remains on its original Lean 4.19.0 setup.

## Subspace and S-unit theorems

- Repository: https://github.com/rwst/Subspace-Theorems
- Author: Ralf Stephan.
- License: Apache License 2.0. The upstream copyright and license notices are retained in the dependency.
- Revision: `09835cb23557ae5ae0cf55a9c4ab9055f5d60338`.
- Source license: https://github.com/rwst/Subspace-Theorems/blob/09835cb23557ae5ae0cf55a9c4ab9055f5d60338/LICENSE
- Mathlib revision: `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`.

On 21 October 2026, a fresh checkout compiled the complete 142-module local dependency closure of
`DiophantineApproximation.SubspaceAffine` and `DiophantineApproximation.UnitEquationSeveral`,
including `DiophantineApproximation.RepetitionSubspaces`. All local modules were built from source;
only official mathlib compiled caches were used. No upstream helper, challenge, or comparator scripts
were run, and no proof source was edited. The targeted build was:

```sh
lake --no-cache --fail-fast build DiophantineApproximation.SubspaceAffine \
  DiophantineApproximation.UnitEquationSeveral DiophantineApproximation.RepetitionSubspaces
```

Stock Lean's `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound` for:

- `NumberField.exists_finset_submodule_of_integer_of_affineProd_le`
- `NumberField.finite_setOf_sum_mem_eq_one`
- `Rat.exists_finset_submodule_of_prod_mul_prod_padicNorm_le`

This establishes those imported results, not the completion of the Collatz-specific reductions.
The upstream default build and unrelated repository gates were not certified.

Both direct dependencies and every transitive Git revision are pinned in `lake-manifest.json`.
The local development setup reuses the separately built dependency checkout; no generated binary
is part of this source project. A fresh checkout must fetch these pinned dependencies and build the
required source modules using the recorded Lean version.
