# Two short Collatz preprints

**Ethan Walker · 21 October 2026**

| Paper | Read | Editable source |
| --- | --- | --- |
| An entropy bound for the maximum height of a nonrepeating Collatz orbit | [PDF](papers/entropy-height.pdf) | [LaTeX](papers/entropy-height.tex) |
| Collatz prefixes with finitely many deviations from rational periodic trajectories | [PDF](papers/bounded-deviations.pdf) | [LaTeX](papers/bounded-deviations.tex) |

Both papers include their proofs and references.

The first proves a chronological maximum-height exponent of `1.0526808586…` using an elementary finite entropy inequality. Its literature comparison distinguishes chronological maxima from uniform spatial occupation bounds.

The second bounds the length of an accelerated odd Collatz prefix with a fixed number of deep steps by `(1 + epsilon) log_2(n + 1) + O(1)`. It also treats deviations from a fixed finite rational periodic dictionary. Its proof uses the established p-adic Subspace Theorem and S-unit finiteness; the constants are ineffective.

**Both papers' main theorems are now formally verified end to end in Lean.**

- [Entropy proof](formal/EntropyHeight.lean): the actual maximum-height lower-limit theorem, with its exact symbolic constant.
- [Bounded-prefix proofs](formal-bounded/BoundedRepairTheorem.lean): the fixed-repair reference-depth theorem, the exact cycle-mean length bound, and the actual deep-step-count corollary.

Both projects audit all public theorem dependencies and use only standard Lean foundations, with no proof holes or custom mathematical axioms. See the [precise verification scope](FORMAL_VERIFICATION.md), [entropy instructions](formal/README.md), [bounded-proof instructions](formal-bounded/README.md), and [external theorem credits](formal-bounded/EXTERNAL_DEPENDENCIES.md).

These are preprints, with AI assistance disclosed in each paper. They have not undergone independent human peer review. Formal verification of the entropy theorem does not establish a novelty claim, certify its bibliography or decimal approximation, or prove Collatz convergence. The written proofs were reconstructed from the supplied research summaries; their formal statements are now checked. See [provenance](PROVENANCE.md).

## Build and check

Requires Python 3 and a TeX distribution with `pdflatex`, `amsmath`, `amsthm`, `microtype`, `geometry`, and `hyperref`.

```sh
make
make check
```

The numerical checks cover constants, finite entropy inequalities, exact orbit identities, and the sharp shallow-step family. They are consistency checks, not a machine verification of the Diophantine proof.
