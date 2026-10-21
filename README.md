# Two short Collatz preprints

**Ethan Walker · 21 October 2026**

| Paper | Read | Editable source |
| --- | --- | --- |
| An entropy bound for the maximum height of a nonrepeating Collatz orbit | [PDF](papers/entropy-height.pdf) | [LaTeX](papers/entropy-height.tex) |
| Collatz prefixes with finitely many deviations from rational periodic trajectories | [PDF](papers/bounded-deviations.pdf) | [LaTeX](papers/bounded-deviations.tex) |

Both papers include their proofs and references.

The first proves a chronological maximum-height exponent of `1.0526808586…` using an elementary finite entropy inequality. Its literature comparison distinguishes chronological maxima from uniform spatial occupation bounds.

The second bounds the length of an accelerated odd Collatz prefix with a fixed number of deep steps by `(1 + epsilon) log_2(n + 1) + O(1)`. It also treats deviations from a fixed finite rational periodic dictionary. Its proof uses the established p-adic Subspace Theorem and S-unit finiteness; the constants are ineffective.

**Formal verification is incomplete for both papers.** See the [verification status and acceptance criteria](FORMAL_VERIFICATION.md). The requested public release with formal certificates remains pending.

These are preprints, with AI assistance disclosed in each paper. They have not undergone independent human peer review or formal verification. Neither paper proves Collatz convergence, and neither asserts a comprehensive priority claim. The second paper's proof is reconstructed from the supplied research summaries; see [provenance](PROVENANCE.md).

## Build and check

Requires Python 3 and a TeX distribution with `pdflatex`, `amsmath`, `amsthm`, `microtype`, `geometry`, and `hyperref`.

```sh
make
make check
```

The numerical checks cover constants, finite entropy inequalities, exact orbit identities, and the sharp shallow-step family. They are consistency checks, not a machine verification of the Diophantine proof.
