# Two short Collatz preprints

**Ethan Walker · 21 October 2026**

| Paper | Read | Editable source |
| --- | --- | --- |
| An entropy bound for the maximum height of a nonrepeating Collatz orbit | [PDF](papers/entropy-height.pdf) | [LaTeX](papers/entropy-height.tex) |
| Collatz prefixes with finitely many deviations from rational periodic trajectories | [PDF](papers/bounded-deviations.pdf) | [LaTeX](papers/bounded-deviations.tex) |

Both papers include their proofs and references.

The first proves a chronological maximum-height exponent of `1.0526808586…` using an elementary finite entropy inequality. Its literature comparison distinguishes chronological maxima from uniform spatial occupation bounds.

The second bounds the length of an accelerated odd Collatz prefix with a fixed number of deep steps by `(1 + epsilon) log_2(n + 1) + O(1)`. It also treats deviations from a fixed finite rational periodic dictionary. Its proof uses the established p-adic Subspace Theorem and S-unit finiteness; the constants are ineffective.

**The entropy maximum-height theorem is now formally verified end to end in Lean.** The exact symbolic statement is [`entropy_height_liminf`](formal/EntropyHeight.lean): for an injective positive orbit of the actual shortcut map, the extended-real lower limit of `log H_M / log M` is at least `log 2 / binEntropy (log 2 / log 3)`. It does not assume the growth bound being proved. The proof and its dependencies use only standard Lean foundations, with no proof holes or custom axioms.

**The arbitrary-repair theorem in the bounded-deviations paper is not yet formally verified.** The project includes proved accelerated-map, reference-dictionary and zero-repair results, but these are not a substitute for its arbitrary-budget conclusion. See the [precise status](FORMAL_VERIFICATION.md), [Lean instructions](formal/README.md), and [dependency audit](formal/VERIFICATION_RESULTS.txt).

These are preprints, with AI assistance disclosed in each paper. They have not undergone independent human peer review. Formal verification of the entropy theorem does not establish a novelty claim, certify its bibliography or decimal approximation, or prove Collatz convergence. The second paper's proof is reconstructed from the supplied research summaries; see [provenance](PROVENANCE.md).

## Build and check

Requires Python 3 and a TeX distribution with `pdflatex`, `amsmath`, `amsthm`, `microtype`, `geometry`, and `hyperref`.

```sh
make
make check
```

The numerical checks cover constants, finite entropy inequalities, exact orbit identities, and the sharp shallow-step family. They are consistency checks, not a machine verification of the Diophantine proof.
