# Formal verification status: INCOMPLETE

Neither paper currently has an end-to-end proof-assistant verification. The written proofs and the Python consistency checks must not be described as formal certificates. Full formal verification of both papers is a publication requirement requested by the author and remains open.

## Entropy paper

The required formal target is the maximum-height liminf theorem for the actual shortcut Collatz orbit, not a numerical approximation or an implication assuming the main entropy bound.

Outstanding obligations:

1. Define the orbit and prove the parity-word residue correspondence.
2. Prove injectivity of the sampled parity-window map on distinct bounded states.
3. Develop the finite probability space on chronological positions; prove its joint entropy and coordinate-window boundary estimates.
4. Apply formal entropy subadditivity, binary entropy concavity, and monotonicity to prove the finite theorem.
5. Prove the exact logarithmic growth identity and harmonic error bound for distinct positive integers.
6. Formalize the subsequence/liminf argument, linking the entropy constant to the exact symbolic expression. Decimal approximations are secondary.

## Bounded-deviations paper

The target must use the actual accelerated odd map, actual valuations, an explicitly defined periodic dictionary, and the stated domain restriction.

Outstanding obligations:

1. Rational cycle denominator properties; positivity and uniform ratio estimates.
2. Valuation bound for good runs; finite branching and induction over repairs.
3. Minimal-repair replacement and bounded difference in reference depth.
4. Subsequences, cluster extraction, and the zero-cluster replacement lemma.
5. Integrality of the vector, all three local estimates, and the resulting height inequality.
6. Subspace extraction; limiting coefficient relation; S-unit decomposition and elimination of every exceptional subspace.
7. Translation from reference depth to length and the specialization to the negative fixed point.

The p-adic Subspace Theorem and nondegenerate S-unit finiteness are deep external inputs cited precisely in the paper. If introduced as assumptions rather than proved/imported from a checked library, the output must be labelled **conditional formal verification**, with those assumptions visible in the theorem's dependency audit. Assuming a Collatz-specific intermediate claim does not constitute verification of that claim.

## Acceptance criteria

- A pinned, reproducible proof-assistant project with the full target statements.
- All proof obligations discharged, with no `sorry`, `admit`, or hidden theorem-shaped axioms.
- A checked list of axioms/dependencies, separating logical foundations from any explicitly assumed external mathematical theorems.
- Successful checker output and a reproducible CI command.
- The PDFs and README accurately state the achieved level of verification.

## Environment attempt on 21 October 2026

Lean 4.19.0 was downloaded from the official distribution, and mathlib tag v4.19.0 was fetched. Invoking the downloaded Lean executable returned `error: failed to locate application`; Lake reported it could not detect its installation configuration. No Lean theorem was successfully checked in this session. These setup attempts are not evidence for either proof.
