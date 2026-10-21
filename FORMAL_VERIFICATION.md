# Formal verification status: INCOMPLETE

Neither paper currently has an end-to-end proof-assistant verification. Full formal verification of both papers is a requirement requested by the author and remains open.

There is now a pinned, successfully checked Lean project containing 34 component theorems, with no proof holes or theorem-shaped axioms. See [formal/README.md](formal/README.md) for exact coverage and reproduction, and [the recorded dependency audit](formal/VERIFICATION_RESULTS.txt). The Python checks remain numerical consistency checks. A successful component audit does not establish either main asymptotic theorem.

## Entropy paper

The required formal target is the maximum-height liminf theorem for the actual shortcut Collatz orbit, not a numerical approximation or an implication assuming the main entropy bound.

Completed components:

1. Actual shortcut map, parity-residue correspondence, and sampled-word injectivity.
2. A finite Bernoulli product-mass argument giving the entropy inequality, including its degenerate endpoint. This is an alternative formal derivation of the written entropy argument.
3. Exact chronological boundary correction and `positive_chronological_entropy` for distinct starts below `2^r`, in natural-log units.
4. Exact logarithmic orbit-growth identity and the pointwise reciprocal bound for correction terms.

Outstanding:

1. The bound on the reciprocal sum over arbitrary distinct positive orbit values and its harmonic estimate.
2. The subsequence/liminf argument and final exact symbolic maximum-height exponent.
3. An explicit formal link from the paper's chosen maximum/ceiling definition of `r` to the bounded-state hypothesis used by the verified finite inequality.

## Bounded-deviations paper

The target must use the actual accelerated odd map, actual valuations, an explicitly defined periodic dictionary, and the stated domain restriction.

Checked components are the exact rational defect increment, matching-step invariance, repair ratio, and the zero-deep-step prefix identity/divisibility/size bound. They do not establish the arbitrary-budget theorem.

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

## Verified run on 21 October 2026

Lean 4.19.0 and pinned mathlib were installed. The executable-discovery issue was resolved with the narrow `/proc/self/exe` compatibility fallback documented in `formal/README.md`. The Lean kernel and theorem terms were not modified.

`lake build`, a fresh `lake env lean VerificationAudit.lean`, and `python3 check_audit.py verification.log` passed for all 34 listed component theorems. Their axiom dependencies are confined to the standard `propext`, `Classical.choice`, and `Quot.sound` foundations.

A search of the pinned mathlib sources did not locate the needed Subspace Theorem or S-unit finiteness formalizations. These deep inputs, and the Collatz-specific reductions using them, have not been formalized here. No axiom asserting them was added.
