# Formal verification status

## Entropy-height paper: main theorem VERIFIED

The full exact symbolic maximum-height theorem is proved in
[`formal/EntropyHeight.lean`](formal/EntropyHeight.lean), declaration
`CollatzPrefix.entropy_height_liminf`.

Its assumptions are a positive natural starting value and injectivity of the
actual shortcut Collatz orbit. Its conclusion is the extended-real lower limit

`liminf (log H_M / log M) >= log 2 / binEntropy (log 2 / log 3)`.

Here `H_M` is exactly the maximum over the first `M` states. `binEntropy` uses
natural logarithms, so the constant is precisely the paper's
`1 / h_2(log_3 2)`. The statement allows the lower limit to be positive infinity.
An explicitly proved equivalence also gives the usual formulation: every
strictly smaller real exponent is eventually below the logarithmic height ratio.

### Complete dependency path

1. `FormalComponents.lean`: the actual map, parity/residue injectivity,
   finite Bernoulli entropy packing, chronological window boundary correction,
   exact orbit growth and correction upper bound.
2. `CorrectionDecay.lean`: injectivity implies escape from every finite set;
   reciprocal corrections tend to zero and their Cesàro mean tends to zero.
   This suffices for the main theorem; an explicit harmonic rate is unnecessary.
3. `HeightWindow.lean`: actual prefix maximum, exact natural ceiling window,
   bounded-state implication and logarithmic window upper bound.
4. `EntropyHeight.lean`: bias lower bound, asymptotic contradiction, eventual
   lower exponents and the exact extended-real lower-limit theorem.

No growth-rate, random-parity, finite-entropy, or desired-result hypothesis is
assumed in the final theorem. The dependency audit admits only standard Lean
foundations (`propext`, `Classical.choice`, `Quot.sound`).

This verifies the mathematical statement, not its novelty, literature priority,
rounded decimal evaluation, or every sentence of the paper. The proof uses a
qualitative Cesàro argument in place of the exposition's quantitative harmonic
estimate. This does not weaken the final conclusion.

## Bounded-deviations paper: arbitrary-repair theorem INCOMPLETE

The original rational defect identities and zero-deep-step bound are checked.
`BoundedDeviations.lean` further develops the actual valuation-defined accelerated
map, rational periodic dictionaries, good-run valuation loss and the zero-repair
case. Consult its exact theorem signatures: these do not prove the arbitrary
fixed repair-budget theorem.

Still required for the full paper:

- Minimal-repair replacement, finite branching, induction and subsequences.
- Cluster extraction, zero-cluster replacement and all local estimates.
- The three-place product inequality and the appropriate Subspace Theorem.
- Nondegenerate S-unit finiteness and exceptional-subspace elimination.
- The final arbitrary-budget depth/length conclusions and specialization.

The deep inputs are absent from the pinned mathlib used here. An external
Subspace/S-unit formalization is under evaluation; it is not imported or relied
upon in this revision. Absence from this project is not a claim that no external
formalization exists. No axiom asserting those theorems or a Collatz-specific
replacement has been added.

## Reproduction and acceptance

See [formal/README.md](formal/README.md) for pinned toolchain and commands.
`VerificationAudit.lean` covers every theorem/lemma in all five proof modules;
`check_audit.py` checks coverage, forbidden proof-hole constructs and the
Lean-produced axiom dependencies. A green aggregate build certifies only the
statements actually present, not the incomplete arbitrary-repair theorem.
