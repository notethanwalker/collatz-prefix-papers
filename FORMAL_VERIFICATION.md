# Formal verification: both papers' main theorems verified

The exact symbolic main theorems of both papers are now proved end to end in
Lean, including their actual Collatz dynamics, uniform quantifiers and limiting
arguments. Their final theorem dependencies contain only `propext`,
`Classical.choice`, and `Quot.sound`. No custom Diophantine axiom, assumed target
statement, proof hole or native-evaluation axiom is used.

Two pinned projects keep the already verified entropy setup unchanged.

## Entropy maximum height

Project: [`formal/`](formal/README.md), Lean 4.19.0.
Endpoint: `CollatzPrefix.entropy_height_liminf` in
[`EntropyHeight.lean`](formal/EntropyHeight.lean).

For a positive starting integer whose actual shortcut Collatz orbit is
injective, the extended-real lower limit of `log H_M / log M` is at least
`log 2 / binEntropy (log 2 / log 3)`, exactly the paper's `1/h_2(log_3 2)`.
`H_M` is the maximum over exactly the first M states. Infinite lower limits are
allowed. A separate equivalence proves the usual eventual-lower-exponent form.

The complete chain includes parity-residue injectivity, finite entropy packing,
chronological boundary corrections, exact growth, correction decay, the actual
maximum/ceiling window and the asymptotic contradiction. The formal proof uses
qualitative Cesàro decay in place of the written proof's stronger harmonic rate;
this does not weaken the conclusion.

## Fixed repair budgets and deep steps

Project: [`formal-bounded/`](formal-bounded/README.md), Lean 4.35.0-rc3.
Endpoints in [`BoundedRepairTheorem.lean`](formal-bounded/BoundedRepairTheorem.lean):

- `bounded_repair_reference_depth`: for fixed dictionary C, repair budget R and
  epsilon>0, one constant bounds the reference depth of every admissible actual
  positive odd prefix by `(1+epsilon)log_2(n+1)+K`.
- `bounded_repair_prefix_length`: the full general length bound, with coefficient
  `(1+epsilon)/beta`. `beta` is formally identified with the minimum genuine
  least-period cycle mean, not replaced by the weaker lower bound 1.
- `bounded_deep_steps_prefix_length`: the exact negative-fixed-point
  specialization, counting actual valuations `v_2(3n+1)>=2` rather than a
  symbolic surrogate.

The constant is existentially quantified **before** all sources, lengths and
reference paths. The paper's negative-reference/high-floor domain restriction
is retained. The proof discharges the actual-map, minimal-repair, fixed-start,
subsequence, clustering, valuation-cover, three-place-product, Subspace and
S-unit elimination obligations. Induction uses only the strictly smaller repair
budget. No hypothetical failure-family certificate is assumed by the final
conclusions. See the [proof map](formal-bounded/BOUNDED_PROOF_MAP.md).

The ancillary sharpness paragraph is also formalized in
[`SharpShallowFamily.lean`](formal-bounded/SharpShallowFamily.lean): the exact
family `n=2^(h+1)-1` has h shallow steps, and no uniform leading coefficient
below 1 can hold.

### Deep inputs and credit

The p-adic Subspace and S-unit results are imported from
[Ralf Stephan's Subspace-Theorems](https://github.com/rwst/Subspace-Theorems),
pinned to `09835cb23557ae5ae0cf55a9c4ab9055f5d60338`, with mathlib pinned to
`5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`. All 142 required local external
modules were independently compiled from source; endpoint audits use stock
Lean, not the upstream custom audit scripts. Only official mathlib caches are
used. The dependency's Apache-2.0 notices remain in its source. See
[dependency details](formal-bounded/EXTERNAL_DEPENDENCIES.md).

These deep mathematical theorems and their formalizations are not discoveries
of this Collatz project. Original mathematical citations and intellectual
attribution are preserved in the papers and proof map.

## What verification does and does not establish

- The checked conclusions follow from their explicit definitions and standard
  Lean foundations. Separate semantic review inspected correspondence to the
  paper statements, not merely successful compilation.
- Every public local theorem/lemma is listed in the respective axiom audit.
  Private helpers are kernel-checked and included transitively.
- This does not prove Collatz convergence, allow a growing repair budget, give
  effective constants, establish a comprehensive novelty/priority claim, or
  independently verify every bibliographic or rounded numerical statement.
- AI-assisted formal proof development and semantic review are disclosed. The
  papers have not undergone independent human peer review.

## Reproduction

Each project has its own committed toolchain, dependency manifest, aggregate
build target, theorem-coverage checker and recorded dependency log. Follow its
README. The GitHub workflows rebuild and audit the exact committed sources.
A green build must include the final endpoints; merely checking finite
components would not meet this repository's completion criterion.
