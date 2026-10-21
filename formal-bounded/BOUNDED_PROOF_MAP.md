# Bounded-deviations proof map

This document maps the paper `papers/bounded-deviations.tex` to the formal
proofs. The main depth theorem is an actual accelerated-orbit theorem, not a
conditional statement about symbolic trajectories or an assumed product bound.

## Public endpoints

- `CollatzPrefix.bounded_repair_reference_depth` proves `PrefixDepthBound C R ε`
  for every fixed natural repair budget `R`, every `ε > 0`, and every injectively
  labeled `RationalPeriodicDictionary C`.
- `CollatzPrefix.bounded_deep_steps_prefix_length` specializes to the negative
  fixed point `−1`. It counts actual steps with
  `2 ≤ acceleratedExponent (oddOrbit n t)` and proves
  `h ≤ (1+ε) * log(n+1)/log(2) + K`, uniformly over positive odd starts and
  prefixes having at most `R` such steps.

`PrefixDepthBound` explicitly quantifies a single real constant `K` before all
starts, lengths, and reference paths. It does not fix the prefix length, bound
the exponents at repairs, or assume an orbit escapes to infinity.

## Length bound with the exact cycle mean

`PeriodicMeanBound.lean` defines `C.minimumCycleMean` for a nonempty finite
label type and proves it is positive. The theorem
`cycleMeanAt_eq_minimalPeriod_average` identifies the common-period averages
used in the definition with the averages over the actual minimal cycles.
Thus this is the paper's `β`, not an arbitrary lower bound such as `1`.

`minimum_mean_mul_length_le_of_repairs` proves
`β*h ≤ referenceDepth + periodicMeanError C R` for any reference path with at
most `R` repairs. The potential identity telescopes on genuine periodic steps;
the finitely many repair jumps contribute a constant depending only on `C,R`.
`length_log_bound_of_depth_bound` then gives the required coefficient
`(1+ε)/β` by applying the already proved depth bound. The final public wrapper
is supplied in `BoundedRepairTheorem.lean` now integrated.

## Mathematical data and domain

`BoundedDeviations.lean` defines the actual valuation
`acceleratedExponent n = padicValNat 2 (3*n+1)` and actual map
`accelerated n = (3*n+1)/2^(acceleratedExponent n)`.
`PrefixRepairs.lean` defines their iterates `oddOrbit`, actual cumulative depth,
reference depth, the repair set, and its cardinality.

A `RationalPeriodicDictionary` stores a positive odd common denominator, odd
integer numerators, positive exponents, and a permutation of the finite labels.
Its exact affine step equation is part of the data. The proved theorems
`value_step`, `value_valuation`, and `exponent_eq_valuation` establish that these
are the rational periodic trajectories with the exact required valuation,
not an arbitrary assignment of exponents. Injectivity of `C.value` represents
the paper's set of distinct reference rationals.

`Admissible C n h` is the disjunction:

1. every reference value is negative; or
2. for every prefix state and every reference value,
   `2 * abs(reference) + 2 ≤ state`.

For integer states the second condition is equivalent to the paper's
`ceil(2 * max abs(reference)) + 2` threshold. The finite denominator encoding
and infinite reference functions are representations of the paper's finite
rational dictionary and finite reference paths, respectively; only path
positions through the specified endpoint are used.

## Complete induction chain

1. **Exact valuations and the zero-repair case.**
   `periodic_no_repair_valuation` derives the valuation drop along every good
   step, retaining one factor of two at the odd endpoint.
   `periodic_no_repair_log_bound` and `prefixDepthBound_zero` give the base case.

2. **Bounded starts and repairs.**
   `length_le_prefixLengthCap` proves a finite length bound for every fixed
   positive odd start and every fixed repair budget. Its recursion enumerates
   the finitely many possible first-repair locations; it is not a termination
   assumption about Collatz orbits.
   `referenceDepth_le_add_repairs` bounds the cost of changing references.

3. **Actual failure families and minimal references.**
   `exists_minimal_failure_family` constructs globally repair-minimal actual
   prefixes from failure of a uniform bound. `exists_full_budget_failure_family`
   uses the smaller-budget induction hypothesis to force exactly `R+1` repairs.
   `stabilize_failure_family` sorts the repair positions, stabilizes the finitely
   many reference labels, and extracts the fixed-width cluster partition.

4. **Divergence is proved, not assumed.**
   `repair_neighbors_tendsto_of_divergent_excess` shows that both states next
   to each selected repair tend to infinity in a failure family. A bounded
   successor would leave a smaller-budget prefix and a uniformly bounded-start
   suffix, contradicting the diverging excess.
   `actual_sorted_repairs_normalized_tendsto` then proves all normalized
   repair snapshots tend to one, using the exact quotient identity.

5. **Zero clusters cannot survive minimality.**
   `zero_cluster_replacement` proves endpoint-preserving replacement by an exact
   reference path. `SpliceRepairs.lean` proves this removes an actual repair
   without adding boundary repairs. Therefore
   `minimal_repairs_cluster_increment_ne_zero` gives a nonzero increment in
   every cluster of the minimal reference path.

6. **Actual integer vectors and the three-place estimate.**
   `integerSnapshot_cast` proves
   `X_t = D * 3^H * normalizedDefect_t` after rational casting.
   `integerSnapshot_two_norm` and `integerSnapshot_three_norm_le` prove the
   local norm estimates from the actual integer factorization.
   `good_gap_valuation_cover` proves the valuation covering inequality.
   `normalizedDefect_cluster_bound` proves the real increment bound.
   `actual_cluster_three_place_fixed_width_bound` constructs the exceptional
   interval union, bounds its cardinality by the fixed total cluster width,
   and derives the entire product estimate.

7. **Subspace Theorem with all input inequalities discharged.**
   `actual_cluster_eventually_subspace_small` combines the actual product and
   height estimates with diverging excess and produces a positive exponent
   satisfying the Subspace inequality eventually.
   `cluster_three_place_relations` applies the checked external theorem at
   the places infinity, 2 and 3, with consecutive-difference forms at infinity
   and coordinate forms at the finite places.
   `actual_snapshot_increment_relation` extracts one fixed nonzero relation
   along a subsequence, proves its coefficient sum is zero from the normalized
   limits, and derives a nonzero tail-coefficient relation on the increments.

8. **S-unit elimination with the actual repair expansion.**
   `RepairUnitExpansion.lean` telescopes the actual normalized defect across
   each cluster and expands every repair into its two rational-coefficient
   powers-of-2-and-3 terms. Zero coefficients are removed using their finite
   support, rather than assumed absent.
   `RepairClusterAssignment.lean` proves cluster assignment, exact time-interval
   membership, and divergence of every cross-cluster time separation.
   `no_separated_actual_cluster_relation` applies checked S-unit finiteness,
   forcing each weighted cluster increment to vanish. One nonzero tail
   coefficient and the minimality result give the contradiction.

9. **Outer induction.**
   `stabilized_failure_family_impossible` assembles all of steps 3–8 for actual
   stabilized failure data. `bounded_repair_reference_depth` applies it in
   ordinary induction on the repair budget. The induction hypothesis is used
   only at the smaller budget. No family-impossibility statement is postulated.

## Verification and trust boundary

The full depth endpoint, deep-step endpoint, family contradiction, actual
Subspace smallness, and actual relation extraction have been checked by stock
Lean 4.35.0-rc3. Their reported axiom dependencies are only:

- `propext`
- `Classical.choice`
- `Quot.sound`

There are no `sorry` proofs, custom Diophantine axioms, opaque assumed target
statements, or `native_decide` proof shortcuts in this development. See
`EXTERNAL_DEPENDENCIES.md` for the pinned external Subspace/S-unit source and
its verification scope. Kernel checking establishes derivability from the
stated definitions and standard Lean foundations; it is not a substitute for
reviewing whether those definitions represent the intended mathematics.

## Intellectual credit and original sources

The Collatz-specific finite-prefix argument is Ethan Walker's paper. The
formal development above reconstructs and checks that argument and its
reductions; it does not claim a new Subspace Theorem or a new S-unit theorem.

The imported formal Diophantine proofs are due to **Ralf Stephan**, in
[Subspace-Theorems](https://github.com/rwst/Subspace-Theorems), pinned at
[`09835cb23557ae5ae0cf55a9c4ab9055f5d60338`](https://github.com/rwst/Subspace-Theorems/tree/09835cb23557ae5ae0cf55a9c4ab9055f5d60338).
The separate dependency audit checked its full 142-module local closure from
source with stock Lean. This project retains its Apache-2.0 license and
attribution, and imports the results rather than presenting them as original
Collatz-project proofs.

The mathematical sources cited by the paper for the two Diophantine inputs are:

- Y. Bilu, *The many faces of the Subspace Theorem*, Astérisque 317 (2008),
  1–38, especially Theorem 2.3:
  [arXiv:0907.2098](https://arxiv.org/abs/0907.2098).
- J.-H. Evertse, H. P. Schlickewei, and W. M. Schmidt, *Linear equations in
  variables which lie in a multiplicative group*, Annals of Mathematics 155
  (2002), 807–836, especially Theorem 1.1:
  [arXiv:math/0409604](https://arxiv.org/abs/math/0409604).

The external library provides its own complete formal theorem chain and source
references. The paper's original citations are mathematical attribution, not
unverified Lean axioms.
