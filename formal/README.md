# Lean verification: partial coverage

**Neither paper's main asymptotic theorem has complete formal verification.** A green component build does not certify the entire paper.

This project pins Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. `FormalComponents.lean` contains 34 proved theorems; `VerificationAudit.lean` prints every theorem's axiom dependencies. No Collatz-specific axiom, `sorry`, `admit`, or `native_decide` is used.

## Checked coverage

- The actual shortcut map, parity-word residue correspondence, and bounded-state word injectivity.
- A finite Bernoulli packing inequality, its degenerate endpoint, and exact chronological window corrections.
- `positive_chronological_entropy`: the finite entropy inequality for the actual positive Collatz orbit with distinct starts below `2^r`. The real logarithms and binary entropy are both in natural units; dividing by `log 2` gives the base-two form. The size condition is explicit; the paper chooses `r` from the maximum.
- Exact one-step and finite-orbit logarithmic growth identities; the reciprocal bound on each correction term.
- The rational normalized defect increment, matching-step invariance, and repair ratio identities.
- The zero-deep-step prefix identity, divisibility, and coefficient-one bound. This does not prove the arbitrary fixed repair-budget theorem.

## Reproduce

Install elan from the official Lean distribution, then run:

```sh
cd formal
lake update
lake exe cache get Mathlib.Analysis.SpecialFunctions.BinaryEntropy Mathlib.Tactic Mathlib.Data.Nat.ModEq
lake build
lake env lean VerificationAudit.lean > verification.log
python3 check_audit.py verification.log
```

The expected dependency set is confined to Lean's standard `propext`, `Classical.choice`, and `Quot.sound` foundations. See `VERIFICATION_RESULTS.txt` for the run recorded with this revision and the repository workflow for fresh checks.

## Remaining work

The entropy paper still needs the distinct-state harmonic sum bound, the asymptotic limit/subsequence argument, and the final maximum-height exponent statement. The bounded-deviations paper still needs the valuation and cluster reductions, three-place estimate, formal Diophantine inputs, exceptional-subspace elimination, and final arbitrary-budget theorem. See the root `FORMAL_VERIFICATION.md` for details.

## Runtime compatibility used in this session

The task environment exposes `/proc/self/exe`, while Lean 4.19 queries `/proc/<pid>/exe`. `runtime-compat/readlink-self.c` supplies a narrow fallback only for that process's own executable-path lookup. It does not modify Lean's kernel or proof terms. Ordinary Linux CI does not need it. To reproduce in an affected environment:

```sh
gcc -shared -fPIC -o runtime-compat/readlink-self.so runtime-compat/readlink-self.c -ldl
export LD_PRELOAD="$PWD/runtime-compat/readlink-self.so"
export TAR_OPTIONS=--no-same-owner
```
