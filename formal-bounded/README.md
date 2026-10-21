# Lean verification of bounded Collatz prefixes

This is the separate Lean 4.35 project for the bounded-deviations paper. The
entropy theorem remains in `../formal` on its original Lean 4.19 pins.

## Exact top-level results

- `CollatzPrefix.bounded_repair_reference_depth` in `BoundedRepairTheorem.lean`:
  for every fixed finite injectively labelled rational periodic dictionary,
  repair budget R and epsilon>0, there is one constant valid for every positive
  odd actual prefix satisfying the paper's domain condition.
- `CollatzPrefix.bounded_deep_steps_prefix_length` in the same file: for every
  R and epsilon>0, one constant bounds every positive odd prefix with at most
  R actual valuations v2(3n+1)>=2 by (1+epsilon)log2(n+1)+K.

- `CollatzPrefix.bounded_repair_prefix_length`: the full general length bound
  with coefficient `(1+epsilon)/minimumCycleMean`, whose mean is proved equal
  to the minimum of the least-period cycle averages.

`SharpShallowFamily.lean` also verifies the explicit shallow family
`n=2^(h+1)-1`, its actual orbit and exact logarithmic height, and the impossibility
of a uniform leading coefficient below 1.

These are universal statements with the constant quantified before all starts,
lengths and reference paths. The final conclusions assume neither a growth law,
a certificate, nor the bound to be proved. The induction hypothesis is used only
at a strictly smaller repair budget.

No result here proves the Collatz conjecture, allows R to grow with the prefix,
or supplies an effective numerical value for the constant. See the top-level
`FORMAL_VERIFICATION.md` for the distinction between formal verification and
literature/novelty assessment.

## Reproduction

Install the official Lean elan toolchain manager, then from this directory:

```sh
lake --no-cache exe cache get $(cat mathlib-cache-modules.txt)
lake --no-cache build
lake env lean VerificationAudit.lean > verification.log
python3 check_audit.py verification.log
```

The committed `lean-toolchain` and `lake-manifest.json` pin all dependencies.
The first command downloads **official mathlib** compiled artifacts. The second
compiles all required external Subspace-Theorems and local proof modules from
source, with Lake's third-party package-artifact cache disabled. It targets the
imported proof closure, not unrelated upstream roadmap/default targets.
No upstream auxiliary audit script, comparator executable or prebuilt third-party
proof object is needed.

`proof_modules.json` enumerates our proof modules; `VerificationAudit.lean`
prints every public theorem/lemma's transitive axioms. The audit checks only
`propext`, `Classical.choice`, and `Quot.sound` are used, and rejects source proof
holes and custom mathematical axioms. Private helpers are checked by Lean and
included transitively in the public theorem dependencies. Regenerate audit
commands after adding declarations with `python3 check_audit.py --generate`.

A kernel check certifies the formal statement. Statement correspondence to the
paper was separately inspected, including the actual valuation map, uniform
quantifiers, domain restriction, minimal-reference construction, exceptional
subspaces and exact deep-step specialization.

## Sources and attribution

The mathematical Subspace Theorem and S-unit finiteness are external results,
not discoveries of this project. Their formal proofs are imported from
[Ralf Stephan's Subspace-Theorems](https://github.com/rwst/Subspace-Theorems),
commit `09835cb23557ae5ae0cf55a9c4ab9055f5d60338`, released under Apache-2.0.
The imported source was independently rebuilt and its endpoints audited with
stock Lean. See `EXTERNAL_DEPENDENCIES.md` for precise versions and endpoints.

The Collatz-specific construction, reductions and integration formalize Ethan
Walker's AI-assisted research package. OpenAI assistance was used to write,
debug and review the formalization. A verified proof is not a comprehensive
priority claim or a substitute for independent specialist review of novelty.
