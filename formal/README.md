# Lean 4.19: full entropy theorem and original components

The entropy paper's **main symbolic asymptotic theorem is verified end to end**.
The bounded-deviations paper's complete proof is in the separate
[Lean 4.35 project](../formal-bounded/README.md); the older components here
remain available without changing this project's toolchain.
See the [exact coverage](../FORMAL_VERIFICATION.md).

Pinned toolchain: Lean 4.19.0, mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

## Proof modules

- `FormalComponents.lean`: original finite entropy, orbit identities and rational identities.
- `CorrectionDecay.lean`: correction terms and their means tend to zero along an injective orbit.
- `HeightWindow.lean`: actual chronological maximum and the paper's ceiling window.
- `EntropyHeight.lean`: full `entropy_height_liminf` theorem and eventual-exponent equivalence.
- `BoundedDeviations.lean`: accelerated map, periodic-reference valuations and zero-repair bounds.

No `sorry`, `admit`, `native_decide`, or custom mathematical axioms are used.
Every theorem's checked dependency set is restricted to `propext`,
`Classical.choice`, and `Quot.sound`.

## Reproduce

Install Lean via its official elan distribution, then run:

```sh
cd formal
lake update
lake exe cache get Mathlib.Analysis.SpecialFunctions.BinaryEntropy Mathlib.Tactic Mathlib.Data.Nat.ModEq Mathlib.Analysis.Asymptotics.SpecificAsymptotics Mathlib.Order.Filter.Cofinite Mathlib.Algebra.Order.Floor.Semiring Mathlib.Data.EReal.Basic Mathlib.Order.LiminfLimsup Mathlib.NumberTheory.Padics.PadicVal.Basic
lake build
lake env lean VerificationAudit.lean > verification.log
python3 check_audit.py verification.log
```

The committed audit commands must cover every theorem in all five modules.
When adding a theorem, regenerate them with `python3 check_audit.py --generate`,
then rebuild and rerun the audit. The script's source scan is an extra guardrail;
Lean's kernel checking and transitive axiom inspection are the decisive checks.
The independent semantic review must still confirm that theorem statements
match the intended mathematical claims.

## Recorded verification

See `VERIFICATION_RESULTS.txt` and the GitHub workflow for checked results.
The current verification used unmodified standard Lean without a runtime shim.
The historical `runtime-compat/readlink-self.c` is retained for environments
where Lean's executable-path lookup requires it; it is not part of the proof or
required for ordinary Linux CI.
