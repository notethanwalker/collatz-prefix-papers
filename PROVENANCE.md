# Provenance and review scope

These papers were prepared from the user-supplied `Collatz_PrePaper_Research_Package_2026-10-21.zip`, especially the entropy and fixed-event/dictionary summaries in `chapters/legacy_routes.md`, and public sources named in the bibliographies. No personal memory or Library material was consulted.

The supplied package contained summaries rather than the complete original fixed-event and dictionary manuscripts. The second paper therefore supplies a reconstructed argument, including the cluster reduction, three-place estimate, and elimination of exceptional subspaces. It should be evaluated on that written argument rather than treated as a transcription of an independently reviewed proof.

OpenAI ChatGPT/Codex assisted with proof reconstruction, literature comparison, drafting, typesetting, and consistency checks. The author name follows the supplied research package. No human referee approval or proof-assistant certification of either full main theorem is claimed. The checked component coverage is documented separately in `formal/README.md`.

The literature comparisons identify differences from specific cited results. They do not certify global novelty or priority. The papers deliberately omit the package's unrelated claims and machine constructions.

## End-to-end Lean verification (21 October 2026)

Both main theorem developments now include kernel-checked formal proofs. The
Collatz-specific formalizations were developed with OpenAI assistance. Deep
Subspace/S-unit formal proofs are credited to Ralf Stephan and imported from
the pinned Apache-2.0 Subspace-Theorems library. Original mathematical sources
and exact dependency details are in formal-bounded/EXTERNAL_DEPENDENCIES.md and
formal-bounded/BOUNDED_PROOF_MAP.md. Formal verification does not establish
novelty or replace independent specialist review of priority.
