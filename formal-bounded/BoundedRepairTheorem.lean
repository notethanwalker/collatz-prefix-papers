import DepthBoundDefinitions
import FamilyContradiction
import DeepStepSpecialization
import PeriodicMeanBound

/-!
# Uniform bounds for fixed repair budgets

These are the unconditional top-level conclusions for the actual accelerated
Collatz map. Deep Diophantine results are imported from a checked library, not
introduced as axioms. The induction hypothesis is used only for a smaller
repair budget.
-/

namespace CollatzPrefix

/-- The full fixed-budget reference-depth theorem for an injectively labeled
finite rational periodic dictionary under the paper's domain alternatives. -/
theorem bounded_repair_reference_depth {ι : Type*} [Fintype ι]
    (C : RationalPeriodicDictionary ι) (hinj : Function.Injective C.value)
    (R : ℕ) (ε : ℝ) (hε : 0 < ε) : PrefixDepthBound C R ε := by
  induction R with
  | zero => exact prefixDepthBound_zero C ε hε.le
  | succ R ih =>
    by_contra hfail
    obtain ⟨w, hcount, hexcess⟩ := exists_full_budget_failure_family C R ε ih hfail
    obtain ⟨g, hg, D, hD⟩ := stabilize_failure_family C R (repairDepthProfile ε) w hcount hexcess
    exact stabilized_failure_family_impossible C hinj R ε hε ih D

/-- For each fixed deep-step budget, every positive odd accelerated prefix
has length at most `(1+ε) log₂(n+1)` plus a uniform constant. Deep steps are
counted by the actual valuation, not by a symbolic surrogate. -/
theorem bounded_deep_steps_prefix_length (R : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ n h : ℕ, 0 < n → Odd n → deepStepCount n h ≤ R →
      (h : ℝ) ≤ (1 + ε) * (Real.log ((n : ℝ) + 1) / Real.log 2) + K := by
  exact deep_step_bound_of_dictionary_bound R ε
    (bounded_repair_reference_depth negativeFixedDictionary
      negativeFixedDictionary_injective R ε hε)

/-- The general length conclusion uses the actual minimum cycle mean of
the fixed dictionary, not merely the lower estimate that each depth is one. -/
theorem bounded_repair_prefix_length {ι : Type*} [Fintype ι] [Nonempty ι]
    (C : RationalPeriodicDictionary ι) (hinj : Function.Injective C.value)
    (R : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ (n h : ℕ) (c : ℕ → ι),
      0 < n → Odd n → Admissible C n h → repairCount C n c h ≤ R →
        (h : ℝ) ≤ ((1 + ε) / C.minimumCycleMean) *
          (Real.log ((n : ℝ) + 1) / Real.log 2) + K := by
  obtain ⟨K, hK⟩ := bounded_repair_reference_depth C hinj R ε hε
  refine ⟨(K + periodicMeanError C R) / C.minimumCycleMean, ?_⟩
  intro n h c hn ho had hr
  exact length_log_bound_of_depth_bound C R n h c ε K hr (hK n h c hn ho had hr)

end CollatzPrefix
