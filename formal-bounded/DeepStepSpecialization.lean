import DepthBoundDefinitions

namespace CollatzPrefix

/-- The negative fixed point -1 is a one-state rational periodic dictionary. -/
def negativeFixedDictionary : RationalPeriodicDictionary Unit where
  denominator := 1
  denominator_pos := by decide
  denominator_odd := by decide
  numerator := fun _ => -1
  numerator_odd := fun _ => by decide
  next := Equiv.refl _
  exponent := fun _ => 1
  exponent_pos := fun _ => by decide
  step := fun _ => by norm_num

@[simp] theorem negativeFixedDictionary_value (i : Unit) :
    negativeFixedDictionary.value i = -1 := by
  norm_num [RationalPeriodicDictionary.value, negativeFixedDictionary]

theorem negativeFixedDictionary_injective :
    Function.Injective negativeFixedDictionary.value := fun _ _ _ => Subsingleton.elim _ _

/-- Deep divisions are counted using the exact valuation of the actual odd orbit. -/
def deepStepCount (n h : ℕ) : ℕ :=
  ((Finset.range h).filter (fun t => 2 ≤ acceleratedExponent (oddOrbit n t))).card

theorem negative_reference_admissible (n h : ℕ) : Admissible negativeFixedDictionary n h := by
  left
  intro i
  rw [negativeFixedDictionary_value]
  norm_num

theorem negative_reference_depth (h : ℕ) :
    referenceDepth negativeFixedDictionary (fun _ => ()) h = h := by
  simp [referenceDepth, negativeFixedDictionary]

theorem negative_reference_repair_count (n h : ℕ) (ho : Odd n) :
    repairCount negativeFixedDictionary n (fun _ => ()) h = deepStepCount n h := by
  unfold repairCount deepStepCount
  congr 1
  ext t
  simp only [mem_repairSet, Finset.mem_filter, Finset.mem_range]
  have hp := acceleratedExponent_pos (oddOrbit_odd ho t)
  simp only [GoodAt, negativeFixedDictionary, Equiv.refl_apply, and_true]
  omega

/-- Applying the uniform dictionary-depth bound at -1 gives exactly the
fixed-deep-step-count claim, not an abstract reference-count surrogate. -/
theorem deep_step_bound_of_dictionary_bound (R : ℕ) (ε : ℝ)
    (hb : PrefixDepthBound negativeFixedDictionary R ε) :
    ∃ K : ℝ, ∀ n h : ℕ, 0 < n → Odd n → deepStepCount n h ≤ R →
      (h : ℝ) ≤ (1 + ε) * (Real.log ((n : ℝ) + 1) / Real.log 2) + K := by
  obtain ⟨K, hK⟩ := hb
  refine ⟨K, ?_⟩
  intro n h hn ho hr
  have hrep : repairCount negativeFixedDictionary n (fun _ => ()) h ≤ R := by
    rw [negative_reference_repair_count n h ho]
    exact hr
  have hh := hK n h (fun _ => ()) hn ho (negative_reference_admissible n h) hrep
  simpa only [negative_reference_depth, repairDepthProfile] using hh

end CollatzPrefix
