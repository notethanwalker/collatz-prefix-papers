import FailureFamilies

namespace CollatzPrefix
open Filter

variable {ι : Type*} [Fintype ι]

/-- The target reference-depth profile for a fixed positive epsilon. -/
noncomputable def repairDepthProfile (ε : ℝ) (n : ℕ) : ℝ :=
  (1 + ε) * (Real.log ((n : ℝ) + 1) / Real.log 2)

/-- The exact uniform arbitrary-budget depth claim, including the actual
orbit, actual repair count and the paper's domain alternatives. -/
def PrefixDepthBound (C : RationalPeriodicDictionary ι) (R : ℕ) (ε : ℝ) : Prop :=
  ∃ K : ℝ, ∀ (n h : ℕ) (c : ℕ → ι),
    0 < n → Odd n → Admissible C n h → repairCount C n c h ≤ R →
      (referenceDepth C c h : ℝ) ≤ repairDepthProfile ε n + K

/-- Base case of the repair-budget induction, with an explicit uniform constant. -/
theorem prefixDepthBound_zero (C : RationalPeriodicDictionary ι)
    (ε : ℝ) (hε : 0 ≤ ε) : PrefixDepthBound C 0 ε := by
  refine ⟨Real.log C.scale / Real.log 2, ?_⟩
  intro n h c hn ho had hr
  have hg : ∀ t < h, GoodAt C n c t :=
    (repairCount_zero_iff C n h c).mp (Nat.eq_zero_of_le_zero hr)
  have hb := periodic_no_repair_log_bound C (oddOrbit n) c h
    (fun t _ => oddOrbit_odd ho t)
    (fun t ht => admissible_value_lt C hn had ht (c t))
    (fun t _ => oddOrbit_succ n t)
    (fun t ht => (hg t ht).2) (fun t ht => (hg t ht).1)
  have hnlog : 0 ≤ Real.log ((n : ℝ) + 1) / Real.log 2 := by
    apply div_nonneg
    · exact Real.log_nonneg (by have hh : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  simp only [oddOrbit_zero] at hb
  change (referenceDepth C c h : ℝ) ≤ _ at hb
  unfold repairDepthProfile
  nlinarith [mul_nonneg hε hnlog]

/-- A failed induction step can be reduced to a sequence of minimal paths
spending exactly the new repair budget and with linearly growing excess. -/
theorem exists_full_budget_failure_family (C : RationalPeriodicDictionary ι)
    (R : ℕ) (ε : ℝ) (hind : PrefixDepthBound C R ε)
    (hfail : ¬ PrefixDepthBound C (R + 1) ε) :
    ∃ w : ℕ → MinimalRepairPrefix C (R + 1),
      (∀ j, repairCount C (w j).seed (w j).path (w j).length = R + 1) ∧
      (∀ j : ℕ, (j : ℝ) <
        (referenceDepth C (w j).path (w j).length : ℝ) - repairDepthProfile ε (w j).seed) := by
  obtain ⟨K, hK⟩ := hind
  obtain ⟨w, hw⟩ := exists_minimal_failure_family C (R + 1) (repairDepthProfile ε) hfail
  have he := failure_family_eventually_full_budget C R (repairDepthProfile ε) K hK w hw
  obtain ⟨g, hg, hge⟩ := extraction_of_eventually_atTop he
  refine ⟨w ∘ g, hge, ?_⟩
  intro j
  have hj : j ≤ g j := hg.le_apply
  have hjr : (j : ℝ) ≤ g j := by exact_mod_cast hj
  exact hjr.trans_lt (hw (g j))

end CollatzPrefix
