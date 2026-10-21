import PrefixRepairs
import CounterexampleExtraction

namespace CollatzPrefix
open Filter

variable {ι : Type*} [Fintype ι]

/-- A genuine admissible prefix equipped with a globally minimal reference
path. Minimality is with respect to all paths of the same prefix. -/
structure MinimalRepairPrefix (C : RationalPeriodicDictionary ι) (R : ℕ) where
  seed : ℕ
  length : ℕ
  path : ℕ → ι
  positive : 0 < seed
  odd : Odd seed
  admissible : Admissible C seed length
  budget : repairCount C seed path length ≤ R
  minimal : ∀ d : ℕ → ι, repairCount C seed path length ≤ repairCount C seed d length

/-- Failure of the actual uniform prefix bound yields minimally referenced
counterexamples whose excess tends to infinity. The finite cost of replacing
references is paid before choosing each member of the family. -/
theorem exists_minimal_failure_family (C : RationalPeriodicDictionary ι)
    (R : ℕ) (F : ℕ → ℝ)
    (hfail : ¬ ∃ K : ℝ, ∀ (n h : ℕ) (c : ℕ → ι),
      0 < n → Odd n → Admissible C n h → repairCount C n c h ≤ R →
        (referenceDepth C c h : ℝ) ≤ F n + K) :
    ∃ w : ℕ → MinimalRepairPrefix C R, ∀ j : ℕ,
      (j : ℝ) < (referenceDepth C (w j).path (w j).length : ℝ) - F (w j).seed := by
  classical
  push Not at hfail
  have hex : ∀ j : ℕ, ∃ w : MinimalRepairPrefix C R,
      (j : ℝ) < (referenceDepth C w.path w.length : ℝ) - F w.seed := by
    intro j
    obtain ⟨n, h, c, hn, ho, had, hr, he⟩ :=
      hfail ((j : ℝ) + ((2 * R * exponentCap C : ℕ) : ℝ))
    obtain ⟨d, hdc, hdmin⟩ := exists_minimal_repairs C n h c
    have hdr : repairCount C n d h ≤ R := hdc.trans hr
    have hcost : (repairCount C n c h + repairCount C n d h) * exponentCap C ≤
        2 * R * exponentCap C := Nat.mul_le_mul_right _ (by omega)
    have hd := referenceDepth_le_add_repairs C n h c d
    have hdrift : referenceDepth C c h ≤ referenceDepth C d h + 2 * R * exponentCap C :=
      hd.trans (Nat.add_le_add_left hcost _)
    have hdreal : (referenceDepth C c h : ℝ) ≤
        (referenceDepth C d h : ℝ) + ((2 * R * exponentCap C : ℕ) : ℝ) := by
      exact_mod_cast hdrift
    refine ⟨⟨n, h, d, hn, ho, had, hdr, hdmin⟩, ?_⟩
    change (j : ℝ) < (referenceDepth C d h : ℝ) - F n
    linarith
  choose w hw using hex
  exact ⟨w, hw⟩

/-- A finite family of linear relations has one fixed member holding along
an infinite subsequence. This requires no bound on the values of the vectors. -/
theorem finite_relation_subsequence {α : Type*} (S : Finset α)
    (P : α → ℕ → Prop) (h : ∀ j, ∃ z ∈ S, P z j) :
    ∃ z ∈ S, ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ j, P z (g j) := by
  classical
  have hc : ∀ j, ∃ z : S, P z j := by
    intro j
    obtain ⟨z, hz, hp⟩ := h j
    exact ⟨⟨z, hz⟩, hp⟩
  choose z hz using hc
  obtain ⟨g, hg, a, ha⟩ := finite_label_constant_subsequence z
  refine ⟨a, a.property, g, hg, ?_⟩
  intro j
  have hh := hz (g j)
  rw [ha j] at hh
  exact hh

/-- In an induction step every sufficiently late counterexample spends the
entire next repair budget. No separate repair-count stabilization is needed. -/
theorem failure_family_eventually_full_budget (C : RationalPeriodicDictionary ι)
    (R : ℕ) (F : ℕ → ℝ) (K : ℝ)
    (hind : ∀ (n h : ℕ) (c : ℕ → ι), 0 < n → Odd n → Admissible C n h →
      repairCount C n c h ≤ R → (referenceDepth C c h : ℝ) ≤ F n + K)
    (w : ℕ → MinimalRepairPrefix C (R + 1))
    (hw : ∀ j : ℕ, (j : ℝ) <
      (referenceDepth C (w j).path (w j).length : ℝ) - F (w j).seed) :
    ∀ᶠ j in atTop, repairCount C (w j).seed (w j).path (w j).length = R + 1 := by
  filter_upwards [eventually_gt_atTop (Nat.ceil K)] with j hj
  have hKj : K < (j : ℝ) := (Nat.le_ceil K).trans_lt (by exact_mod_cast hj)
  have hnot : ¬ repairCount C (w j).seed (w j).path (w j).length ≤ R := by
    intro hr
    have hb := hind (w j).seed (w j).length (w j).path
      (w j).positive (w j).odd (w j).admissible hr
    linarith [hw j]
  have hb := (w j).budget
  omega

end CollatzPrefix
