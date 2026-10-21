import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace CollatzPrefix
open Filter

/-- Any natural-valued sequence has a subsequence that is constant or
escapes to infinity. This is the finite-gap extraction used for repair clusters. -/
theorem constant_or_divergent_subsequence (f : ℕ → ℕ) :
    ∃ g : ℕ → ℕ, StrictMono g ∧
      ((∃ c, ∀ j, f (g j) = c) ∨ Tendsto (fun j => f (g j)) atTop atTop) := by
  classical
  by_cases h : ∃ c, ∃ᶠ j in atTop, f j = c
  · obtain ⟨c, hc⟩ := h
    obtain ⟨g, hg, hgc⟩ := extraction_of_frequently_atTop hc
    exact ⟨g, hg, Or.inl ⟨c, hgc⟩⟩
  · have hf : ∀ c, (f ⁻¹' {c}).Finite := by
      intro c
      have hn : ¬ (∃ᶠ j in atTop, f j = c) := fun hc => h ⟨c, hc⟩
      rw [← Nat.cofinite_eq_atTop, frequently_cofinite_iff_infinite] at hn
      have hfset : {x | f x = c}.Finite := Set.not_infinite.mp hn
      convert hfset using 1
      ext j
      simp
    have ht : Tendsto f atTop atTop := by
      simpa only [Nat.cofinite_eq_atTop] using
        (Tendsto.cofinite_of_finite_preimage_singleton hf)
    exact ⟨id, strictMono_id, Or.inr ht⟩

/-- A finite list of gaps can be stabilized simultaneously. -/
theorem finite_constant_or_divergent_subsequence (r : ℕ) (f : Fin r → ℕ → ℕ) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ i,
      ((∃ c, ∀ j, f i (g j) = c) ∨ Tendsto (fun j => f i (g j)) atTop atTop) := by
  induction r with
  | zero => exact ⟨id, strictMono_id, fun i => Fin.elim0 i⟩
  | succ r ih =>
    obtain ⟨g, hg, hfg⟩ := ih (fun i => f i.castSucc)
    obtain ⟨h, hh, hlast⟩ := constant_or_divergent_subsequence (fun j => f (Fin.last r) (g j))
    refine ⟨g ∘ h, hg.comp hh, ?_⟩
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · exact hlast
    · rcases hfg k with ⟨c, hc⟩ | ht
      · exact Or.inl ⟨c, fun j => hc (h j)⟩
      · exact Or.inr (ht.comp hh.tendsto_atTop)

/-- Finite labels can be fixed on an infinite subsequence. -/
theorem finite_label_constant_subsequence {α : Type*} [Finite α] (f : ℕ → α) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∃ c, ∀ j, f (g j) = c := by
  classical
  have hf : ∃ c, ∃ᶠ j in atTop, f j = c := by
    by_contra h
    push Not at h
    have he : ∀ᶠ j in atTop, ∀ c, f j ≠ c := eventually_all.mpr (fun c => by simpa only [not_frequently] using h c)
    obtain ⟨j, hj⟩ := he.exists
    exact hj (f j) rfl
  obtain ⟨c, hc⟩ := hf
  obtain ⟨g, hg, hgc⟩ := extraction_of_frequently_atTop hc
  exact ⟨g, hg, c, hgc⟩

/-- Failure of a uniform additive bound supplies an arbitrarily growing
counterexample family, without a numerical search assumption. -/
theorem unbounded_excess_sequence {α : Type*} (P : α → Prop) (E : α → ℝ)
    (h : ¬ ∃ K : ℝ, ∀ x, P x → E x ≤ K) :
    ∃ x : ℕ → α, (∀ j, P (x j)) ∧ (∀ j : ℕ, (j : ℝ) < E (x j)) := by
  classical
  have hchoice : ∀ j : ℕ, ∃ x, P x ∧ (j : ℝ) < E x := by
    intro j
    by_contra he
    apply h
    refine ⟨j, ?_⟩
    intro x hx
    by_contra hn
    exact he ⟨x, hx, lt_of_not_ge hn⟩
  choose x hp he using hchoice
  exact ⟨x, hp, he⟩

/-- Growing excess must leave every bounded source set, once each such set
has a uniform excess bound. This isolates the fixed-start reduction. -/
theorem source_tendsto_of_excess (seed : ℕ → ℕ) (E : ℕ → ℝ)
    (hE : ∀ j : ℕ, (j : ℝ) < E j)
    (hbound : ∀ N : ℕ, ∃ C : ℝ, ∀ j, seed j ≤ N → E j ≤ C) :
    Tendsto seed atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  obtain ⟨C, hC⟩ := hbound N
  filter_upwards [eventually_gt_atTop (Nat.ceil C)] with j hj
  by_contra hn
  have hs : seed j ≤ N := by omega
  have hh := hC j hs
  have hjr : C < (j : ℝ) := (Nat.le_ceil C).trans_lt (by exact_mod_cast hj)
  linarith [hE j]

end CollatzPrefix
