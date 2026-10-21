import PrefixRepairs
import CounterexampleExtraction

/-!
Inductive reduction for bounded-repair counterexamples: the states immediately
before and after every selected repair tend to infinity. The hypothesis is an
explicit bound for prefixes with one fewer repair, not the target theorem.
-/
namespace CollatzPrefix
open Filter
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The prefix strictly before any selected repair spends one fewer repair. -/
theorem repairCount_prefix_before_repair (C : RationalPeriodicDictionary ι)
    (n h t : ℕ) (c : ℕ → ι) (ht : t < h) (hbad : ¬ GoodAt C n c t) :
    repairCount C n c t + 1 ≤ repairCount C n c h := by
  classical
  have hnot : t ∉ repairSet C n c t := by simp [mem_repairSet]
  have hsub : insert t (repairSet C n c t) ⊆ repairSet C n c h := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (mem_repairSet C n c h j).mpr ⟨ht, hbad⟩
    · have hj' := (mem_repairSet C n c t j).mp hj
      exact (mem_repairSet C n c h j).mpr ⟨hj'.1.trans ht, hj'.2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at hc
  exact hc

/-- Splitting a reference sum at a selected index. -/
theorem referenceDepth_add (C : RationalPeriodicDictionary ι) (c : ℕ → ι) (l k : ℕ) :
    referenceDepth C c (l + k) =
      referenceDepth C c l + referenceDepth C (fun t => c (l + t)) k := by
  exact Finset.sum_range_add _ _ _

theorem referenceDepth_succ (C : RationalPeriodicDictionary ι) (c : ℕ → ι) (t : ℕ) :
    referenceDepth C c (t + 1) = referenceDepth C c t + C.exponent (c t) :=
  Finset.sum_range_succ _ _

/-- Prefix depth, one selected position, and the shifted suffix exhaust the depth. -/
theorem referenceDepth_split_at (C : RationalPeriodicDictionary ι) (c : ℕ → ι)
    {h t : ℕ} (ht : t < h) :
    referenceDepth C c h = referenceDepth C c t + C.exponent (c t) +
      referenceDepth C (fun j => c (t + 1 + j)) (h - (t + 1)) := by
  have hh : t + 1 + (h - (t + 1)) = h := by omega
  conv_lhs => rw [← hh, referenceDepth_add, referenceDepth_succ]

/-- A finite uniform cap for suffixes whose starting state is bounded. -/
def boundedStateLengthCap (C : RationalPeriodicDictionary ι) (R N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), prefixLengthCap C R n

theorem prefixLengthCap_le_boundedStateLengthCap (C : RationalPeriodicDictionary ι)
    (R : ℕ) {n N : ℕ} (hn : n ≤ N) :
    prefixLengthCap C R n ≤ boundedStateLengthCap C R N := by
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (prefixLengthCap C R i))
    (Finset.mem_range.mpr (by omega))

/-- Bounded post-repair states bound the total excess using only the prior-budget bound. -/
theorem excess_le_of_repair_successor_le (C : RationalPeriodicDictionary ι)
    (R : ℕ) (F : ℕ → ℝ) (K : ℝ)
    (hind : ∀ (n h : ℕ) (c : ℕ → ι), 0 < n → Odd n → Admissible C n h →
      repairCount C n c h ≤ R → (referenceDepth C c h : ℝ) ≤ F n + K)
    {n h t N : ℕ} (c : ℕ → ι)
    (hn : 0 < n) (hodd : Odd n) (had : Admissible C n h)
    (hr : repairCount C n c h ≤ R + 1)
    (ht : t < h) (hbad : ¬ GoodAt C n c t)
    (hstate : oddOrbit n (t + 1) ≤ N) :
    (referenceDepth C c h : ℝ) - F n ≤
      K + exponentCap C + boundedStateLengthCap C R N * exponentCap C := by
  have hpbudget := repairCount_prefix_before_repair C n h t c ht hbad
  have hprefix := hind n t c hn hodd (admissible_prefix C had ht.le) (by omega)
  have hsbudget := repairCount_suffix_after_repair C n h t c ht hbad
  have hlength := length_le_prefixLengthCap C R (fun j => c (t + 1 + j))
    (oddOrbit_pos hn _) (oddOrbit_odd hodd _)
    (admissible_suffix C had (by omega : t + 1 + (h - (t + 1)) ≤ h)) (by omega)
  have hlength' := hlength.trans (prefixLengthCap_le_boundedStateLengthCap C R hstate)
  have hsdepth := (referenceDepth_le_cap_mul C (fun j => c (t + 1 + j)) (h - (t + 1))).trans
    (Nat.mul_le_mul_right (exponentCap C) hlength')
  have hone := exponent_le_cap C (c t)
  have hsplit := referenceDepth_split_at C c ht
  have hsplitR : (referenceDepth C c h : ℝ) = (referenceDepth C c t : ℝ) +
      C.exponent (c t) + referenceDepth C (fun j => c (t + 1 + j)) (h - (t + 1)) := by
    exact_mod_cast hsplit
  have hsdepthR : (referenceDepth C (fun j => c (t + 1 + j)) (h - (t + 1)) : ℝ) ≤
      (boundedStateLengthCap C R N : ℝ) * exponentCap C := by exact_mod_cast hsdepth
  have honeR : (C.exponent (c t) : ℝ) ≤ exponentCap C := by exact_mod_cast hone
  linarith

/-- In an unbounded-excess family with `R+1` repairs, any selected repair's
successor diverges, provided the bound is already known for budget `R`. -/
theorem repair_successor_tendsto_of_excess (C : RationalPeriodicDictionary ι)
    (R : ℕ) (F : ℕ → ℝ) (K : ℝ)
    (hind : ∀ (n h : ℕ) (c : ℕ → ι), 0 < n → Odd n → Admissible C n h →
      repairCount C n c h ≤ R → (referenceDepth C c h : ℝ) ≤ F n + K)
    (seed len t : ℕ → ℕ) (c : ℕ → ℕ → ι)
    (hseed : ∀ j, 0 < seed j) (hodd : ∀ j, Odd (seed j))
    (had : ∀ j, Admissible C (seed j) (len j))
    (hr : ∀ j, repairCount C (seed j) (c j) (len j) ≤ R + 1)
    (ht : ∀ j, t j < len j) (hbad : ∀ j, ¬ GoodAt C (seed j) (c j) (t j))
    (hE : ∀ j : ℕ, (j : ℝ) < (referenceDepth C (c j) (len j) : ℝ) - F (seed j)) :
    Tendsto (fun j => oddOrbit (seed j) (t j + 1)) atTop atTop := by
  apply source_tendsto_of_excess _ _ hE
  intro N
  refine ⟨K + exponentCap C + boundedStateLengthCap C R N * exponentCap C, ?_⟩
  intro j hstate
  exact excess_le_of_repair_successor_le C R F K hind (c j) (hseed j) (hodd j)
    (had j) (hr j) (ht j) (hbad j) hstate

/-- A universal upper bound for the accelerated image. -/
theorem accelerated_le_three_mul_add_one (n : ℕ) : accelerated n ≤ 3 * n + 1 := by
  unfold accelerated
  exact Nat.div_le_self _ _

/-- Divergence after a step forces divergence before it. -/
theorem predecessor_tendsto_of_successor (seed t : ℕ → ℕ)
    (h : Tendsto (fun j => oddOrbit (seed j) (t j + 1)) atTop atTop) :
    Tendsto (fun j => oddOrbit (seed j) (t j)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  filter_upwards [h.eventually_ge_atTop (3 * N + 1)] with j hj
  have hu := accelerated_le_three_mul_add_one (oddOrbit (seed j) (t j))
  rw [← oddOrbit_succ] at hu
  omega

/-- The same reduction with the paper's direct `excess → ∞` hypothesis. -/
theorem repair_neighbors_tendsto_of_divergent_excess (C : RationalPeriodicDictionary ι)
    (R : ℕ) (F : ℕ → ℝ) (K : ℝ)
    (hind : ∀ (n h : ℕ) (c : ℕ → ι), 0 < n → Odd n → Admissible C n h →
      repairCount C n c h ≤ R → (referenceDepth C c h : ℝ) ≤ F n + K)
    (seed len t : ℕ → ℕ) (c : ℕ → ℕ → ι)
    (hseed : ∀ j, 0 < seed j) (hodd : ∀ j, Odd (seed j))
    (had : ∀ j, Admissible C (seed j) (len j))
    (hr : ∀ j, repairCount C (seed j) (c j) (len j) ≤ R + 1)
    (ht : ∀ j, t j < len j) (hbad : ∀ j, ¬ GoodAt C (seed j) (c j) (t j))
    (hE : Tendsto (fun j => (referenceDepth C (c j) (len j) : ℝ) - F (seed j))
      atTop atTop) :
    Tendsto (fun j => oddOrbit (seed j) (t j)) atTop atTop ∧
      Tendsto (fun j => oddOrbit (seed j) (t j + 1)) atTop atTop := by
  have hs : Tendsto (fun j => oddOrbit (seed j) (t j + 1)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [hE.eventually_gt_atTop
      (K + exponentCap C + boundedStateLengthCap C R N * exponentCap C)] with j hj
    by_contra hstate
    have hb := excess_le_of_repair_successor_le C R F K hind (c j) (hseed j) (hodd j)
      (had j) (hr j) (ht j) (hbad j) (by omega : oddOrbit (seed j) (t j + 1) ≤ N)
    exact hj.not_ge hb
  exact ⟨predecessor_tendsto_of_successor seed t hs, hs⟩

end CollatzPrefix
