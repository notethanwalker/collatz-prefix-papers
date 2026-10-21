import IntegerSnapshots
import SortedRepairs
import RepairAsymptotics
import RepairDivergence

/-!
# Actual repair ratios and normalized snapshots

The limits in this file concern the actual accelerated Collatz orbit, rather
than a freely chosen sequence of ratios. Admissibility supplies every nonzero
denominator needed for the exact rational identity and for cancellation.
-/

namespace CollatzPrefix
open Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

/-- Admissibility makes the actual normalized defect strictly positive. -/
theorem normalizedDefect_pos (C : RationalPeriodicDictionary ι) {n H t : ℕ}
    (c : ℕ → ι) (hn : 0 < n) (had : Admissible C n H) (ht : t ≤ H) :
    0 < normalizedDefect C n c t := by
  unfold normalizedDefect
  exact mul_pos (by positivity) (sub_pos.mpr (admissible_value_lt C hn had ht _))

/-- The exact quotient at any actual orbit step, including repair steps. -/
theorem normalizedDefect_step_ratio (C : RationalPeriodicDictionary ι)
    {n H t : ℕ} (c : ℕ → ι) (hn : 0 < n)
    (had : Admissible C n H) (ht : t < H) :
    normalizedDefect C n c (t + 1) / normalizedDefect C n c t =
      (1 + 1 / (3 * (oddOrbit n t : ℚ))) *
      (1 - C.value (c (t + 1)) / (oddOrbit n (t + 1) : ℚ)) /
      (1 - C.value (c t) / (oddOrbit n t : ℚ)) := by
  have h := defect_ratio (oddOrbit n t : ℚ) (oddOrbit n (t + 1) : ℚ)
    (C.value (c t)) (C.value (c (t + 1)))
    (acceleratedExponent (oddOrbit n t)) (actualDepth n t) t
    (by exact_mod_cast ne_of_gt (oddOrbit_pos hn t))
    (by exact_mod_cast ne_of_gt (oddOrbit_pos hn (t + 1)))
    (ne_of_gt (sub_pos.mpr (admissible_value_lt C hn had ht.le _)))
    (oddOrbit_affineStep n t).symm
  simpa [normalizedDefect, actualDepth, Finset.sum_range_succ] using h

/-- For fixed labels, divergence of the actual states on both sides of a
repair forces its actual normalized-defect quotient to tend to one. -/
theorem actual_repair_ratio_tendsto_one (C : RationalPeriodicDictionary ι)
    (seed len t : ℕ → ℕ) (c : ℕ → ℕ → ι) (before after : ι)
    (hseed : ∀ j, 0 < seed j) (had : ∀ j, Admissible C (seed j) (len j))
    (ht : ∀ j, t j < len j)
    (hbefore : ∀ j, c j (t j) = before)
    (hafter : ∀ j, c j (t j + 1) = after)
    (hleft : Tendsto (fun j => oddOrbit (seed j) (t j)) atTop atTop)
    (hright : Tendsto (fun j => oddOrbit (seed j) (t j + 1)) atTop atTop) :
    Tendsto (fun j => (normalizedDefect C (seed j) (c j) (t j + 1) : ℝ) /
      (normalizedDefect C (seed j) (c j) (t j) : ℝ)) atTop (𝓝 1) := by
  have h := repair_ratio_tendsto_one
    (fun j => (oddOrbit (seed j) (t j) : ℝ))
    (fun j => (oddOrbit (seed j) (t j + 1) : ℝ))
    (C.value before : ℝ) (C.value after : ℝ)
    (tendsto_natCast_atTop_atTop.comp hleft)
    (tendsto_natCast_atTop_atTop.comp hright)
  apply h.congr
  intro j
  have he := normalizedDefect_step_ratio C (c j) (hseed j) (had j) (ht j)
  rw [hbefore j, hafter j] at he
  have hc := congrArg (fun q : ℚ => (q : ℝ)) he
  push_cast at hc
  exact hc.symm

/-- The prior-budget bound and unbounded excess supply precisely the actual
neighbor divergence needed by the quotient identity. -/
theorem actual_repair_ratio_tendsto_of_excess (C : RationalPeriodicDictionary ι)
    (R : ℕ) (F : ℕ → ℝ) (K : ℝ)
    (hind : ∀ (n h : ℕ) (c : ℕ → ι), 0 < n → Odd n → Admissible C n h →
      repairCount C n c h ≤ R → (referenceDepth C c h : ℝ) ≤ F n + K)
    (seed len t : ℕ → ℕ) (c : ℕ → ℕ → ι) (before after : ι)
    (hseed : ∀ j, 0 < seed j) (hodd : ∀ j, Odd (seed j))
    (had : ∀ j, Admissible C (seed j) (len j))
    (hr : ∀ j, repairCount C (seed j) (c j) (len j) ≤ R + 1)
    (ht : ∀ j, t j < len j) (hbad : ∀ j, ¬ GoodAt C (seed j) (c j) (t j))
    (hbefore : ∀ j, c j (t j) = before)
    (hafter : ∀ j, c j (t j + 1) = after)
    (hEx : Tendsto (fun j => (referenceDepth C (c j) (len j) : ℝ) - F (seed j))
      atTop atTop) :
    Tendsto (fun j => (normalizedDefect C (seed j) (c j) (t j + 1) : ℝ) /
      (normalizedDefect C (seed j) (c j) (t j) : ℝ)) atTop (𝓝 1) := by
  obtain ⟨hleft, hright⟩ := repair_neighbors_tendsto_of_divergent_excess
    C R F K hind seed len t c hseed hodd had hr ht hbad hEx
  exact actual_repair_ratio_tendsto_one C seed len t c before after
    hseed had ht hbefore hafter hleft hright

/-- Every pre- and post-repair normalized defect has the same asymptotic scale
as the initial one. The only steps used between repairs are the genuinely good
steps supplied by the exact sorted enumeration. -/
theorem sorted_repairs_normalized_tendsto
    (C : RationalPeriodicDictionary ι) (seed len : ℕ → ℕ)
    (c : ℕ → ℕ → ι) (r : ℕ) (p : ℕ → Fin r → ℕ)
    (hseed : ∀ j, 0 < seed j) (had : ∀ j, Admissible C (seed j) (len j))
    (hmono : ∀ j, StrictMono (p j)) (hbound : ∀ j i, p j i < len j)
    (henum : ∀ j t, t ∈ repairSet C (seed j) (c j) (len j) ↔ ∃ i, p j i = t)
    (hratio : ∀ i, Tendsto (fun j =>
      (normalizedDefect C (seed j) (c j) (p j i + 1) : ℝ) /
      (normalizedDefect C (seed j) (c j) (p j i) : ℝ)) atTop (𝓝 1)) :
    ∀ i, Tendsto (fun j =>
      (normalizedDefect C (seed j) (c j) (p j i) : ℝ) /
      (normalizedDefect C (seed j) (c j) 0 : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun j =>
      (normalizedDefect C (seed j) (c j) (p j i + 1) : ℝ) /
      (normalizedDefect C (seed j) (c j) 0 : ℝ)) atTop (𝓝 1) := by
  have hnz (j t : ℕ) (ht : t ≤ len j) :
      (normalizedDefect C (seed j) (c j) t : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (normalizedDefect_pos C (c j) (hseed j) (had j) ht)
  have hpost (i : Fin r)
      (hpre : Tendsto (fun j =>
        (normalizedDefect C (seed j) (c j) (p j i) : ℝ) /
        (normalizedDefect C (seed j) (c j) 0 : ℝ)) atTop (𝓝 1)) :
      Tendsto (fun j =>
        (normalizedDefect C (seed j) (c j) (p j i + 1) : ℝ) /
        (normalizedDefect C (seed j) (c j) 0 : ℝ)) atTop (𝓝 1) := by
    have hm := (hratio i).mul hpre
    simp only [one_mul] at hm
    apply hm.congr
    intro j
    field_simp [hnz j (p j i) (hbound j i).le, hnz j 0 (Nat.zero_le _)]
  cases r with
  | zero => intro i; exact Fin.elim0 i
  | succ r =>
    intro i
    induction i using Fin.induction with
    | zero =>
      have he (j : ℕ) : normalizedDefect C (seed j) (c j) (p j 0) =
          normalizedDefect C (seed j) (c j) 0 := by
        apply normalizedDefect_good_gap C (seed j) (c j) (Nat.zero_le _)
        intro t ht
        exact goodAt_before_first_repair C (seed j) (c j) (len j)
          (hmono j) (hbound j) (henum j) (Nat.succ_pos r)
          (Finset.mem_Ico.mp ht).2
      have hpre : Tendsto (fun j =>
          (normalizedDefect C (seed j) (c j) (p j 0) : ℝ) /
          (normalizedDefect C (seed j) (c j) 0 : ℝ)) atTop (𝓝 1) := by
        have he' : (fun j =>
          (normalizedDefect C (seed j) (c j) (p j 0) : ℝ) /
          (normalizedDefect C (seed j) (c j) 0 : ℝ)) = fun _j => (1 : ℝ) := by
          funext j
          rw [he j, div_self (hnz j 0 (Nat.zero_le _))]
        rw [he']
        exact tendsto_const_nhds
      exact ⟨hpre, hpost 0 hpre⟩
    | succ i ih =>
      have he (j : ℕ) : normalizedDefect C (seed j) (c j) (p j i.succ) =
          normalizedDefect C (seed j) (c j) (p j i.castSucc + 1) := by
        have horder := (hmono j) (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
        apply normalizedDefect_good_gap C (seed j) (c j) (Nat.succ_le_of_lt horder)
        intro t ht
        exact goodAt_between_repairs C (seed j) (c j) (len j)
          (hmono j) (hbound j) (henum j) (i := i.castSucc) (j := i.succ) (by rfl)
          (by have := (Finset.mem_Ico.mp ht).1; omega) (Finset.mem_Ico.mp ht).2
      have hpre : Tendsto (fun j =>
          (normalizedDefect C (seed j) (c j) (p j i.succ) : ℝ) /
          (normalizedDefect C (seed j) (c j) 0 : ℝ)) atTop (𝓝 1) := by
        convert ih.2 using 1
        funext j
        rw [he j]
      exact ⟨hpre, hpost i.succ hpre⟩

/-- A concrete family of sorted actual repairs, with stabilized labels and
divergent successors, has all its pre- and post-repair snapshots normalized
to the initial defect tending to one. -/
theorem actual_sorted_repairs_normalized_tendsto
    (C : RationalPeriodicDictionary ι) (seed len : ℕ → ℕ)
    (c : ℕ → ℕ → ι) (r : ℕ) (p : ℕ → Fin r → ℕ)
    (before after : Fin r → ι)
    (hseed : ∀ j, 0 < seed j) (had : ∀ j, Admissible C (seed j) (len j))
    (hmono : ∀ j, StrictMono (p j)) (hbound : ∀ j i, p j i < len j)
    (henum : ∀ j t, t ∈ repairSet C (seed j) (c j) (len j) ↔ ∃ i, p j i = t)
    (hbefore : ∀ j i, c j (p j i) = before i)
    (hafter : ∀ j i, c j (p j i + 1) = after i)
    (hright : ∀ i, Tendsto (fun j => oddOrbit (seed j) (p j i + 1)) atTop atTop) :
    ∀ i, Tendsto (fun j =>
      (normalizedDefect C (seed j) (c j) (p j i) : ℝ) /
      (normalizedDefect C (seed j) (c j) 0 : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun j =>
      (normalizedDefect C (seed j) (c j) (p j i + 1) : ℝ) /
      (normalizedDefect C (seed j) (c j) 0 : ℝ)) atTop (𝓝 1) := by
  apply sorted_repairs_normalized_tendsto C seed len c r p hseed had hmono hbound henum
  intro i
  exact actual_repair_ratio_tendsto_one C seed len (fun j => p j i) c
    (before i) (after i) hseed had (fun j => hbound j i)
    (fun j => hbefore j i) (fun j => hafter j i)
    (predecessor_tendsto_of_successor seed (fun j => p j i) (hright i)) (hright i)

/-- Clearing a common denominator and terminal power does not change a
snapshot's ratio to the initial snapshot. -/
theorem integerSnapshot_ratio_eq (C : RationalPeriodicDictionary ι)
    (n : ℕ) (c : ℕ → ι) {H t : ℕ} (ht : t ≤ H) :
    (integerSnapshot C n c H t : ℝ) / (integerSnapshot C n c H 0 : ℝ) =
      (normalizedDefect C n c t : ℝ) / (normalizedDefect C n c 0 : ℝ) := by
  have hfactor : (C.denominator : ℚ) * (3 : ℚ)^H ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast ne_of_gt C.denominator_pos) (by positivity)
  have hq : (integerSnapshot C n c H t : ℚ) / (integerSnapshot C n c H 0 : ℚ) =
      normalizedDefect C n c t / normalizedDefect C n c 0 := by
    rw [integerSnapshot_cast C n c ht, integerSnapshot_cast C n c (Nat.zero_le H)]
    exact mul_div_mul_left _ _ hfactor
  have hc := congrArg (fun q : ℚ => (q : ℝ)) hq
  push_cast at hc
  exact hc

/-- Actual normalized-defect convergence transfers to the integer vectors
used by the Subspace Theorem, even when the terminal lengths vary. -/
theorem integerSnapshot_normalized_tendsto (C : RationalPeriodicDictionary ι)
    (seed len t : ℕ → ℕ) (c : ℕ → ℕ → ι)
    (ht : ∀ j, t j ≤ len j)
    (hlim : Tendsto (fun j =>
      (normalizedDefect C (seed j) (c j) (t j) : ℝ) /
      (normalizedDefect C (seed j) (c j) 0 : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun j => (integerSnapshot C (seed j) (c j) (len j) (t j) : ℝ) /
      (integerSnapshot C (seed j) (c j) (len j) 0 : ℝ)) atTop (𝓝 1) := by
  apply hlim.congr
  intro j
  exact (integerSnapshot_ratio_eq C (seed j) (c j) (ht j)).symm

/-- A boundary lying in a chosen good gap inherits the normalized limit at
that gap's initial endpoint. -/
theorem normalizedDefect_good_gap_tendsto (C : RationalPeriodicDictionary ι)
    (seed l u : ℕ → ℕ) (c : ℕ → ℕ → ι)
    (hlu : ∀ j, l j ≤ u j)
    (hgood : ∀ j t, t ∈ Finset.Ico (l j) (u j) → GoodAt C (seed j) (c j) t)
    (hlim : Tendsto (fun j =>
      (normalizedDefect C (seed j) (c j) (l j) : ℝ) /
      (normalizedDefect C (seed j) (c j) 0 : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun j =>
      (normalizedDefect C (seed j) (c j) (u j) : ℝ) /
      (normalizedDefect C (seed j) (c j) 0 : ℝ)) atTop (𝓝 1) := by
  apply hlim.congr
  intro j
  rw [normalizedDefect_good_gap C (seed j) (c j) (hlu j) (hgood j)]

end CollatzPrefix
