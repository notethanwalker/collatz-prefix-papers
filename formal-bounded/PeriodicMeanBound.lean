import PrefixRepairs
import Mathlib.GroupTheory.OrderOfElement

/-!
# The minimum periodic mean and the reference-depth-to-length estimate

A finite permutation has a common positive period. Averaging each reference
orbit over this common period gives exactly its cycle mean. A finite potential
turns the minimum of these means into a per-step inequality; each repair pays
a bounded potential error. Thus the length coefficient uses the actual minimum
cycle mean, rather than the weaker bound `b ≥ 1`.
-/
namespace CollatzPrefix
open scoped BigOperators Classical

/-- Discrete weighted summation for one period. -/
theorem cyclic_weighted_difference (f : ℕ → ℝ) (L : ℕ) (hperiod : f L = f 0) :
    (∑ t ∈ Finset.range L, (t : ℝ) * f (t + 1)) -
      (∑ t ∈ Finset.range L, (t : ℝ) * f t) =
        (L : ℝ) * f 0 - ∑ t ∈ Finset.range L, f t := by
  have hs := (Finset.sum_range_succ f L).symm.trans (Finset.sum_range_succ' f L)
  rw [hperiod] at hs
  have hw := (Finset.sum_range_succ (fun t => (t : ℝ) * f t) L).symm.trans
    (Finset.sum_range_succ' (fun t => (t : ℝ) * f t) L)
  simp only [hperiod, Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one,
    add_mul, one_mul, Finset.sum_add_distrib] at hw
  linarith

namespace RationalPeriodicDictionary
variable {ι : Type*} [Fintype ι] (C : RationalPeriodicDictionary ι)

/-- A common period for all cycles in the finite dictionary permutation. -/
noncomputable def commonPeriod : ℕ := orderOf C.next

theorem commonPeriod_pos : 0 < C.commonPeriod := orderOf_pos C.next

theorem next_pow_commonPeriod : C.next ^ C.commonPeriod = 1 := pow_orderOf_eq_one C.next

/-- Mean reference depth of the cycle containing `i`, averaged over a common period. -/
noncomputable def cycleMeanAt (i : ι) : ℝ :=
  (∑ t ∈ Finset.range C.commonPeriod, (C.exponent ((C.next ^ t) i) : ℝ)) /
    C.commonPeriod

/-- A weighted-period potential whose increment is `b(i) - mean(i)`. -/
noncomputable def cyclePotential (i : ι) : ℝ :=
  (∑ t ∈ Finset.range C.commonPeriod, (t : ℝ) * C.exponent ((C.next ^ t) i)) /
    C.commonPeriod

theorem one_le_cycleMeanAt (i : ι) : 1 ≤ C.cycleMeanAt i := by
  have hP : (0 : ℝ) < C.commonPeriod := by exact_mod_cast C.commonPeriod_pos
  apply (le_div_iff₀ hP).mpr
  simp only [one_mul]
  calc
    (C.commonPeriod : ℝ) = ∑ _t ∈ Finset.range C.commonPeriod, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun t _ => by exact_mod_cast C.exponent_pos ((C.next ^ t) i))

theorem cyclePotential_nonneg (i : ι) : 0 ≤ C.cyclePotential i := by
  unfold cyclePotential
  positivity

/-- Exact local potential identity. -/
theorem cyclePotential_step (i : ι) :
    C.cyclePotential (C.next i) - C.cyclePotential i =
      (C.exponent i : ℝ) - C.cycleMeanAt i := by
  have hP : (C.commonPeriod : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt C.commonPeriod_pos
  have hperiod : (C.exponent ((C.next ^ C.commonPeriod) i) : ℝ) = C.exponent ((C.next ^ 0) i) := by
    simp only [C.next_pow_commonPeriod, pow_zero, Equiv.Perm.one_apply]
  have hweighted := cyclic_weighted_difference
    (fun t => (C.exponent ((C.next ^ t) i) : ℝ)) C.commonPeriod hperiod
  have hshift (t : ℕ) : (C.next ^ t) (C.next i) = (C.next ^ (t + 1)) i := by
    rw [pow_succ, Equiv.Perm.coe_mul]
    rfl
  unfold cyclePotential cycleMeanAt
  simp_rw [hshift]
  rw [← sub_div, hweighted]
  simp only [pow_zero, Equiv.Perm.one_apply]
  field_simp

/-- The common-period mean is constant along a dictionary cycle. -/
theorem cycleMeanAt_next (i : ι) : C.cycleMeanAt (C.next i) = C.cycleMeanAt i := by
  have hperiod : (C.exponent ((C.next ^ C.commonPeriod) i) : ℝ) = C.exponent i := by
    simp only [C.next_pow_commonPeriod, Equiv.Perm.one_apply]
  have hs := (Finset.sum_range_succ (fun t => (C.exponent ((C.next ^ t) i) : ℝ))
    C.commonPeriod).symm.trans
    (Finset.sum_range_succ' (fun t => (C.exponent ((C.next ^ t) i) : ℝ)) C.commonPeriod)
  simp only [pow_zero, Equiv.Perm.one_apply, hperiod] at hs
  have hshift (t : ℕ) : (C.next ^ t) (C.next i) = (C.next ^ (t + 1)) i := by
    rw [pow_succ, Equiv.Perm.coe_mul]
    rfl
  unfold cycleMeanAt
  simp_rw [hshift]
  congr 1
  linarith

theorem cycleMeanAt_pow (i : ι) (t : ℕ) : C.cycleMeanAt ((C.next ^ t) i) = C.cycleMeanAt i := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Equiv.Perm.coe_mul]
    change C.cycleMeanAt (C.next ((C.next ^ t) i)) = _
    rw [C.cycleMeanAt_next, ih]

/-- The definition agrees with the ordinary average over any return period,
in particular the least period of the reference's own cycle. -/
theorem cycleMeanAt_eq_period_average (i : ι) (m : ℕ) (hm : 0 < m)
    (hreturn : (C.next ^ m) i = i) :
    C.cycleMeanAt i = (∑ t ∈ Finset.range m, (C.exponent ((C.next ^ t) i) : ℝ)) / m := by
  have hpoint (t : ℕ) : (C.exponent ((C.next ^ t) i) : ℝ) = C.cycleMeanAt i +
      (C.cyclePotential ((C.next ^ (t + 1)) i) - C.cyclePotential ((C.next ^ t) i)) := by
    have hs := C.cyclePotential_step ((C.next ^ t) i)
    rw [C.cycleMeanAt_pow] at hs
    have hshift : C.next ((C.next ^ t) i) = (C.next ^ (t + 1)) i := by
      rw [pow_succ', Equiv.Perm.coe_mul]
      rfl
    rw [hshift] at hs
    linarith
  have hsum := Finset.sum_congr (s₁ := Finset.range m) rfl (fun t _ => hpoint t)
  rw [Finset.sum_add_distrib,
    Finset.sum_range_sub (fun t => C.cyclePotential ((C.next ^ t) i)) m] at hsum
  simp only [hreturn, pow_zero, Equiv.Perm.one_apply, sub_self, add_zero,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  rw [hsum]
  field_simp

/-- Every dictionary label has a positive least return period. -/
theorem minimalPeriod_pos (i : ι) : 0 < Function.minimalPeriod C.next i := by
  have hp : Function.IsPeriodicPt C.next C.commonPeriod i := by
    change (C.next : ι → ι)^[C.commonPeriod] i = i
    rw [← Equiv.Perm.coe_pow, C.next_pow_commonPeriod]
    rfl
  exact hp.minimalPeriod_pos C.commonPeriod_pos

/-- Thus the common-period mean is literally the average over the label's
own least period, establishing the paper's cycle-mean interpretation. -/
theorem cycleMeanAt_eq_minimalPeriod_average (i : ι) :
    C.cycleMeanAt i =
      (∑ t ∈ Finset.range (Function.minimalPeriod C.next i),
        (C.exponent ((C.next ^ t) i) : ℝ)) / Function.minimalPeriod C.next i := by
  apply C.cycleMeanAt_eq_period_average i _ (C.minimalPeriod_pos i)
  simpa only [Equiv.Perm.coe_pow] using (Function.iterate_minimalPeriod (f := C.next) (x := i))

/-- Uniform bound on the nonnegative potential over the finite dictionary. -/
noncomputable def potentialCap : ℝ := ∑ i, C.cyclePotential i

theorem potentialCap_nonneg : 0 ≤ C.potentialCap :=
  Finset.sum_nonneg (fun i _ => C.cyclePotential_nonneg i)

theorem cyclePotential_le_cap (i : ι) : C.cyclePotential i ≤ C.potentialCap :=
  Finset.single_le_sum (fun j _ => C.cyclePotential_nonneg j) (Finset.mem_univ i)

variable [Nonempty ι]

/-- The minimum of the cycle means, as in the paper's `β`. -/
noncomputable def minimumCycleMean : ℝ :=
  (Finset.univ.image C.cycleMeanAt).min' (Finset.univ_nonempty.image _)

theorem minimumCycleMean_le (i : ι) : C.minimumCycleMean ≤ C.cycleMeanAt i := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

theorem one_le_minimumCycleMean : 1 ≤ C.minimumCycleMean := by
  apply Finset.le_min'
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact C.one_le_cycleMeanAt i

theorem minimumCycleMean_pos : 0 < C.minimumCycleMean :=
  lt_of_lt_of_le (by norm_num) C.one_le_minimumCycleMean

/-- Every genuine cycle average is at least the dictionary minimum. -/
theorem minimumCycleMean_le_period_average (i : ι) (m : ℕ) (hm : 0 < m)
    (hreturn : (C.next ^ m) i = i) :
    C.minimumCycleMean ≤ (∑ t ∈ Finset.range m, (C.exponent ((C.next ^ t) i) : ℝ)) / m := by
  rw [← C.cycleMeanAt_eq_period_average i m hm hreturn]
  exact C.minimumCycleMean_le i

/-- Some dictionary cycle attains the minimum. -/
theorem exists_cycleMeanAt_eq_minimum : ∃ i, C.cycleMeanAt i = C.minimumCycleMean := by
  have hmem := Finset.min'_mem (Finset.univ.image C.cycleMeanAt)
    (Finset.univ_nonempty.image C.cycleMeanAt)
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi⟩

/-- Potential inequality along a genuine reference transition. -/
theorem minimum_mean_step (i : ι) :
    C.minimumCycleMean ≤ (C.exponent i : ℝ) -
      C.cyclePotential (C.next i) + C.cyclePotential i := by
  have hs := C.cyclePotential_step i
  have hm := C.minimumCycleMean_le i
  linarith

end RationalPeriodicDictionary

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- At a repair, the missing potential identity costs only a dictionary-dependent amount. -/
theorem minimum_mean_reference_step (C : RationalPeriodicDictionary ι)
    (n : ℕ) (c : ℕ → ι) (t : ℕ) :
    C.minimumCycleMean ≤ (C.exponent (c t) : ℝ) -
      C.cyclePotential (c (t + 1)) + C.cyclePotential (c t) +
        if ¬ GoodAt C n c t then C.minimumCycleMean + C.potentialCap else 0 := by
  classical
  by_cases hg : GoodAt C n c t
  · rw [ite_eq_right (not_not.mpr hg), hg.2, add_zero]
    exact C.minimum_mean_step (c t)
  · rw [ite_eq_left hg]
    have hV := C.cyclePotential_le_cap (c (t + 1))
    have hV0 := C.cyclePotential_nonneg (c t)
    have hb : (0 : ℝ) ≤ C.exponent (c t) := by positivity
    linarith

/-- Reference depth pays the true minimum cycle mean, with a bounded loss
for the initial potential and for each repair. No orbit size hypothesis is needed. -/
theorem minimum_mean_mul_length_le_depth (C : RationalPeriodicDictionary ι)
    (n h : ℕ) (c : ℕ → ι) :
    C.minimumCycleMean * h ≤ (referenceDepth C c h : ℝ) + C.potentialCap +
      (repairCount C n c h : ℝ) * (C.minimumCycleMean + C.potentialCap) := by
  classical
  have hsum := Finset.sum_le_sum (fun t (_ht : t ∈ Finset.range h) =>
    minimum_mean_reference_step C n c t)
  have htel := Finset.sum_range_sub (fun t => C.cyclePotential (c t)) h
  have hpen : (∑ t ∈ Finset.range h,
      if ¬ GoodAt C n c t then C.minimumCycleMean + C.potentialCap else 0) =
      (repairCount C n c h : ℝ) * (C.minimumCycleMean + C.potentialCap) := by
    rw [← Finset.sum_filter]
    simp [repairCount, repairSet]
    ring
  have hdepth : (∑ t ∈ Finset.range h, (C.exponent (c t) : ℝ)) = referenceDepth C c h := by
    simp [referenceDepth]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  rw [hdepth, hpen] at hsum
  simp only [Finset.sum_sub_distrib] at htel
  have hV := C.cyclePotential_le_cap (c 0)
  have hV0 := C.cyclePotential_nonneg (c h)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  nlinarith

/-- The uniform additive loss for prefixes with at most `R` repairs. -/
noncomputable def periodicMeanError (C : RationalPeriodicDictionary ι) (R : ℕ) : ℝ :=
  C.potentialCap + R * (C.minimumCycleMean + C.potentialCap)

theorem minimum_mean_mul_length_le_of_repairs (C : RationalPeriodicDictionary ι)
    (R : ℕ) (n h : ℕ) (c : ℕ → ι) (hr : repairCount C n c h ≤ R) :
    C.minimumCycleMean * h ≤ (referenceDepth C c h : ℝ) + periodicMeanError C R := by
  have hbase := minimum_mean_mul_length_le_depth C n h c
  have hnonneg : 0 ≤ C.minimumCycleMean + C.potentialCap :=
    add_nonneg C.minimumCycleMean_pos.le C.potentialCap_nonneg
  have hmul := mul_le_mul_of_nonneg_right (show (repairCount C n c h : ℝ) ≤ R by exact_mod_cast hr)
    hnonneg
  unfold periodicMeanError
  linarith

/-- The paper's length estimate follows with coefficient `(1+ε)/β`. -/
theorem length_log_bound_of_depth_bound (C : RationalPeriodicDictionary ι)
    (R : ℕ) (n h : ℕ) (c : ℕ → ι) (ε K : ℝ)
    (hr : repairCount C n c h ≤ R)
    (hdepth : (referenceDepth C c h : ℝ) ≤
      (1 + ε) * (Real.log (n + 1) / Real.log 2) + K) :
    (h : ℝ) ≤ ((1 + ε) / C.minimumCycleMean) * (Real.log (n + 1) / Real.log 2) +
      (K + periodicMeanError C R) / C.minimumCycleMean := by
  have hmean := minimum_mean_mul_length_le_of_repairs C R n h c hr
  have hbound : C.minimumCycleMean * h ≤
      (1 + ε) * (Real.log (n + 1) / Real.log 2) + K + periodicMeanError C R := by linarith
  calc
    (h : ℝ) ≤ ((1 + ε) * (Real.log (n + 1) / Real.log 2) + K +
        periodicMeanError C R) / C.minimumCycleMean :=
      (le_div_iff₀ C.minimumCycleMean_pos).mpr (by nlinarith [hbound])
    _ = _ := by ring

end CollatzPrefix
