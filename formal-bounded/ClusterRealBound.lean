import SpliceRepairs
import Mathlib.Tactic

namespace CollatzPrefix
open scoped BigOperators

/-- A cumulative-exponent scale at an earlier point of a width-w block is
at most 3^w times the endpoint scale. -/
theorem scale_le_endpoint (A : ℕ → ℕ) (hA : Monotone A)
    (l w t : ℕ) (hlt : l ≤ t) (htk : t ≤ l + w) :
    (2 : ℚ) ^ A t / 3 ^ t ≤ 3 ^ w * (2 ^ A (l + w) / 3 ^ (l + w)) := by
  have h2 : (2 : ℚ) ^ A t ≤ 2 ^ A (l + w) := by
    gcongr
    · norm_num
    · exact hA htk
  have h3 : (3 : ℚ) ^ (l + w - t) ≤ 3 ^ w := by
    gcongr
    · norm_num
    · omega
  have hp : (3 : ℚ) ^ (l + w) = 3 ^ (l + w - t) * 3 ^ t := by
    rw [← pow_add, Nat.sub_add_cancel htk]
  calc
    _ ≤ (2 : ℚ) ^ A (l + w) / 3 ^ t := div_le_div_of_nonneg_right h2 (by positivity)
    _ = 3 ^ (l + w - t) * (2 ^ A (l + w) / 3 ^ (l + w)) := by
      rw [hp]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 (by positivity)

/-- Finite telescoping turns a uniform step bound into a block bound. -/
theorem cluster_bound_of_step_bound (Z : ℕ → ℚ) (l w : ℕ) (B : ℚ)
    (hB : ∀ t, l ≤ t → t < l + w → |Z (t + 1) - Z t| ≤ B) :
    |Z (l + w) - Z l| ≤ (w : ℚ) * B := by
  have htel : (∑ j ∈ Finset.range w, (Z (l + j + 1) - Z (l + j))) =
      Z (l + w) - Z l := by
    simpa [Nat.add_assoc] using Finset.sum_range_sub (fun j => Z (l + j)) w
  rw [← htel]
  calc
    _ ≤ ∑ j ∈ Finset.range w, |Z (l + j + 1) - Z (l + j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range w, B :=
      Finset.sum_le_sum (fun j hj => hB (l + j) (by omega) (by simpa using Finset.mem_range.mp hj))
    _ = _ := by simp

/-- The two terms of an exact normalized increment are uniformly bounded
by a common endpoint scale. -/
theorem scaled_defect_increment_bound (c d M B s s' : ℚ)
    (hM : 0 ≤ M) (_hB : 0 ≤ B) (hc : |c| ≤ M) (hd : |d| ≤ M)
    (hs : 0 ≤ s) (hs' : 0 ≤ s') (hsB : s ≤ B) (hsB' : s' ≤ B) :
    |((3 * c + 1) / 3) * s - d * s'| ≤ (4 * M + 1) * B := by
  have hcoeff : |(3 * c + 1) / 3| ≤ 3 * M + 1 := by
    rw [abs_div]
    norm_num
    have hh := abs_add_le (3 * c) 1
    rw [abs_mul] at hh
    norm_num at hh
    linarith
  calc
    _ ≤ |((3 * c + 1) / 3) * s| + |d * s'| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (((3 * c + 1) / 3) * s) (-(d * s'))
    _ = |(3 * c + 1) / 3| * s + |d| * s' := by
      rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg hs']
    _ ≤ (3 * M + 1) * B + M * B := by
      have hfirst := mul_le_mul hcoeff hsB hs (by linarith : 0 ≤ 3 * M + 1)
      have hsecond := mul_le_mul hd hsB' hs' hM
      linarith
    _ = _ := by ring

theorem actualDepth_succ (n t : ℕ) :
    actualDepth n (t + 1) = actualDepth n t + acceleratedExponent (oddOrbit n t) := by
  simp [actualDepth, Finset.sum_range_succ]

theorem actualDepth_monotone (n : ℕ) : Monotone (actualDepth n) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hab)

variable {ι : Type*} [Fintype ι]

/-- Uniform absolute reference-height bound for the fixed dictionary. -/
def referenceAbsCap (C : RationalPeriodicDictionary ι) : ℚ := ∑ i, |C.value i|

theorem referenceAbsCap_nonneg (C : RationalPeriodicDictionary ι) :
    0 ≤ referenceAbsCap C := Finset.sum_nonneg (fun i _ => abs_nonneg (C.value i))

theorem abs_reference_le_cap (C : RationalPeriodicDictionary ι) (i : ι) :
    |C.value i| ≤ referenceAbsCap C :=
  Finset.single_le_sum (fun j _ => abs_nonneg (C.value j)) (Finset.mem_univ i)

theorem normalizedDefect_increment (C : RationalPeriodicDictionary ι)
    (n : ℕ) (c : ℕ → ι) (t : ℕ) :
    normalizedDefect C n c (t + 1) - normalizedDefect C n c t =
      ((3 * C.value (c t) + 1) / 3) * ((2 : ℚ) ^ actualDepth n t / 3 ^ t) -
        C.value (c (t + 1)) * (2 ^ actualDepth n (t + 1) / 3 ^ (t + 1)) := by
  have he := defect_increment (oddOrbit n t : ℚ) (C.value (c t))
    (C.value (c (t + 1))) (acceleratedExponent (oddOrbit n t)) (actualDepth n t) t
  rw [oddOrbit_affineStep] at he
  unfold normalizedDefect
  rw [actualDepth_succ]
  rw [he]
  simp only [pow_succ]
  field_simp

/-- The actual normalized cluster increment is controlled by its endpoint
scale, with a constant depending only on the dictionary and block width. -/
theorem normalizedDefect_cluster_bound (C : RationalPeriodicDictionary ι)
    (n : ℕ) (c : ℕ → ι) (l w : ℕ) :
    |normalizedDefect C n c (l + w) - normalizedDefect C n c l| ≤
      ((w : ℚ) * (4 * referenceAbsCap C + 1) * 3 ^ w) *
        ((2 : ℚ) ^ actualDepth n (l + w) / 3 ^ (l + w)) := by
  have h := cluster_bound_of_step_bound (normalizedDefect C n c) l w
    ((4 * referenceAbsCap C + 1) *
      (3 ^ w * ((2 : ℚ) ^ actualDepth n (l + w) / 3 ^ (l + w)))) ?_
  · calc
      _ ≤ _ := h
      _ = _ := by ring
  intro t hlt htk
  rw [normalizedDefect_increment]
  apply scaled_defect_increment_bound
  · exact referenceAbsCap_nonneg C
  · positivity
  · exact abs_reference_le_cap C (c t)
  · exact abs_reference_le_cap C (c (t + 1))
  · positivity
  · positivity
  · exact scale_le_endpoint (actualDepth n) (actualDepth_monotone n) l w t hlt (by omega)
  · exact scale_le_endpoint (actualDepth n) (actualDepth_monotone n) l w (t + 1) (by omega) (by omega)

end CollatzPrefix
