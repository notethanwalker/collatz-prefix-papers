import DeepStepSpecialization

/-!
# Sharpness of the coefficient one

The explicit starts `2^(h+1)-1` produce `h` genuinely shallow accelerated
steps. All valuations and orbit identities are proved from the actual map.
These prefixes rule out any uniform leading coefficient strictly below one.
-/
namespace CollatzPrefix
open scoped BigOperators

/-- The sharp family of initial odd values. -/
def sharpShallowSeed (h : ℕ) : ℕ := 2 ^ (h + 1) - 1

/-- The explicit states through the first `h` accelerated steps. -/
def sharpShallowState (h t : ℕ) : ℕ := 3 ^ t * 2 ^ (h + 1 - t) - 1

theorem sharpShallowState_add_one (h t : ℕ) :
    sharpShallowState h t + 1 = 3 ^ t * 2 ^ (h + 1 - t) := by
  unfold sharpShallowState
  apply Nat.sub_add_cancel
  apply Nat.succ_le_of_lt
  positivity

@[simp] theorem sharpShallowState_zero (h : ℕ) : sharpShallowState h 0 = sharpShallowSeed h := by
  simp [sharpShallowState, sharpShallowSeed]

theorem sharpShallowState_pos {h t : ℕ} (ht : t ≤ h) : 0 < sharpShallowState h t := by
  have hexp : 1 ≤ h + 1 - t := by omega
  have hp : 2 ≤ 2 ^ (h + 1 - t) :=
    (show 2 ^ 1 ≤ 2 ^ (h + 1 - t) from Nat.pow_le_pow_right (by decide) hexp)
  have h3 : 1 ≤ 3 ^ t := Nat.one_le_pow _ _ (by decide)
  have hs := sharpShallowState_add_one h t
  nlinarith

theorem sharpShallowState_odd {h t : ℕ} (ht : t ≤ h) : Odd (sharpShallowState h t) := by
  have hexp : h + 1 - t = (h - t) + 1 := by omega
  have hmod : (sharpShallowState h t + 1) % 2 = 0 := by
    rw [sharpShallowState_add_one, hexp, pow_succ]
    simp [Nat.mul_mod]
  apply Nat.odd_iff.mpr
  omega

/-- Every preterminal explicit state is 3 modulo 4. -/
theorem sharpShallowState_mod_four {h t : ℕ} (ht : t < h) :
    sharpShallowState h t % 4 = 3 := by
  have hexp : h + 1 - t = (h - t - 1) + 2 := by omega
  have hmod : (sharpShallowState h t + 1) % 4 = 0 := by
    rw [sharpShallowState_add_one, hexp, pow_add]
    norm_num [Nat.mul_mod]
  omega

/-- For a natural state congruent to 3 modulo 4, the exact Collatz valuation is one. -/
theorem acceleratedExponent_eq_one_of_mod_four {n : ℕ} (hn : n % 4 = 3) :
    acceleratedExponent n = 1 := by
  have hnum : 3 * n + 1 ≠ 0 := by omega
  have hd2 : 2 ∣ 3 * n + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hnot4 : ¬ 4 ∣ 3 * n + 1 := by
    intro hd
    have hh := Nat.mod_eq_zero_of_dvd hd
    omega
  have hlo := one_le_padicValNat_of_dvd (p := 2) hnum hd2
  have hhi : padicValNat 2 (3 * n + 1) < 2 := by
    by_contra h
    have hd := (padicValNat_dvd_iff_le (p := 2) hnum).mpr (show 2 ≤ padicValNat 2 (3*n+1) by omega)
    exact hnot4 (by simpa using hd)
  unfold acceleratedExponent
  omega

theorem sharpShallowState_exponent {h t : ℕ} (ht : t < h) :
    acceleratedExponent (sharpShallowState h t) = 1 :=
  acceleratedExponent_eq_one_of_mod_four (sharpShallowState_mod_four ht)

/-- Exact shallow-step recurrence for the explicit family. -/
theorem sharpShallowState_recurrence {h t : ℕ} (ht : t < h) :
    2 * sharpShallowState h (t + 1) = 3 * sharpShallowState h t + 1 := by
  have hexp : h + 1 - t = (h + 1 - (t + 1)) + 1 := by omega
  have he : 2 * (sharpShallowState h (t + 1) + 1) =
      3 * (sharpShallowState h t + 1) := by
    rw [sharpShallowState_add_one, sharpShallowState_add_one, hexp]
    simp only [pow_succ]
    ring
  omega

theorem sharpShallowState_step {h t : ℕ} (ht : t < h) :
    accelerated (sharpShallowState h t) = sharpShallowState h (t + 1) := by
  have hs := accelerated_numerator (sharpShallowState h t)
  rw [sharpShallowState_exponent ht] at hs
  norm_num at hs
  have hx := sharpShallowState_recurrence ht
  omega

/-- The formula is the actual accelerated Collatz orbit, not merely a symbolic word. -/
theorem oddOrbit_sharpShallowSeed (h : ℕ) :
    ∀ t ≤ h, oddOrbit (sharpShallowSeed h) t = sharpShallowState h t := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    intro ht
    rw [oddOrbit_succ, ih (by omega), sharpShallowState_step (by omega)]

theorem sharpShallowSeed_pos (h : ℕ) : 0 < sharpShallowSeed h := by
  simpa using sharpShallowState_pos (h := h) (t := 0) (Nat.zero_le h)

theorem sharpShallowSeed_odd (h : ℕ) : Odd (sharpShallowSeed h) := by
  simpa using sharpShallowState_odd (h := h) (t := 0) (Nat.zero_le h)

/-- All first `h` actual accelerated exponents equal one. -/
theorem sharpShallowSeed_exponent (h : ℕ) {t : ℕ} (ht : t < h) :
    acceleratedExponent (oddOrbit (sharpShallowSeed h) t) = 1 := by
  rw [oddOrbit_sharpShallowSeed h t ht.le]
  exact sharpShallowState_exponent ht

/-- In particular this family uses no deep step at all. -/
theorem deepStepCount_sharpShallowSeed (h : ℕ) : deepStepCount (sharpShallowSeed h) h = 0 := by
  unfold deepStepCount
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro t ht hdeep
  rw [sharpShallowSeed_exponent h (Finset.mem_range.mp ht)] at hdeep
  omega

/-- Exact initial logarithmic height of the family. -/
theorem sharpShallowSeed_log_height (h : ℕ) :
    Real.log ((sharpShallowSeed h : ℝ) + 1) / Real.log 2 = (h : ℝ) + 1 := by
  have hs : sharpShallowSeed h + 1 = 2 ^ (h + 1) := by
    simpa using sharpShallowState_add_one h 0
  have hcast : (sharpShallowSeed h : ℝ) + 1 = (2 : ℝ) ^ (h + 1) := by exact_mod_cast hs
  rw [hcast, Real.log_pow]
  have hlog : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [mul_div_cancel_right₀ _ hlog]
  simp

/-- No uniform zero-deep-step estimate can have leading coefficient below one. -/
theorem no_uniform_shallow_leading_coefficient (κ : ℝ) (hκ : κ < 1) :
    ¬ ∃ K : ℝ, ∀ n h : ℕ, 0 < n → Odd n → deepStepCount n h = 0 →
      (h : ℝ) ≤ κ * (Real.log ((n : ℝ) + 1) / Real.log 2) + K := by
  rintro ⟨K, hK⟩
  obtain ⟨h, hh⟩ := exists_nat_gt ((κ + K) / (1 - κ))
  have hh' : κ + K < (h : ℝ) * (1 - κ) :=
    (div_lt_iff₀ (by linarith : 0 < 1 - κ)).mp hh
  have hb := hK (sharpShallowSeed h) h (sharpShallowSeed_pos h) (sharpShallowSeed_odd h)
    (deepStepCount_sharpShallowSeed h)
  rw [sharpShallowSeed_log_height] at hb
  nlinarith

end CollatzPrefix
