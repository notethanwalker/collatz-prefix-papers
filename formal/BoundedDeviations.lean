import FormalComponents
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Accelerated orbits and the zero-repair periodic-reference theorem

This file proves the valuation reduction and the full zero-repair case for a
finite rational periodic dictionary. It does not claim the arbitrary-repair
theorem: the p-adic Subspace Theorem and nondegenerate S-unit finiteness used
in the paper are not imported or assumed here.
-/

namespace CollatzPrefix
open scoped BigOperators

/-- The exponent in the accelerated odd Collatz map. -/
def acceleratedExponent (n : ℕ) : ℕ := padicValNat 2 (3 * n + 1)

/-- The accelerated map; on odd positive inputs this is the usual odd map. -/
def accelerated (n : ℕ) : ℕ := (3 * n + 1) / 2 ^ acceleratedExponent n

theorem accelerated_numerator (n : ℕ) :
    2 ^ acceleratedExponent n * accelerated n = 3 * n + 1 := by
  simpa [accelerated, acceleratedExponent, Nat.mul_comm] using
    (Nat.div_mul_cancel (pow_padicValNat_dvd (p := 2) (n := 3 * n + 1)))

theorem accelerated_pos (n : ℕ) : 0 < accelerated n := by
  have h := accelerated_numerator n
  by_contra hn
  have hz : accelerated n = 0 := by omega
  rw [hz, mul_zero] at h
  omega

theorem accelerated_odd (n : ℕ) : Odd (accelerated n) := by
  have hv : padicValNat 2 (accelerated n) = 0 := by
    unfold accelerated acceleratedExponent
    rw [padicValNat.div_pow (pow_padicValNat_dvd (p := 2)), Nat.sub_self]
  have hnot : ¬2 ∣ accelerated n := by
    intro hd
    have := one_le_padicValNat_of_dvd (accelerated_pos n) hd
    omega
  exact Nat.odd_iff.mpr (by omega)

theorem acceleratedExponent_pos {n : ℕ} (hn : Odd n) :
    0 < acceleratedExponent n := by
  apply one_le_padicValNat_of_dvd (by omega)
  rcases hn with ⟨k, hk⟩
  exact ⟨3 * k + 2, by omega⟩

/-- An integer-scaled finite dictionary of rational periodic trajectories.
The common denominator is odd, all numerator labels are odd, and `next`
permutes the labels. The affine equation and oddness force each specified
exponent to be its exact 2-adic valuation. -/
structure RationalPeriodicDictionary (ι : Type*) [Fintype ι] where
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_odd : Odd denominator
  numerator : ι → ℤ
  numerator_odd : ∀ i, Odd (numerator i)
  next : Equiv.Perm ι
  exponent : ι → ℕ
  exponent_pos : ∀ i, 0 < exponent i
  step : ∀ i, (2 : ℤ) ^ exponent i * numerator (next i) =
    3 * numerator i + denominator

namespace RationalPeriodicDictionary
variable {ι : Type*} [Fintype ι] (C : RationalPeriodicDictionary ι)

/-- The rational reference associated to a label. -/
def value (i : ι) : ℚ := C.numerator i / C.denominator

theorem value_step (i : ι) :
    affineStep (C.exponent i) (C.value i) = C.value (C.next i) := by
  have hD : (C.denominator : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt C.denominator_pos
  have hs : (2 : ℚ) ^ C.exponent i * C.numerator (C.next i) =
      3 * C.numerator i + C.denominator := by exact_mod_cast C.step i
  unfold value affineStep
  field_simp [hD]
  nlinarith [hs]

/-- Common-denominator numerator of the defect from a reference label. -/
def defect (n : ℕ) (i : ι) : ℤ := C.denominator * (n : ℤ) - C.numerator i

theorem defect_step (n : ℕ) (i : ι)
    (hmatch : acceleratedExponent n = C.exponent i) :
    (2 : ℤ) ^ C.exponent i * C.defect (accelerated n) (C.next i) =
      3 * C.defect n i := by
  have hn : (2 : ℤ) ^ C.exponent i * (accelerated n : ℤ) = 3 * n + 1 := by
    exact_mod_cast (hmatch ▸ accelerated_numerator n)
  have hc := C.step i
  unfold defect
  linear_combination (C.denominator : ℤ) * hn - hc

theorem defect_even {n : ℕ} (hn : Odd n) (i : ι) : Even (C.defect n i) := by
  have hD : Odd (C.denominator : ℤ) := by exact_mod_cast C.denominator_odd
  have hn' : Odd (n : ℤ) := by exact_mod_cast hn
  exact (hD.mul hn').sub_odd (C.numerator_odd i)

/-- These really are odd 2-adic rational references, not just affine labels. -/
theorem value_valuation (i : ι) : padicValRat 2 (C.value i) = 0 := by
  have hp : C.numerator i ≠ 0 := by
    intro hz
    have ho := C.numerator_odd i
    simp [hz, Int.odd_iff] at ho
  have hD : (C.denominator : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt C.denominator_pos
  have hpq : (C.numerator i : ℚ) ≠ 0 := by exact_mod_cast hp
  have hvp : padicValInt 2 (C.numerator i) = 0 :=
    padicValInt.eq_zero_of_not_dvd (fun hd =>
      (Int.not_even_iff_odd.mpr (C.numerator_odd i)) (even_iff_two_dvd.mpr hd))
  have hvD : padicValNat 2 C.denominator = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun hd =>
      (Nat.not_even_iff_odd.mpr C.denominator_odd) (even_iff_two_dvd.mpr hd))
  rw [value, padicValRat.div hpq hD, padicValRat.of_int, padicValRat.of_nat, hvp, hvD]
  norm_num

/-- The dictionary exponent is the exact valuation prescribed in the paper. -/
theorem exponent_eq_valuation (i : ι) :
    padicValRat 2 (3 * C.value i + 1) = C.exponent i := by
  have hs := C.value_step i
  unfold affineStep at hs
  have htwo : (2 : ℚ) ^ C.exponent i ≠ 0 := by positivity
  have hp : C.numerator (C.next i) ≠ 0 := by
    intro hz
    have ho := C.numerator_odd (C.next i)
    simp [hz, Int.odd_iff] at ho
  have hv : C.value (C.next i) ≠ 0 := by
    unfold value
    exact div_ne_zero (by exact_mod_cast hp)
      (by exact_mod_cast ne_of_gt C.denominator_pos)
  have heq : 3 * C.value i + 1 = (2 : ℚ) ^ C.exponent i * C.value (C.next i) := by
    exact (div_eq_iff htwo).mp hs |>.trans (mul_comm _ _)
  rw [heq, padicValRat.mul htwo hv, C.value_valuation, add_zero,
    padicValRat.pow (by norm_num)]
  change _ * padicValRat 2 ((2 : ℕ) : ℚ) = _
  rw [padicValRat.self (by norm_num), mul_one]

/-- A uniform coefficient bounding every integral scaled defect. -/
def scale : ℕ := C.denominator + ∑ i, (C.numerator i).natAbs

theorem scale_pos : 0 < C.scale := by
  unfold scale
  exact Nat.add_pos_left C.denominator_pos _

theorem defect_natAbs_le (n : ℕ) (i : ι) :
    (C.defect n i).natAbs ≤ C.scale * (n + 1) := by
  have hi : (C.numerator i).natAbs ≤ ∑ j, (C.numerator j).natAbs :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (C.numerator j).natAbs) (Finset.mem_univ i)
  have hd := Int.natAbs_sub_le ((C.denominator : ℤ) * n) (C.numerator i)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hd
  unfold defect scale
  calc
    _ ≤ C.denominator * n + (C.numerator i).natAbs := hd
    _ ≤ C.denominator * n + ∑ j, (C.numerator j).natAbs := Nat.add_le_add_left hi _
    _ ≤ _ := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
      omega

theorem defect_pos_of_value_lt {n : ℕ} {i : ι} (h : C.value i < (n : ℚ)) :
    0 < C.defect n i := by
  have hD : (0 : ℚ) < C.denominator := by exact_mod_cast C.denominator_pos
  have heq : (C.defect n i : ℚ) = C.denominator * ((n : ℚ) - C.value i) := by
    unfold defect value
    push_cast
    field_simp
    ring
  have hh : (0 : ℚ) < C.defect n i := by
    rw [heq]
    exact mul_pos hD (sub_pos.mpr h)
  exact_mod_cast hh

end RationalPeriodicDictionary

/-- Valuations of an integer defect lose precisely the exponent at a good step. -/
theorem defect_valuation_step {u v : ℤ} {a : ℕ} (hu : u ≠ 0)
    (hstep : (2 : ℤ) ^ a * v = 3 * u) :
    a + padicValInt 2 v = padicValInt 2 u := by
  have hv : v ≠ 0 := by
    intro hv
    rw [hv, mul_zero] at hstep
    exact hu (by omega)
  have h := congrArg (padicValInt 2) hstep
  rw [padicValInt.mul (by positivity) hv,
    padicValInt.mul (by norm_num) hu] at h
  have hpow : padicValInt 2 ((2 : ℤ) ^ a) = a := by
    simp [padicValInt, Int.natAbs_pow]
  have hthree : padicValInt 2 3 = 0 := by
    exact padicValInt.eq_zero_of_not_dvd (by decide)
  simpa [hpow, hthree] using h

/-- Telescoping the actual valuation drop along a finite good run. -/
theorem good_run_valuation (d : ℕ → ℤ) (a : ℕ → ℕ) (h : ℕ)
    (hd : ∀ t ≤ h, d t ≠ 0)
    (hs : ∀ t < h, (2 : ℤ) ^ a t * d (t + 1) = 3 * d t) :
    (∑ t ∈ Finset.range h, a t) + padicValInt 2 (d h) = padicValInt 2 (d 0) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hp := ih (fun t ht => hd t (by omega)) (fun t ht => hs t (by omega))
    have he := defect_valuation_step (hd h (by omega)) (hs h (by omega))
    rw [Finset.sum_range_succ]
    omega

/-- The zero-repair valuation bound for the actual accelerated orbit and a
rational periodic dictionary. Only exclusion of zero defect is needed; both
domain alternatives in the paper guarantee that exclusion. -/
theorem periodic_no_repair_valuation {ι : Type*} [Fintype ι]
    (C : RationalPeriodicDictionary ι) (n : ℕ → ℕ) (c : ℕ → ι) (h : ℕ)
    (hn : ∀ t ≤ h, Odd (n t))
    (hd : ∀ t ≤ h, C.defect (n t) (c t) ≠ 0)
    (hstep : ∀ t < h, n (t + 1) = accelerated (n t))
    (hphase : ∀ t < h, c (t + 1) = C.next (c t))
    (hmatch : ∀ t < h, acceleratedExponent (n t) = C.exponent (c t)) :
    (∑ t ∈ Finset.range h, C.exponent (c t)) + 1 ≤
      padicValInt 2 (C.defect (n 0) (c 0)) := by
  have ht := good_run_valuation (fun t => C.defect (n t) (c t))
    (fun t => C.exponent (c t)) h hd (fun t ht => by
      dsimp only
      rw [hstep t ht, hphase t ht]
      exact C.defect_step (n t) (c t) (hmatch t ht))
  dsimp only at ht
  have he := C.defect_even (hn h le_rfl) (c h)
  have hev : (2 : ℤ) ∣ C.defect (n h) (c h) := even_iff_two_dvd.mp he
  have hv : 1 ≤ padicValInt 2 (C.defect (n h) (c h)) := by
    have hh := (padicValInt_dvd_iff (p := 2) 1 (C.defect (n h) (c h))).mp
      (by simpa using hev)
    exact hh.resolve_left (hd h le_rfl)
  omega

/-- The corresponding sharp power bound; unlike the arbitrary-repair theorem,
this result needs no external Diophantine input. -/
theorem periodic_no_repair_bound {ι : Type*} [Fintype ι]
    (C : RationalPeriodicDictionary ι) (n : ℕ → ℕ) (c : ℕ → ι) (h : ℕ)
    (hn : ∀ t ≤ h, Odd (n t))
    (hd : ∀ t ≤ h, C.defect (n t) (c t) ≠ 0)
    (hstep : ∀ t < h, n (t + 1) = accelerated (n t))
    (hphase : ∀ t < h, c (t + 1) = C.next (c t))
    (hmatch : ∀ t < h, acceleratedExponent (n t) = C.exponent (c t)) :
    2 ^ ((∑ t ∈ Finset.range h, C.exponent (c t)) + 1) ≤
      (C.defect (n 0) (c 0)).natAbs := by
  have hv := periodic_no_repair_valuation C n c h hn hd hstep hphase hmatch
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr (hd 0 (by omega)))
  exact (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr (hd 0 (by omega)))).mpr hv

/-- A sharp, uniform coefficient-one logarithmic bound for zero repairs.
The constant is explicit and depends only on the finite dictionary.
The domain condition is implied by either domain alternative of the paper. -/
theorem periodic_no_repair_log_bound {ι : Type*} [Fintype ι]
    (C : RationalPeriodicDictionary ι) (n : ℕ → ℕ) (c : ℕ → ι) (h : ℕ)
    (hn : ∀ t ≤ h, Odd (n t))
    (hdom : ∀ t ≤ h, C.value (c t) < (n t : ℚ))
    (hstep : ∀ t < h, n (t + 1) = accelerated (n t))
    (hphase : ∀ t < h, c (t + 1) = C.next (c t))
    (hmatch : ∀ t < h, acceleratedExponent (n t) = C.exponent (c t)) :
    ((∑ t ∈ Finset.range h, C.exponent (c t) : ℕ) : ℝ) ≤
      Real.log (n 0 + 1) / Real.log 2 + Real.log C.scale / Real.log 2 := by
  have hd : ∀ t ≤ h, C.defect (n t) (c t) ≠ 0 :=
    fun t ht => ne_of_gt (C.defect_pos_of_value_lt (hdom t ht))
  have hp := periodic_no_repair_bound C n c h hn hd hstep hphase hmatch
  have hsize := C.defect_natAbs_le (n 0) (c 0)
  let B : ℕ := ∑ t ∈ Finset.range h, C.exponent (c t)
  have hpower : (2 : ℝ) ^ B ≤ (C.scale : ℝ) * ((n 0 : ℝ) + 1) := by
    have hpow : 2 ^ B ≤ 2 ^ (B + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hnat : 2 ^ B ≤ C.scale * (n 0 + 1) := hpow.trans (hp.trans hsize)
    exact_mod_cast hnat
  have hscale : (0 : ℝ) < C.scale := by exact_mod_cast C.scale_pos
  have hn0 : (0 : ℝ) < (n 0 : ℝ) + 1 := by positivity
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ B) hpower
  rw [Real.log_pow, Real.log_mul (ne_of_gt hscale) (ne_of_gt hn0)] at hlog
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  change (B : ℝ) ≤ _
  rw [← add_div]
  apply (le_div_iff₀ htwo).mpr
  exact hlog.trans_eq (add_comm _ _)

end CollatzPrefix
