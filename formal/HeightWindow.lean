import FormalComponents
import Mathlib.Algebra.Order.Floor.Semiring

namespace CollatzPrefix

noncomputable def orbitHeight (n M : ℕ) : ℕ :=
  (Finset.range M).sup (fun t => shortcut^[t] n)

noncomputable def heightWindow (H : ℕ) : ℕ :=
  ⌈Real.log ((H : ℝ) + 1) / Real.log 2⌉₊

theorem orbit_le_height (n M t : ℕ) (ht : t < M) :
    shortcut^[t] n ≤ orbitHeight n M := by
  exact Finset.le_sup (f := fun t => shortcut^[t] n) (Finset.mem_range.mpr ht)

theorem orbitHeight_pos (n M : ℕ) (hn : 0 < n) (hM : 0 < M) :
    0 < orbitHeight n M := by
  have h := orbit_le_height n M 0 hM
  simpa using lt_of_lt_of_le hn h

theorem height_lt_two_pow_window (H : ℕ) (hH : 0 < H) :
    H < 2 ^ heightWindow H := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil := Nat.le_ceil (Real.log ((H : ℝ) + 1) / Real.log 2)
  change Real.log ((H : ℝ) + 1) / Real.log 2 ≤ (heightWindow H : ℝ) at hceil
  have hlog : Real.log ((H : ℝ) + 1) ≤ Real.log ((2 : ℝ) ^ heightWindow H) := by
    rw [Real.log_pow]
    exact (div_le_iff₀ h2).mp hceil
  have hh : (H : ℝ) + 1 ≤ (2 : ℝ) ^ heightWindow H :=
    (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog
  have : (H : ℝ) < (2 : ℝ) ^ heightWindow H := by linarith
  exact_mod_cast this

theorem heightWindow_le_log (H : ℕ) (hH : 0 < H) :
    (heightWindow H : ℝ) ≤ Real.log (H : ℝ) / Real.log 2 + 2 := by
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHp : (0 : ℝ) < H := by positivity
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlognonneg : 0 ≤ Real.log ((H : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hceil := Nat.ceil_lt_add_one (div_nonneg hlognonneg h2.le)
  change (heightWindow H : ℝ) < Real.log ((H : ℝ) + 1) / Real.log 2 + 1 at hceil
  have hlog : Real.log ((H : ℝ) + 1) ≤ Real.log (H : ℝ) + Real.log 2 := by
    calc
      _ ≤ Real.log ((H : ℝ) * 2) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := Real.log_mul (ne_of_gt hHp) (by norm_num)
  have hdiv := (div_le_div_iff_of_pos_right h2).mpr hlog
  rw [add_div, div_self (ne_of_gt h2)] at hdiv
  linarith

end CollatzPrefix
