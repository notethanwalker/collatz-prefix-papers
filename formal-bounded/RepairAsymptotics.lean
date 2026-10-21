import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace CollatzPrefix
open Filter
open scoped Topology BigOperators

/-- A repair's exact normalized defect ratio tends to one when both
neighboring states escape, for fixed reference labels. -/
theorem repair_ratio_tendsto_one (x y : ℕ → ℝ) (c d : ℝ)
    (hx : Tendsto x atTop atTop) (hy : Tendsto y atTop atTop) :
    Tendsto (fun j => (1 + 1 / (3 * x j)) *
      (1 - d / y j) / (1 - c / x j)) atTop (𝓝 1) := by
  have hfirst := (hx.const_mul_atTop (by norm_num : (0 : ℝ) < 3)).const_div_atTop 1
  have hsecond := hy.const_div_atTop d
  have hthird := hx.const_div_atTop c
  have h := (((tendsto_const_nhds (x := (1 : ℝ))).add hfirst).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hsecond)).div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hthird) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  convert h using 1; norm_num

/-- Finitely many repair ratios tending to one have product tending to one. -/
theorem repair_product_tendsto_one {ι : Type*} (s : Finset ι)
    (ρ : ι → ℕ → ℝ) (hρ : ∀ i ∈ s, Tendsto (ρ i) atTop (𝓝 1)) :
    Tendsto (fun j => ∏ i ∈ s, ρ i j) atTop (𝓝 1) := by
  simpa using tendsto_finsetProd s hρ

/-- A normalized snapshot ratio tending to one is eventually positive
and bounded by two. This supplies the required family height estimate. -/
theorem snapshot_ratio_eventual_bounds (z : ℕ → ℝ)
    (hz : Tendsto z atTop (𝓝 1)) :
    ∀ᶠ j in atTop, 0 < z j ∧ z j < 2 := by
  exact ((tendsto_order.mp hz).1 0 (by norm_num)).and
    ((tendsto_order.mp hz).2 2 (by norm_num))

/-- A fixed linear relation among asymptotically equal normalized snapshots
has coefficients summing to zero. -/
theorem normalized_relation_coeff_sum_zero {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (Z : ι → ℕ → ℝ) (Z0 : ℕ → ℝ)
    (hZ : ∀ i ∈ s, Tendsto (fun j => Z i j / Z0 j) atTop (𝓝 1))
    (hrel : ∀ᶠ j in atTop, ∑ i ∈ s, c i * Z i j = 0) :
    ∑ i ∈ s, c i = 0 := by
  have hlim : Tendsto (fun j => ∑ i ∈ s, c i * (Z i j / Z0 j))
      atTop (𝓝 (∑ i ∈ s, c i)) := by
    simpa using tendsto_finsetSum s (fun i hi => (hZ i hi).const_mul (c i))
  have he : ∀ᶠ j in atTop, (∑ i ∈ s, c i * (Z i j / Z0 j)) = 0 := by
    filter_upwards [hrel] with j hj
    calc
      _ = (∑ i ∈ s, c i * Z i j) / Z0 j := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hj]; simp
  have hz : Tendsto (fun j => ∑ i ∈ s, c i * (Z i j / Z0 j)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)
  exact tendsto_nhds_unique hlim hz

/-- Successive snapshot ratios tending to one imply every normalized
snapshot tends to one. Nonzero states are explicit, not silently canceled. -/
theorem snapshot_normalized_tendsto (Z : ℕ → ℕ → ℝ) (s : ℕ)
    (hnz : ∀ i ≤ s, ∀ j, Z i j ≠ 0)
    (hstep : ∀ i < s, Tendsto (fun j => Z (i + 1) j / Z i j) atTop (𝓝 1)) :
    ∀ i ≤ s, Tendsto (fun j => Z i j / Z 0 j) atTop (𝓝 1) := by
  intro i
  induction i with
  | zero =>
    intro hi
    have he : (fun j => Z 0 j / Z 0 j) = fun _j => (1 : ℝ) := by
      funext j
      exact div_self (hnz 0 (by omega) j)
    rw [he]
    exact tendsto_const_nhds
  | succ i ih =>
    intro hi
    have ht := (hstep i (by omega)).mul (ih (by omega))
    have he : (fun j => (Z (i + 1) j / Z i j) * (Z i j / Z 0 j)) =
        (fun j => Z (i + 1) j / Z 0 j) := by
      funext j
      field_simp [hnz i (by omega) j, hnz 0 (by omega) j]
    rw [he] at ht
    simpa using ht

end CollatzPrefix
