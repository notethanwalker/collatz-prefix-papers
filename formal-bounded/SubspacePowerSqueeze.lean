import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
# From excess depth to a negative power of snapshot height

These estimates derive the small-product hypothesis of the Subspace Theorem
from separate height and product bounds. The negative power is not assumed.
-/

namespace CollatzPrefix
open Filter
open scoped Topology

/-- Divergent excess over a fixed positive proportion absorbs both fixed
constants and a sufficiently small positive multiple of the height exponent. -/
theorem eventually_affine_exponent_nonpos
    (B L : ℕ → ℝ) (ε α C_H C_P : ℝ)
    (hε : 0 < ε) (hα : 0 ≤ α)
    (hL : ∀ᶠ j in atTop, 0 ≤ L j)
    (hEx : Tendsto (fun j => B j - (1 + ε) * L j) atTop atTop) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ j in atTop,
      L j - B j + C_P + η * (α * B j + L j + C_H) ≤ 0 := by
  let K : ℝ := α * (1 + ε) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let η : ℝ := ε / (2 * K)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηK : η * K = ε / 2 := by
    dsimp [η]
    field_simp
  have hηα : η * α ≤ 1 / 2 := by
    have heK : ε * α ≤ K := by dsimp [K]; nlinarith
    have hm := mul_le_mul_of_nonneg_left heK (le_of_lt hη)
    nlinarith
  refine ⟨η, hη, ?_⟩
  have hD0 := (tendsto_atTop.1 hEx) 0
  have hDc := (tendsto_atTop.1 hEx) (2 * (C_P + η * C_H))
  filter_upwards [hL, hD0, hDc] with j hjL hjD0 hjDc
  have h1 : (η * α - 1) * (B j - (1 + ε) * L j) ≤
      -(B j - (1 + ε) * L j) / 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - η * α by linarith) hjD0]
  have h2 : (η * K - ε) * L j ≤ 0 := by
    rw [hηK]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hjL
  have hid : L j - B j + C_P + η * (α * B j + L j + C_H) =
      (η * α - 1) * (B j - (1 + ε) * L j) +
      (η * K - ε) * L j + (C_P + η * C_H) := by
    dsimp [K]
    ring
  rw [hid]
  linarith

/-- A logarithmic version useful independently of the Collatz application. -/
theorem eventually_log_product_add_height_nonpos
    (B L logH logP : ℕ → ℝ) (ε α C_H C_P : ℝ)
    (hε : 0 < ε) (hα : 0 ≤ α)
    (hL : ∀ᶠ j in atTop, 0 ≤ L j)
    (hEx : Tendsto (fun j => B j - (1 + ε) * L j) atTop atTop)
    (hH : ∀ᶠ j in atTop, logH j ≤ α * B j + L j + C_H)
    (hP : ∀ᶠ j in atTop, logP j ≤ L j - B j + C_P) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ j in atTop, logP j + η * logH j ≤ 0 := by
  obtain ⟨η, hη, hb⟩ := eventually_affine_exponent_nonpos B L ε α C_H C_P
    hε hα hL hEx
  refine ⟨η, hη, ?_⟩
  filter_upwards [hH, hP, hb] with j hjH hjP hjb
  exact (add_le_add hjP (mul_le_mul_of_nonneg_left hjH hη.le)).trans hjb

/-- Exponential product bounds imply the actual negative real-power bound.
No positivity hypothesis on `P` is needed: zero products are included directly. -/
theorem eventually_product_le_rpow_neg_of_log_exp_bounds
    (B L H P : ℕ → ℝ) (ε α C_H C_P : ℝ)
    (hε : 0 < ε) (hα : 0 ≤ α)
    (hL : ∀ᶠ j in atTop, 0 ≤ L j)
    (hEx : Tendsto (fun j => B j - (1 + ε) * L j) atTop atTop)
    (hHpos : ∀ᶠ j in atTop, 0 < H j)
    (hH : ∀ᶠ j in atTop, Real.log (H j) ≤ α * B j + L j + C_H)
    (hP : ∀ᶠ j in atTop, P j ≤ Real.exp (L j - B j + C_P)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ j in atTop, P j ≤ (H j) ^ (-η) := by
  obtain ⟨η, hη, hb⟩ := eventually_affine_exponent_nonpos B L ε α C_H C_P
    hε hα hL hEx
  refine ⟨η, hη, ?_⟩
  filter_upwards [hHpos, hH, hP, hb] with j hjHpos hjH hjP hjb
  apply hjP.trans
  rw [Real.rpow_def_of_pos hjHpos]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hjH hη.le
  nlinarith

/-- The precise power squeeze needed by the cluster snapshots. The reference
length `h` is only required to be at most its reference depth `B`; all constants
are fixed in the family. Bounds may hold merely eventually. -/
theorem eventually_product_le_height_rpow_neg
    (n h B : ℕ → ℕ) (height product : ℕ → ℝ)
    (ε C_H C_P : ℝ) (hε : 0 < ε) (hCH : 0 < C_H) (hCP : 0 < C_P)
    (hEx : Tendsto (fun j => (B j : ℝ) - (1 + ε) *
      (Real.log ((n j : ℝ) + 1) / Real.log 2)) atTop atTop)
    (hheight_pos : ∀ᶠ j in atTop, 0 < height j)
    (hdepth : ∀ᶠ j in atTop, h j ≤ B j)
    (hheight : ∀ᶠ j in atTop,
      height j ≤ C_H * (3 : ℝ) ^ h j * ((n j : ℝ) + 1))
    (hproduct : ∀ᶠ j in atTop,
      product j ≤ C_P * ((n j : ℝ) + 1) / (2 : ℝ) ^ B j) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ j in atTop, product j ≤ (height j) ^ (-η) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hEx' : Tendsto (fun j => (B j : ℝ) * Real.log 2 -
      (1 + ε) * Real.log ((n j : ℝ) + 1)) atTop atTop := by
    have hm := hEx.const_mul_atTop hlog2
    convert hm using 1
    funext j
    field_simp
  apply eventually_product_le_rpow_neg_of_log_exp_bounds
    (fun j => (B j : ℝ) * Real.log 2)
    (fun j => Real.log ((n j : ℝ) + 1)) height product
    ε (Real.log 3 / Real.log 2) (Real.log C_H) (Real.log C_P)
    hε (div_nonneg hlog3.le hlog2.le)
    (Eventually.of_forall (fun j => Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg _)))) hEx' hheight_pos
  · filter_upwards [hheight_pos, hheight, hdepth] with j hjpos hjheight hjdepth
    have hN : 0 < (n j : ℝ) + 1 := by positivity
    have hh := Real.log_le_log hjpos hjheight
    rw [Real.log_mul (by positivity) hN.ne',
      Real.log_mul hCH.ne' (by positivity), Real.log_pow] at hh
    have hd : (h j : ℝ) ≤ (B j : ℝ) := by exact_mod_cast hjdepth
    have hm := mul_le_mul_of_nonneg_right hd hlog3.le
    have hid : Real.log 3 / Real.log 2 * ((B j : ℝ) * Real.log 2) =
        (B j : ℝ) * Real.log 3 := by field_simp
    rw [hid]
    linarith
  · filter_upwards [hproduct] with j hjproduct
    have hN : 0 < (n j : ℝ) + 1 := by positivity
    have he : Real.exp (Real.log ((n j : ℝ) + 1) -
        (B j : ℝ) * Real.log 2 + Real.log C_P) =
        C_P * ((n j : ℝ) + 1) / (2 : ℝ) ^ B j := by
      rw [Real.exp_add, Real.exp_sub, Real.exp_log hN, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log hCP]
      ring
    rwa [he]

end CollatzPrefix
