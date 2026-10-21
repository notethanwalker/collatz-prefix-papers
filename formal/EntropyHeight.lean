import CorrectionDecay
import HeightWindow
import Mathlib.Data.EReal.Basic
import Mathlib.Order.LiminfLimsup

/-!
# The maximum-height exponent of a nonrepeating shortcut Collatz orbit

This file proves the asymptotic theorem for the actual chronological maximum,
not for an abstract sequence assumed to obey the target bound. The lower limit
is taken in the extended reals so that the theorem also covers a possible
infinite lower limit. An explicit equivalence identifies it with the usual
statement that every smaller real exponent is eventually a strict lower bound.
-/

namespace CollatzPrefix

open Filter
open scoped BigOperators Topology

/-- The critical odd-step frequency. -/
noncomputable def criticalFrequency : ℝ := Real.log 2 / Real.log 3

/-- The exponent in the entropy-height theorem, using natural-log entropy. -/
noncomputable def entropyHeightExponent : ℝ :=
  Real.log 2 / Real.binEntropy criticalFrequency

theorem criticalFrequency_bounds : 1 / 2 < criticalFrequency ∧ criticalFrequency < 1 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have h34 : Real.log 3 < 2 * Real.log 2 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) < 2 * 2)
    rw [Real.log_mul (by norm_num) (by norm_num)] at h
    linarith
  constructor
  · rw [criticalFrequency, lt_div_iff₀ h3]
    linarith
  · rw [criticalFrequency, div_lt_one h3]
    exact h23

/-- A lower bias may be used directly in the finite entropy argument. -/
theorem chronological_entropy_of_lower_bias {M r : ℕ} (hM : 0 < M) (n : ℕ)
    (hinj : Function.Injective (fun i : Fin M => shortcut^[i.val] n))
    (hb : ∀ i : Fin M, shortcut^[i.val] n < 2 ^ r)
    {q : ℝ} (hq : 1 / 2 ≤ q) (hq' : q < 1)
    (hqlower : q ≤ (∑ t ∈ Finset.range M, bitReal (orbitBit n t)) / M -
      ((r : ℝ) - 1) / (2 * M)) :
    Real.log M ≤ (r : ℝ) * Real.binEntropy q := by
  apply entropy_packing hM (chronologicalWord n)
    (chronologicalWord_injective n hinj hb) hq hq'
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hn0 : ∀ t, 0 ≤ bitReal (orbitBit n t) := by
    intro t
    cases h : orbitBit n t <;> simp [h, bitReal]
  have hn1 : ∀ t, bitReal (orbitBit n t) ≤ 1 := by
    intro t
    cases h : orbitBit n t <;> simp [h, bitReal]
  have hwin := all_windows_lower (fun t => bitReal (orbitBit n t)) hn0 hn1 M r
  have heq : (∑ i : Fin M, ∑ j : Fin r, bitReal (chronologicalWord n i j)) =
      ∑ j ∈ Finset.range r, ∑ i ∈ Finset.range M, bitReal (orbitBit n (i + j)) := by
    rw [Finset.sum_comm]
    simp only [chronologicalWord]
    simp_rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [dif_pos (Finset.mem_range.mp hj)]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [dif_pos (Finset.mem_range.mp hi)]
  rw [heq]
  have halg : (M : ℝ) * r *
      ((∑ t ∈ Finset.range M, bitReal (orbitBit n t)) / M -
        ((r : ℝ) - 1) / (2 * M)) =
      (r : ℝ) * (∑ t ∈ Finset.range M, bitReal (orbitBit n t)) -
        (r : ℝ) * (r - 1) / 2 := by
    field_simp
    ring
  calc
    (M : ℝ) * r * q ≤ (M : ℝ) * r *
        ((∑ t ∈ Finset.range M, bitReal (orbitBit n t)) / M -
          ((r : ℝ) - 1) / (2 * M)) :=
      mul_le_mul_of_nonneg_left hqlower (by positivity)
    _ = _ := halg
    _ ≤ _ := hwin

/-- The growth identity gives the necessary odd-step bias without assuming
any growth rate for the orbit. -/
theorem orbit_bias_lower (n : ℕ) (hn : 0 < n) {M : ℕ} (hM : 0 < M) :
    criticalFrequency -
        (Real.log n / (M : ℝ) +
          (∑ t ∈ Finset.range M, correction (shortcut^[t] n)) / (M : ℝ)) /
          Real.log 3 ≤
      (∑ t ∈ Finset.range M, bitReal (orbitBit n t)) / (M : ℝ) := by
  have hg := orbit_log_growth n hn M
  have hp : 0 ≤ Real.log (shortcut^[M] n) := Real.log_nonneg (by
    exact_mod_cast orbit_pos n hn M)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  calc
    _ = ((M : ℝ) * Real.log 2 - Real.log n -
        (∑ t ∈ Finset.range M, correction (shortcut^[t] n))) /
        ((M : ℝ) * Real.log 3) := by
      unfold criticalFrequency
      field_simp [ne_of_gt hMr, ne_of_gt h3]
      ring
    _ ≤ ((∑ t ∈ Finset.range M, bitReal (orbitBit n t)) * Real.log 3) /
        ((M : ℝ) * Real.log 3) :=
      (div_le_div_iff_of_pos_right (mul_pos hMr h3)).mpr (by linarith)
    _ = _ := by
      field_simp [ne_of_gt hMr, ne_of_gt h3]
      ring

/-- A conservative lower bias on a putative height-exponent counterexample. -/
noncomputable def heightBiasLower (n : ℕ) (κ : ℝ) (M : ℕ) : ℝ :=
  criticalFrequency -
    (Real.log n / (M : ℝ) +
      (∑ t ∈ Finset.range M, correction (shortcut^[t] n)) / (M : ℝ)) /
        Real.log 3 -
    ((κ / Real.log 2) * (Real.log M / (M : ℝ)) + 1 / (M : ℝ)) / 2

theorem heightBiasLower_tendsto (n : ℕ) (hn : 0 < n)
    (hinj : Function.Injective (fun t : ℕ => shortcut^[t] n)) (κ : ℝ) :
    Tendsto (heightBiasLower n κ) atTop (𝓝 criticalFrequency) := by
  have hnat : Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun M : ℕ => Real.log M / (M : ℝ)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hnat
  have hc := orbit_correction_mean_tendsto_zero n hn hinj
  have hconst := hnat.const_div_atTop (Real.log n)
  have hinv := hnat.const_div_atTop (1 : ℝ)
  have h := ((tendsto_const_nhds (x := criticalFrequency)).sub ((hconst.add hc).div_const (Real.log 3))).sub
    (((hlog.const_mul (κ / Real.log 2)).add hinv).div_const 2)
  simpa only [heightBiasLower, add_zero, zero_add, mul_zero, zero_div, sub_zero] using h

/-- Every real number below the entropy threshold is eventually strictly
below the logarithmic height ratio. -/
theorem eventually_entropy_height_ratio (n : ℕ) (hn : 0 < n)
    (hinj : Function.Injective (fun t : ℕ => shortcut^[t] n))
    (κ : ℝ) (hκ : κ < entropyHeightExponent) :
    ∀ᶠ M : ℕ in atTop, κ < Real.log (orbitHeight n M) / Real.log M := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hfreq := criticalFrequency_bounds
  have hent : 0 < Real.binEntropy criticalFrequency :=
    Real.binEntropy_pos (by linarith [hfreq.1]) hfreq.2
  have hlim := heightBiasLower_tendsto n hn hinj κ
  have hbhalf : ∀ᶠ M : ℕ in atTop, 1 / 2 < heightBiasLower n κ M :=
    (tendsto_order.mp hlim).1 _ hfreq.1
  have hbone : ∀ᶠ M : ℕ in atTop, heightBiasLower n κ M < 1 :=
    (tendsto_order.mp hlim).2 _ hfreq.2
  have hlogtop : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hfactor : Tendsto (fun M : ℕ => κ / Real.log 2 + 2 / Real.log M)
      atTop (𝓝 (κ / Real.log 2)) := by
    simpa using tendsto_const_nhds.add (hlogtop.const_div_atTop (2 : ℝ))
  have hproduct := hfactor.mul (Real.binEntropy_continuous.continuousAt.tendsto.comp hlim)
  have hlimitlt : κ / Real.log 2 * Real.binEntropy criticalFrequency < 1 := by
    have hk := (lt_div_iff₀ hent).mp hκ
    change κ * Real.binEntropy criticalFrequency < Real.log 2 at hk
    calc
      κ / Real.log 2 * Real.binEntropy criticalFrequency =
          (κ * Real.binEntropy criticalFrequency) / Real.log 2 := by ring
      _ < 1 := (div_lt_one h2).mpr hk
  have hsmall : ∀ᶠ M : ℕ in atTop,
      (κ / Real.log 2 + 2 / Real.log M) * Real.binEntropy (heightBiasLower n κ M) < 1 :=
    (tendsto_order.mp hproduct).2 _ hlimitlt
  filter_upwards [hbhalf, hbone, hsmall, eventually_gt_atTop (1 : ℕ)] with M hhalf hone hsmall hM
  have hM0 : 0 < M := by omega
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM0
  have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast hM)
  have hH : 0 < orbitHeight n M := orbitHeight_pos n M hn hM0
  let r := heightWindow (orbitHeight n M)
  have hwindow : ∀ i : Fin M, shortcut^[i.val] n < 2 ^ r := by
    intro i
    exact lt_of_le_of_lt (orbit_le_height n M i.val i.isLt) (height_lt_two_pow_window (orbitHeight n M) hH)
  by_contra hbad
  have hratio : Real.log (orbitHeight n M) / Real.log M ≤ κ := le_of_not_gt hbad
  have hlogH : Real.log (orbitHeight n M) ≤ κ * Real.log M :=
    (div_le_iff₀ hlogM).mp hratio
  have hrbound : (r : ℝ) ≤ (κ / Real.log 2) * Real.log M + 2 := by
    have hw := heightWindow_le_log (orbitHeight n M) hH
    have hdiv := (div_le_div_iff_of_pos_right h2).mpr hlogH
    dsimp [r]
    nlinarith [div_mul_eq_mul_div κ (Real.log 2) (Real.log M)]
  have hbias : heightBiasLower n κ M ≤
      (∑ t ∈ Finset.range M, bitReal (orbitBit n t)) / M -
        ((r : ℝ) - 1) / (2 * M) := by
    have hp := orbit_bias_lower n hn hM0
    have hboundary : ((r : ℝ) - 1) / (2 * M) ≤
        ((κ / Real.log 2) * (Real.log M / (M : ℝ)) + 1 / (M : ℝ)) / 2 := by
      calc
        _ ≤ ((κ / Real.log 2) * Real.log M + 2 - 1) / (2 * M) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by
          field_simp [ne_of_gt hMr, ne_of_gt h2]
          ring
    dsimp [heightBiasLower]
    linarith
  have hfinite := chronological_entropy_of_lower_bias hM0 n
    (fun i j hij => Fin.ext (hinj hij)) hwindow hhalf.le hone hbias
  have hnonneg : 0 ≤ Real.binEntropy (heightBiasLower n κ M) :=
    Real.binEntropy_nonneg (by linarith) hone.le
  have hbound := hfinite.trans (mul_le_mul_of_nonneg_right hrbound hnonneg)
  have hdiv := (div_le_div_iff_of_pos_right hlogM).mpr hbound
  have heq : (((κ / Real.log 2) * Real.log M + 2) *
      Real.binEntropy (heightBiasLower n κ M)) / Real.log M =
      (κ / Real.log 2 + 2 / Real.log M) * Real.binEntropy (heightBiasLower n κ M) := by
    field_simp
  rw [div_self (ne_of_gt hlogM), heq] at hdiv
  linarith

/-- The extended-real lower-limit convention is exactly the usual eventual
lower-bound characterization for real logarithmic height ratios. -/
theorem le_height_liminf_iff (f : ℕ → ℝ) (a : ℝ) :
    (a : EReal) ≤ liminf (fun M => (f M : EReal)) atTop ↔
      ∀ κ < a, ∀ᶠ M : ℕ in atTop, κ < f M := by
  constructor
  · intro h κ hκ
    have he := ((le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)).mp h) (κ : EReal) (by exact_mod_cast hκ)
    simpa only [EReal.coe_lt_coe_iff] using he
  · intro h
    apply (le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)).mpr
    intro b hb
    obtain ⟨κ, hbκ, hκa⟩ := EReal.exists_between_coe_real hb
    have he := h κ (by exact_mod_cast hκa)
    filter_upwards [he] with M hM
    exact hbκ.trans (by exact_mod_cast hM)

/-- Main theorem of the entropy-height paper: the chronological maximum of
an injective positive shortcut Collatz orbit has lower exponent at least
`log 2 / binEntropy (log 2 / log 3)`. -/
theorem entropy_height_liminf (n : ℕ) (hn : 0 < n)
    (hinj : Function.Injective (fun t : ℕ => shortcut^[t] n)) :
    ((Real.log 2 / Real.binEntropy (Real.log 2 / Real.log 3) : ℝ) : EReal) ≤
      liminf (fun M : ℕ =>
        ((Real.log (orbitHeight n M) / Real.log M : ℝ) : EReal)) atTop := by
  apply (le_height_liminf_iff _ _).mpr
  intro κ hκ
  exact eventually_entropy_height_ratio n hn hinj κ hκ

end CollatzPrefix
