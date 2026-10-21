import ActualThreePlace
import SubspacePowerSqueeze
import RepairAsymptotics

namespace CollatzPrefix
open Filter
open scoped Topology BigOperators
variable {ι : Type*} [Fintype ι]

/-- The genuine defects on the admissible domain are positive. -/
private theorem normalizedDefect_pos_smallness (C : RationalPeriodicDictionary ι) {n H t : ℕ}
    (c : ℕ → ι) (hn : 0 < n) (had : Admissible C n H) (ht : t ≤ H) :
    0 < normalizedDefect C n c t := by
  unfold normalizedDefect
  exact mul_pos (by positivity) (sub_pos.mpr (admissible_value_lt C hn had ht _))

/-- A failing actual family with fixed cluster widths satisfies the genuine
three-place Subspace Theorem inequality eventually. -/
theorem actual_cluster_eventually_subspace_small (C : RationalPeriodicDictionary ι)
    (s : ℕ) (n H : ℕ → ℕ) (c : ℕ → ℕ → ι)
    (time gapEnd : ℕ → Fin (s+1) → ℕ) (width : Fin s → ℕ)
    (hn : ∀ j, 0 < n j) (hodd : ∀ j, Odd (n j))
    (had : ∀ j, Admissible C (n j) (H j))
    (hzero : ∀ j, time j 0 = 0) (ht : ∀ j i, time j i ≤ H j)
    (hgap : ∀ j i, time j i ≤ gapEnd j i) (hgapH : ∀ j i, gapEnd j i ≤ H j)
    (hend : ∀ j (i : Fin s), time j i.succ = gapEnd j i.castSucc + width i)
    (hgood : ∀ j i, ∀ t ∈ Finset.Ico (time j i) (gapEnd j i), GoodAt C (n j) (c j) t)
    (hcover : ∀ j t, t < H j →
      (∃ i : Fin s, t ∈ Finset.Ico (gapEnd j i.castSucc) (time j i.succ)) ∨
        ∃ i, t ∈ Finset.Ico (time j i) (gapEnd j i))
    (hlim : ∀ i, Tendsto (fun j =>
      (normalizedDefect C (n j) (c j) (time j i) : ℝ) /
        (normalizedDefect C (n j) (c j) 0 : ℝ)) atTop (𝓝 1))
    (ε : ℝ) (hε : 0 < ε)
    (hex : Tendsto (fun j => (referenceDepth C (c j) (H j) : ℝ) -
      (1+ε)*(Real.log ((n j : ℝ)+1)/Real.log 2)) atTop atTop) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ j in atTop,
      clusterThreePlaceProduct s (fun i => integerSnapshot C (n j) (c j) (H j) (time j i)) ≤
        ‖fun i => (integerSnapshot C (n j) (c j) (H j) (time j i) : ℝ)‖^(-η) := by
  have hZbounds : ∀ᶠ j in atTop, ∀ i,
      normalizedDefect C (n j) (c j) (time j i) ≤ 2 * normalizedDefect C (n j) (c j) 0 := by
    have hh : ∀ i, ∀ᶠ j in atTop,
        (normalizedDefect C (n j) (c j) (time j i) : ℝ) /
          (normalizedDefect C (n j) (c j) 0 : ℝ) < 2 :=
      fun i => (snapshot_ratio_eventual_bounds _ (hlim i)).mono (fun _ h => h.2)
    filter_upwards [Filter.eventually_all.mpr hh] with j hj i
    have hp : (0 : ℝ) < (normalizedDefect C (n j) (c j) 0 : ℝ) := by
      exact_mod_cast normalizedDefect_pos_smallness C (c j) (hn j) (had j) (Nat.zero_le _)
    have hh := ((div_lt_iff₀ hp).mp (hj i)).le
    exact_mod_cast hh
  let A : ℝ := 2 * C.scale * (∏ i, clusterWidthCoefficient C (width i)) *
    (2 : ℝ)^((∑ i, width i) * exponentCap C)
  have hA : 0 ≤ A := by
    have hc : 0 ≤ ∏ i, clusterWidthCoefficient C (width i) :=
      Finset.prod_nonneg (fun i _ => clusterWidthCoefficient_nonneg C _)
    dsimp [A]
    positivity
  let X := fun j i => integerSnapshot C (n j) (c j) (H j) (time j i)
  apply eventually_product_le_height_rpow_neg n H
    (fun j => referenceDepth C (c j) (H j))
    (fun j => ‖fun i => (X j i : ℝ)‖)
    (fun j => clusterThreePlaceProduct s (X j)) ε (2*C.scale) (A+1) hε
  · have hp : (0 : ℝ) < C.scale := by exact_mod_cast C.scale_pos
    positivity
  · linarith
  · exact hex
  · exact Eventually.of_forall (fun j => lt_of_lt_of_le (by norm_num : (0 : ℝ)<1)
      (one_le_integerSnapshots_norm C (c j) (hn j) (had j) (time j) (ht j)))
  · exact Eventually.of_forall (fun j => length_le_referenceDepth C (c j) (H j))
  · filter_upwards [hZbounds] with j hj
    exact_mod_cast integerSnapshots_norm_le C (c j) (hn j) (had j) (time j) (ht j)
      (by norm_num : (0 : ℚ) ≤ 2) hj
  · filter_upwards [hZbounds] with j hj
    have hb := actual_cluster_three_place_fixed_width_bound C (c j) (hn j) (hodd j)
      (had j) s (time j) (gapEnd j) width (hzero j) (ht j) (hgap j) (hgapH j)
      (hend j) (hgood j) (hcover j) (by norm_num : (0 : ℚ) ≤ 2) hj
    have hb' : clusterThreePlaceProduct s (X j) ≤ A*((n j:ℝ)+1)/(2:ℝ)^referenceDepth C (c j) (H j) := by
      simpa only [X, A, Rat.cast_ofNat] using hb
    apply hb'.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith : A ≤ A+1) (by positivity)

end CollatzPrefix
