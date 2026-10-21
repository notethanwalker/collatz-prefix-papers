import IntegerSnapshots
import ValuationCover

namespace CollatzPrefix
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

/-- The fixed-width coefficient in the archimedean cluster estimate. -/
def clusterWidthCoefficient (C : RationalPeriodicDictionary ι) (w : ℕ) : ℝ :=
  C.denominator * w * (4 * (referenceAbsCap C : ℝ) + 1) * 3^w

theorem clusterWidthCoefficient_nonneg (C : RationalPeriodicDictionary ι) (w : ℕ) :
    0 ≤ clusterWidthCoefficient C w := by
  have hM : (0 : ℝ) ≤ (referenceAbsCap C : ℝ) := by
    exact_mod_cast referenceAbsCap_nonneg C
  unfold clusterWidthCoefficient
  positivity

/-- Full three-place bound for an actual accelerated prefix cut into clusters
and good gaps. Every analytic and valuation estimate is derived from the actual
orbit; the finite covering hypotheses are exactly those of the cluster cut. -/
theorem actual_cluster_three_place_bound (C : RationalPeriodicDictionary ι)
    {n H : ℕ} (c : ℕ → ι) (hn : 0 < n) (hodd : Odd n)
    (had : Admissible C n H) (s : ℕ)
    (time gapEnd : Fin (s+1) → ℕ) (width : Fin s → ℕ) (P : Finset ℕ)
    (hzero : time 0 = 0) (ht : ∀ i, time i ≤ H)
    (hgap : ∀ i, time i ≤ gapEnd i) (hgapH : ∀ i, gapEnd i ≤ H)
    (hend : ∀ i : Fin s, time i.succ = gapEnd i.castSucc + width i)
    (hgood : ∀ i, ∀ t ∈ Finset.Ico (time i) (gapEnd i), GoodAt C n c t)
    (hcover : ∀ t < H, t ∈ P ∨ ∃ i, t ∈ Finset.Ico (time i) (gapEnd i))
    {K : ℚ} (hK : 0 ≤ K)
    (hz : ∀ i, normalizedDefect C n c (time i) ≤ K * normalizedDefect C n c 0) :
    clusterThreePlaceProduct s (fun i => integerSnapshot C n c H (time i)) ≤
      ((K : ℝ) * C.scale * (∏ i, clusterWidthCoefficient C (width i)) *
        (2 : ℝ)^(P.card * exponentCap C)) * (n+1) /
          (2 : ℝ)^referenceDepth C c H := by
  let X := fun i => integerSnapshot C n c H (time i)
  let D := fun i => C.defect (oddOrbit n (time i)) (c (time i))
  have hval := good_gap_valuation_cover C c hn hodd had time gapEnd P
    hgap hgapH hgood hcover
  have hdepth : referenceDepth C c H ≤
      (∑ i, padicValInt 2 (D i)) + P.card * exponentCap C := by
    dsimp [D]
    omega
  have hN : (0 : ℝ) ≤ (K : ℝ) * C.scale * (n+1) := by
    have hk : (0 : ℝ) ≤ K := by exact_mod_cast hK
    positivity
  have hdiff : ∀ i : Fin s, |(X i.succ : ℝ) - (X i.castSucc : ℝ)| ≤
      clusterWidthCoefficient C (width i) * (2 : ℝ)^actualDepth n (time i.succ) *
        3^(H - time i.succ) := by
    intro i
    have hh := integerSnapshot_cluster_bound C n c (H := H) (width i) (hgap i.castSucc)
      (by rw [← hend i]; exact ht i.succ) (hgood i.castSucc)
    simpa only [X, hend i, clusterWidthCoefficient] using hh
  have hlast : |(X (Fin.last s) : ℝ)| ≤
      ((K : ℝ) * C.scale * (n+1)) * (3 : ℝ)^(H - time 0) := by
    have hh := integerSnapshot_abs_le C c hn had (ht (Fin.last s)) hK (hz (Fin.last s))
    have hc := (Rat.cast_le (K := ℝ)).mpr hh
    push_cast at hc
    rw [hzero, Nat.sub_zero]
    dsimp [X]
    convert hc using 1 <;> ring
  have hh := cluster_three_place_product_depth_bound s X D
    (fun i => actualDepth n (time i)) (fun i => H-time i)
    (fun i => clusterWidthCoefficient C (width i))
    ((K : ℝ) * C.scale * (n+1)) (referenceDepth C c H) (P.card * exponentCap C)
    (fun i => rfl)
    (fun i => ne_of_gt (C.defect_pos_of_value_lt (admissible_value_lt C hn had (ht i) _)))
    (by simp [hzero, actualDepth])
    (fun i => clusterWidthCoefficient_nonneg C _) hN hdiff hlast hdepth
  convert hh using 1 <;> ring

/-- The total number of cluster positions is at most the sum of fixed widths. -/
theorem cluster_positions_card_le (s : ℕ) (left width : Fin s → ℕ) :
    (Finset.univ.biUnion (fun i => Finset.Ico (left i) (left i + width i))).card ≤
      ∑ i, width i := by
  have hh := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin s)))
    (t := fun i => Finset.Ico (left i) (left i + width i))
  simpa using hh

/-- Fixed-width version with the exceptional positions constructed explicitly.
No cardinality or global product estimate is left as an assumption. -/
theorem actual_cluster_three_place_fixed_width_bound (C : RationalPeriodicDictionary ι)
    {n H : ℕ} (c : ℕ → ι) (hn : 0 < n) (hodd : Odd n)
    (had : Admissible C n H) (s : ℕ)
    (time gapEnd : Fin (s+1) → ℕ) (width : Fin s → ℕ)
    (hzero : time 0 = 0) (ht : ∀ i, time i ≤ H)
    (hgap : ∀ i, time i ≤ gapEnd i) (hgapH : ∀ i, gapEnd i ≤ H)
    (hend : ∀ i : Fin s, time i.succ = gapEnd i.castSucc + width i)
    (hgood : ∀ i, ∀ t ∈ Finset.Ico (time i) (gapEnd i), GoodAt C n c t)
    (hcover : ∀ t < H,
      (∃ i : Fin s, t ∈ Finset.Ico (gapEnd i.castSucc) (time i.succ)) ∨
        ∃ i, t ∈ Finset.Ico (time i) (gapEnd i))
    {K : ℚ} (hK : 0 ≤ K)
    (hz : ∀ i, normalizedDefect C n c (time i) ≤ K * normalizedDefect C n c 0) :
    clusterThreePlaceProduct s (fun i => integerSnapshot C n c H (time i)) ≤
      ((K : ℝ) * C.scale * (∏ i, clusterWidthCoefficient C (width i)) *
        (2 : ℝ)^((∑ i, width i) * exponentCap C)) * (n+1) /
          (2 : ℝ)^referenceDepth C c H := by
  classical
  let P := Finset.univ.biUnion (fun i : Fin s =>
    Finset.Ico (gapEnd i.castSucc) (gapEnd i.castSucc + width i))
  have hcov : ∀ t < H, t ∈ P ∨ ∃ i, t ∈ Finset.Ico (time i) (gapEnd i) := by
    intro t ht
    rcases hcover t ht with ⟨i, hi⟩ | hg
    · left
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simpa [hend i] using hi⟩
    · exact Or.inr hg
  have hb := actual_cluster_three_place_bound C c hn hodd had s time gapEnd width P
    hzero ht hgap hgapH hend hgood hcov hK hz
  apply hb.trans
  have hc : P.card ≤ ∑ i, width i := cluster_positions_card_le s
    (fun i => gapEnd i.castSucc) width
  have hp : (2 : ℝ)^(P.card * exponentCap C) ≤
      (2 : ℝ)^((∑ i, width i) * exponentCap C) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right _ hc)
  have hk : (0 : ℝ) ≤ K := by exact_mod_cast hK
  have hpC : 0 ≤ ∏ i, clusterWidthCoefficient C (width i) :=
    Finset.prod_nonneg (fun i _ => clusterWidthCoefficient_nonneg C _)
  gcongr

end CollatzPrefix
