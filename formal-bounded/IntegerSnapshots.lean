import SpliceRepairs
import ThreePlaceProduct
import ClusterRealBound

/-! Integer snapshots and the exact connection with the normalized orbit defect. -/
namespace CollatzPrefix
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

/-- Clearing the fixed dictionary denominator and terminal power of three. -/
def integerSnapshot (C : RationalPeriodicDictionary ι) (n : ℕ) (c : ℕ → ι)
    (H t : ℕ) : ℤ :=
  (3 : ℤ) ^ (H - t) * 2 ^ actualDepth n t * C.defect (oddOrbit n t) (c t)

theorem integerSnapshot_cast (C : RationalPeriodicDictionary ι) (n : ℕ)
    (c : ℕ → ι) {H t : ℕ} (ht : t ≤ H) :
    (integerSnapshot C n c H t : ℚ) =
      C.denominator * (3 : ℚ) ^ H * normalizedDefect C n c t := by
  have hp : (3 : ℚ) ^ H = 3 ^ (H - t) * 3 ^ t := by
    rw [← pow_add, Nat.sub_add_cancel ht]
  unfold integerSnapshot normalizedDefect RationalPeriodicDictionary.defect
    RationalPeriodicDictionary.value
  push_cast
  rw [hp]
  have hD : (C.denominator : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt C.denominator_pos
  field_simp [hD]
  <;> ring

theorem integerSnapshot_pos (C : RationalPeriodicDictionary ι) {n H t : ℕ}
    (c : ℕ → ι) (hn : 0 < n) (had : Admissible C n H) (ht : t ≤ H) :
    0 < integerSnapshot C n c H t := by
  exact mul_pos (mul_pos (by positivity) (by positivity))
    (C.defect_pos_of_value_lt (admissible_value_lt C hn had ht _))

theorem integerSnapshot_two_norm (C : RationalPeriodicDictionary ι) {n H t : ℕ}
    (c : ℕ → ι) (hn : 0 < n) (had : Admissible C n H) (ht : t ≤ H) :
    ((padicNorm 2 (integerSnapshot C n c H t : ℚ) : ℚ) : ℝ) =
      ((2 : ℝ) ^ actualDepth n t *
        2 ^ padicValInt 2 (C.defect (oddOrbit n t) (c t)))⁻¹ := by
  exact snapshot_two_norm _ _ _
    (ne_of_gt (C.defect_pos_of_value_lt (admissible_value_lt C hn had ht _)))

theorem integerSnapshot_three_norm_le (C : RationalPeriodicDictionary ι)
    (n H t : ℕ) (c : ℕ → ι) :
    ((padicNorm 3 (integerSnapshot C n c H t : ℚ) : ℚ) : ℝ) ≤
      ((3 : ℝ) ^ (H - t))⁻¹ :=
  snapshot_three_norm_le _ _ _

/-- Every genuine reference step leaves the normalized defect unchanged. -/
theorem normalizedDefect_good_step (C : RationalPeriodicDictionary ι)
    (n : ℕ) (c : ℕ → ι) {t : ℕ} (hg : GoodAt C n c t) :
    normalizedDefect C n c (t + 1) = normalizedDefect C n c t := by
  have hh := defect_unchanged (oddOrbit n t : ℚ) (C.value (c t))
    (acceleratedExponent (oddOrbit n t)) (actualDepth n t) t
  rw [oddOrbit_affineStep, hg.1, C.value_step, ← hg.2] at hh
  simpa [normalizedDefect, actualDepth, Finset.sum_range_succ, hg.1] using hh

/-- In particular the snapshots on either side of a good gap agree. -/
theorem normalizedDefect_good_gap (C : RationalPeriodicDictionary ι)
    (n : ℕ) (c : ℕ → ι) {l u : ℕ} (hlu : l ≤ u)
    (hg : ∀ t ∈ Finset.Ico l u, GoodAt C n c t) :
    normalizedDefect C n c u = normalizedDefect C n c l := by
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hlu
  induction w with
  | zero => simp
  | succ w ih =>
    have hg' : ∀ t ∈ Finset.Ico l (l + w), GoodAt C n c t := by
      intro t ht
      exact hg t (by simp only [Finset.mem_Ico] at ht ⊢; omega)
    have hs := normalizedDefect_good_step C n c (hg (l + w) (by simp [Finset.mem_Ico]))
    simpa [Nat.add_assoc] using hs.trans (ih (by omega) hg')

/-- A common clearing factor preserves a nonzero cluster increment. -/
theorem integerSnapshot_sub_ne_zero (C : RationalPeriodicDictionary ι)
    (n : ℕ) (c : ℕ → ι) {H l u : ℕ} (hl : l ≤ H) (hu : u ≤ H)
    (hz : normalizedDefect C n c u - normalizedDefect C n c l ≠ 0) :
    integerSnapshot C n c H u - integerSnapshot C n c H l ≠ 0 := by
  intro he
  have heq : (integerSnapshot C n c H u : ℚ) - integerSnapshot C n c H l = 0 := by
    exact_mod_cast he
  rw [integerSnapshot_cast C n c hu, integerSnapshot_cast C n c hl, ← mul_sub] at heq
  have hfactor : (C.denominator : ℚ) * 3 ^ H ≠ 0 :=
    mul_ne_zero (by exact_mod_cast ne_of_gt C.denominator_pos) (by positivity)
  exact hz ((mul_eq_zero.mp heq).resolve_left hfactor)

/-- A normalized-defect ratio bound gives the required integral height bound. -/
theorem integerSnapshot_abs_le (C : RationalPeriodicDictionary ι) {n H t : ℕ}
    (c : ℕ → ι) (hn : 0 < n) (had : Admissible C n H) (ht : t ≤ H)
    {K : ℚ} (hK : 0 ≤ K)
    (hz : normalizedDefect C n c t ≤ K * normalizedDefect C n c 0) :
    |(integerSnapshot C n c H t : ℚ)| ≤
      K * C.scale * (3 : ℚ) ^ H * (n + 1) := by
  have hfactor : (0 : ℚ) ≤ C.denominator * (3 : ℚ) ^ H := by positivity
  have hmul := mul_le_mul_of_nonneg_left hz hfactor
  have hbound : (C.defect n (c 0) : ℚ) ≤ (C.scale : ℚ) * (n + 1) := by
    have hh : C.defect n (c 0) ≤ (C.scale * (n + 1) : ℕ) :=
      (Int.le_natAbs).trans (by exact_mod_cast C.defect_natAbs_le n (c 0))
    exact_mod_cast hh
  have hinit : (integerSnapshot C n c H 0 : ℚ) =
      (3 : ℚ)^H * C.defect n (c 0) := by
    simp [integerSnapshot, actualDepth]
  rw [abs_of_pos (by exact_mod_cast integerSnapshot_pos C c hn had ht)]
  calc
    _ ≤ K * (integerSnapshot C n c H 0 : ℚ) := by
      rw [integerSnapshot_cast C n c ht, integerSnapshot_cast C n c (Nat.zero_le H)]
      nlinarith [hmul]
    _ = K * ((3 : ℚ)^H * C.defect n (c 0)) := by rw [hinit]
    _ ≤ K * ((3 : ℚ)^H * ((C.scale : ℚ) * (n + 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound (by positivity)) hK
    _ = _ := by ring

/-- Supremum norm version for any finite collection of snapshot times. -/
theorem integerSnapshots_norm_le {κ : Type*} [Fintype κ]
    (C : RationalPeriodicDictionary ι) {n H : ℕ} (c : ℕ → ι)
    (hn : 0 < n) (had : Admissible C n H) (time : κ → ℕ)
    (ht : ∀ i, time i ≤ H) {K : ℚ} (hK : 0 ≤ K)
    (hz : ∀ i, normalizedDefect C n c (time i) ≤ K * normalizedDefect C n c 0) :
    ‖fun i => (integerSnapshot C n c H (time i) : ℝ)‖ ≤
      (K : ℝ) * C.scale * (3 : ℝ)^H * (n + 1) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  exact_mod_cast integerSnapshot_abs_le C c hn had (ht i) hK (hz i)

/-- Every nonempty collection has norm at least one, since its coordinates
are positive integers rather than merely nonzero rationals. -/
theorem one_le_integerSnapshots_norm {κ : Type*} [Fintype κ] [Nonempty κ]
    (C : RationalPeriodicDictionary ι) {n H : ℕ} (c : ℕ → ι)
    (hn : 0 < n) (had : Admissible C n H) (time : κ → ℕ)
    (ht : ∀ i, time i ≤ H) :
    1 ≤ ‖fun i => (integerSnapshot C n c H (time i) : ℝ)‖ := by
  obtain ⟨i⟩ := ‹Nonempty κ›
  have hp : (1 : ℤ) ≤ integerSnapshot C n c H (time i) :=
    integerSnapshot_pos C c hn had (ht i)
  calc
    (1 : ℝ) ≤ (integerSnapshot C n c H (time i) : ℝ) := by exact_mod_cast hp
    _ ≤ |(integerSnapshot C n c H (time i) : ℝ)| := le_abs_self _
    _ ≤ _ := by simpa only [Real.norm_eq_abs] using
      norm_le_pi_norm (fun i => (integerSnapshot C n c H (time i) : ℝ)) i

/-- Clear denominators in an actual normalized increment estimate. -/
theorem integerSnapshot_abs_sub_le (C : RationalPeriodicDictionary ι)
    (n : ℕ) (c : ℕ → ι) {H v u : ℕ} (hv : v ≤ H) (hu : u ≤ H)
    (K : ℚ) (hz : |normalizedDefect C n c u - normalizedDefect C n c v| ≤
      K * ((2 : ℚ)^actualDepth n u / 3^u)) :
    |(integerSnapshot C n c H u : ℚ) - integerSnapshot C n c H v| ≤
      (C.denominator : ℚ) * K * 2^actualDepth n u * 3^(H-u) := by
  rw [integerSnapshot_cast C n c hu, integerSnapshot_cast C n c hv, ← mul_sub,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ C.denominator * 3^H)]
  calc
    _ ≤ ((C.denominator : ℚ) * 3^H) * (K * (2^actualDepth n u / 3^u)) :=
      mul_le_mul_of_nonneg_left hz (by positivity)
    _ = _ := by
      have hp : (3 : ℚ)^H = 3^(H-u) * 3^u := by
        rw [← pow_add, Nat.sub_add_cancel hu]
      rw [hp]
      field_simp
      <;> ring

/-- The actual consecutive cluster-snapshot estimate, including its preceding
possibly very long good gap. The coefficient depends only on the fixed width. -/
theorem integerSnapshot_cluster_bound (C : RationalPeriodicDictionary ι)
    (n : ℕ) (c : ℕ → ι) {H v l : ℕ} (w : ℕ)
    (hvl : v ≤ l) (hH : l+w ≤ H)
    (hg : ∀ t ∈ Finset.Ico v l, GoodAt C n c t) :
    |(integerSnapshot C n c H (l+w) : ℝ) - integerSnapshot C n c H v| ≤
      ((C.denominator : ℝ) * (w : ℝ) * (4 * (referenceAbsCap C : ℝ)+1) * 3^w) *
        (2 : ℝ)^actualDepth n (l+w) * 3^(H-(l+w)) := by
  have hz := normalizedDefect_cluster_bound C n c l w
  rw [normalizedDefect_good_gap C n c hvl hg] at hz
  have hh := integerSnapshot_abs_sub_le C n c (by omega : v ≤ H) hH
    ((w : ℚ) * (4 * referenceAbsCap C+1) * 3^w) hz
  have hcast := (Rat.cast_le (K := ℝ)).mpr hh
  push_cast at hcast
  convert hcast using 1 <;> ring

end CollatzPrefix
