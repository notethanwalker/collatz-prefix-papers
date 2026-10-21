import CollatzSubspaceBridge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Three-place estimates for integer cluster snapshots

The local identities use the actual integer factorization of the snapshots.
The global lemma explicitly cancels every power of 2 from actual depth and
every power of 3 from snapshot time; only the defect valuations remain.
-/

namespace CollatzPrefix
open scoped BigOperators

/-- Exact 2-adic size of an integer snapshot with a nonzero scaled defect. -/
theorem snapshot_two_norm (a b : ℕ) (D : ℤ) (hD : D ≠ 0) :
    ((padicNorm 2 (((3 : ℤ)^b * 2^a * D : ℤ) : ℚ) : ℚ) : ℝ) =
      ((2 : ℝ)^a * 2^(padicValInt 2 D))⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h22 : padicNorm 2 (2 : ℚ) = (2 : ℚ)⁻¹ := by
    simpa using (padicNorm.padicNorm_p_of_prime (p := 2))
  have h23 : padicNorm 2 (3 : ℚ) = 1 := by
    simpa using (padicNorm.padicNorm_of_prime_of_ne (by decide : 2 ≠ 3))
  have hq : padicNorm 2 (((3 : ℤ)^b * 2^a * D : ℤ) : ℚ) =
      ((2 : ℚ)^a * 2^(padicValInt 2 D))⁻¹ := by
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, padicNorm.mul,
      IsAbsoluteValue.abv_pow, h23, h22, one_pow, one_mul,
      padicNorm.eq_zpow_of_nonzero (Int.cast_ne_zero.mpr hD),
      padicValRat.of_int, Nat.cast_ofNat, zpow_neg, zpow_natCast, inv_pow, mul_inv]
  simpa only [Rat.cast_inv, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] using
    congrArg (fun q : ℚ => (q : ℝ)) hq

/-- The residual integer defect can only decrease the 3-adic size. -/
theorem snapshot_three_norm_le (a b : ℕ) (D : ℤ) :
    ((padicNorm 3 (((3 : ℤ)^b * 2^a * D : ℤ) : ℚ) : ℚ) : ℝ) ≤
      ((3 : ℝ)^b)⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h33 : padicNorm 3 (3 : ℚ) = (3 : ℚ)⁻¹ := by
    simpa using (padicNorm.padicNorm_p_of_prime (p := 3))
  have h32 : padicNorm 3 (2 : ℚ) = 1 := by
    simpa using (padicNorm.padicNorm_of_prime_of_ne (by decide : 3 ≠ 2))
  have hq : padicNorm 3 (((3 : ℤ)^b * 2^a * D : ℤ) : ℚ) ≤ ((3 : ℚ)^b)⁻¹ := by
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, padicNorm.mul,
      IsAbsoluteValue.abv_pow, h32, h33, one_pow, mul_one, inv_pow]
    exact mul_le_of_le_one_right (by positivity) (padicNorm.of_int D)
  have hr := (Rat.cast_le (K := ℝ)).mpr hq
  simpa only [Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat] using hr

/-- Pure product cancellation behind the three-place estimate. -/
theorem three_place_cancellation (s : ℕ) (A B V : Fin (s+1) → ℝ)
    (C : Fin s → ℝ) (N : ℝ) (hA : ∀ i, A i ≠ 0) (hB : ∀ i, B i ≠ 0)
    (hV : ∀ i, V i ≠ 0) (hA0 : A 0 = 1) :
    (∏ i : Fin s, C i * A i.succ * B i.succ) * (N * B 0) *
        (∏ i, (A i * V i)⁻¹) * (∏ i, (B i)⁻¹) =
      N * (∏ i, C i) / (∏ i, V i) := by
  have hPA : (∏ i : Fin s, A i.succ) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hA i.succ)
  have hPB : (∏ i : Fin s, B i.succ) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hB i.succ)
  have hPV : (∏ i, V i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hV i)
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [Fin.prod_univ_succ A, Fin.prod_univ_succ B, hA0, one_mul]
  field_simp [hPA, hPB, hPV, hB 0]

/-- Explicit cancellation estimate for the paper's integer snapshot
factorization. The hypotheses are individual real increment estimates;
there is no assumed global product bound. -/
theorem cluster_three_place_product_bound (s : ℕ) (X D : Fin (s+1) → ℤ)
    (a b : Fin (s+1) → ℕ) (C : Fin s → ℝ) (N : ℝ)
    (hX : ∀ i, X i = (3 : ℤ)^(b i) * 2^(a i) * D i)
    (hD : ∀ i, D i ≠ 0) (ha0 : a 0 = 0)
    (hC : ∀ i, 0 ≤ C i) (hN : 0 ≤ N)
    (hdiff : ∀ i : Fin s, |(X i.succ : ℝ) - (X i.castSucc : ℝ)| ≤
      C i * (2 : ℝ)^(a i.succ) * 3^(b i.succ))
    (hlast : |(X (Fin.last s) : ℝ)| ≤ N * (3 : ℝ)^(b 0)) :
    clusterThreePlaceProduct s X ≤
      N * (∏ i, C i) / (2 : ℝ)^(∑ i, padicValInt 2 (D i)) := by
  have htwo (i : Fin (s+1)) : ((padicNorm 2 (X i : ℚ) : ℚ) : ℝ) =
      ((2 : ℝ)^(a i) * 2^(padicValInt 2 (D i)))⁻¹ := by
    rw [hX i]
    exact snapshot_two_norm (a i) (b i) (D i) (hD i)
  have hthree (i : Fin (s+1)) : ((padicNorm 3 (X i : ℚ) : ℚ) : ℝ) ≤
      ((3 : ℝ)^(b i))⁻¹ := by
    rw [hX i]
    exact snapshot_three_norm_le (a i) (b i) (D i)
  have hdiffprod : (∏ i : Fin s, |(X i.succ : ℝ) - (X i.castSucc : ℝ)|) ≤
      ∏ i : Fin s, C i * (2 : ℝ)^(a i.succ) * 3^(b i.succ) :=
    Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hdiff i)
  have hthreeprod : (∏ i, ((padicNorm 3 (X i : ℚ) : ℚ) : ℝ)) ≤
      ∏ i, ((3 : ℝ)^(b i))⁻¹ := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact_mod_cast padicNorm.nonneg (p := 3) (X i : ℚ)
    · intro i _
      exact hthree i
  have htwo0 : 0 ≤ ∏ i, ((padicNorm 2 (X i : ℚ) : ℚ) : ℝ) := by
    apply Finset.prod_nonneg
    intro i _
    exact_mod_cast padicNorm.nonneg (p := 2) (X i : ℚ)
  have hthree0 : 0 ≤ ∏ i, ((padicNorm 3 (X i : ℚ) : ℚ) : ℝ) := by
    apply Finset.prod_nonneg
    intro i _
    exact_mod_cast padicNorm.nonneg (p := 3) (X i : ℚ)
  have hbounddiff0 : 0 ≤ ∏ i : Fin s, C i * (2 : ℝ)^(a i.succ) * 3^(b i.succ) := by
    apply Finset.prod_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (hC i) (by positivity)) (by positivity)
  unfold clusterThreePlaceProduct
  calc
    _ ≤ (∏ i : Fin s, C i * (2 : ℝ)^(a i.succ) * 3^(b i.succ)) *
        (N * (3 : ℝ)^(b 0)) *
        (∏ i, ((2 : ℝ)^(a i) * 2^(padicValInt 2 (D i)))⁻¹) *
        (∏ i, ((3 : ℝ)^(b i))⁻¹) := by
      rw [← Finset.prod_congr rfl (fun i _ => htwo i)]
      apply mul_le_mul _ hthreeprod hthree0
      · exact mul_nonneg (mul_nonneg hbounddiff0 (by positivity)) htwo0
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul hdiffprod hlast (abs_nonneg _) hbounddiff0) htwo0
    _ = N * (∏ i, C i) / (∏ i, (2 : ℝ)^(padicValInt 2 (D i))) :=
      three_place_cancellation s (fun i => (2 : ℝ)^(a i))
        (fun i => (3 : ℝ)^(b i)) (fun i => (2 : ℝ)^(padicValInt 2 (D i))) C N
        (by intro i; positivity) (by intro i; positivity) (by intro i; positivity)
        (by rw [ha0, pow_zero])
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum]

/-- A covering inequality for defect valuations converts their remaining
power into the reference-depth power, with only a fixed-width loss. -/
theorem cluster_three_place_product_depth_bound (s : ℕ) (X D : Fin (s+1) → ℤ)
    (a b : Fin (s+1) → ℕ) (C : Fin s → ℝ) (N : ℝ) (depth widthLoss : ℕ)
    (hX : ∀ i, X i = (3 : ℤ)^(b i) * 2^(a i) * D i)
    (hD : ∀ i, D i ≠ 0) (ha0 : a 0 = 0)
    (hC : ∀ i, 0 ≤ C i) (hN : 0 ≤ N)
    (hdiff : ∀ i : Fin s, |(X i.succ : ℝ) - (X i.castSucc : ℝ)| ≤
      C i * (2 : ℝ)^(a i.succ) * 3^(b i.succ))
    (hlast : |(X (Fin.last s) : ℝ)| ≤ N * (3 : ℝ)^(b 0))
    (hcover : depth ≤ (∑ i, padicValInt 2 (D i)) + widthLoss) :
    clusterThreePlaceProduct s X ≤
      (N * (∏ i, C i) * (2 : ℝ)^widthLoss) / (2 : ℝ)^depth := by
  apply (cluster_three_place_product_bound s X D a b C N hX hD ha0 hC hN hdiff hlast).trans
  have hCprod : 0 ≤ ∏ i, C i := Finset.prod_nonneg (fun i _ => hC i)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcover
  rw [pow_add] at hp
  have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg hN hCprod)
  nlinarith

end CollatzPrefix
