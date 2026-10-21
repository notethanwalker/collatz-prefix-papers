import IntegerSnapshots
import FailureFamilies
import SnapshotRelations
import RepairAsymptotics

namespace CollatzPrefix
open Filter
open scoped Topology BigOperators
variable {ι : Type*} [Fintype ι]

/-- Subspace smallness for actual integer snapshots yields one fixed nonzero
relation on actual cluster increments along a subsequence. Normalized limits
force the coefficient sum to vanish; no relation is assumed. -/
theorem actual_snapshot_increment_relation (C : RationalPeriodicDictionary ι)
    (s : ℕ) (hs : 0 < s) (n H : ℕ → ℕ) (c : ℕ → ℕ → ι)
    (time : ℕ → Fin (s+1) → ℕ)
    (hn : ∀ j, 0 < n j) (had : ∀ j, Admissible C (n j) (H j))
    (ht : ∀ j i, time j i ≤ H j)
    (hlim : ∀ i, Tendsto (fun j =>
      (normalizedDefect C (n j) (c j) (time j i) : ℝ) /
        (normalizedDefect C (n j) (c j) 0 : ℝ)) atTop (𝓝 1))
    {η : ℝ} (hη : 0 < η)
    (hsmall : ∀ᶠ j in atTop,
      clusterThreePlaceProduct s (fun i => integerSnapshot C (n j) (c j) (H j) (time j i)) ≤
        ‖fun i => (integerSnapshot C (n j) (c j) (H j) (time j i) : ℝ)‖^(-η)) :
    ∃ (g : ℕ → ℕ) (q : Fin s → ℚ), StrictMono g ∧ q ≠ 0 ∧
      ∀ j, ∑ i, q i *
        (normalizedDefect C (n (g j)) (c (g j)) (time (g j) i.succ) -
          normalizedDefect C (n (g j)) (c (g j)) (time (g j) i.castSucc)) = 0 := by
  classical
  let X := fun j i => integerSnapshot C (n j) (c j) (H j) (time j i)
  obtain ⟨S, hS, hcover⟩ := cluster_three_place_relations s hs hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  have hrelations : ∀ j, ∃ z ∈ S, ∑ i, z i * (X (N+j) i : ℚ) = 0 := by
    intro j
    apply hcover (X (N+j))
    · intro hz
      have hp := integerSnapshot_pos C (c (N+j)) (hn (N+j)) (had (N+j)) (ht (N+j) 0)
      have he : X (N+j) 0 = 0 := congrFun hz 0
      change integerSnapshot C (n (N+j)) (c (N+j)) (H (N+j)) (time (N+j) 0) = 0 at he
      omega
    · exact hN (N+j) (by omega)
  obtain ⟨z, hzS, f, hf, hrel⟩ := finite_relation_subsequence S
    (fun z j => ∑ i, z i * (X (N+j) i : ℚ) = 0) hrelations
  let g := fun j => N+f j
  have hg : StrictMono g := fun j k hjk => Nat.add_lt_add_left (hf hjk) N
  have hrelZ : ∀ j, ∑ i, z i * normalizedDefect C (n (g j)) (c (g j))
      (time (g j) i) = 0 := by
    intro j
    have hh := hrel j
    change ∑ i, z i * (integerSnapshot C (n (g j)) (c (g j)) (H (g j))
      (time (g j) i) : ℚ) = 0 at hh
    simp_rw [integerSnapshot_cast C (n (g j)) (c (g j)) (ht (g j) _)] at hh
    have he : (∑ i, z i * ((C.denominator : ℚ) * 3^(H (g j)) *
        normalizedDefect C (n (g j)) (c (g j)) (time (g j) i))) =
      ((C.denominator : ℚ) * 3^(H (g j))) *
        (∑ i, z i * normalizedDefect C (n (g j)) (c (g j)) (time (g j) i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he] at hh
    apply (mul_eq_zero.mp hh).resolve_left
    exact mul_ne_zero (by exact_mod_cast ne_of_gt C.denominator_pos) (by positivity)
  have hsumR : ∑ i, (z i : ℝ) = 0 := by
    apply normalized_relation_coeff_sum_zero Finset.univ (fun i => (z i : ℝ))
      (fun i j => (normalizedDefect C (n (g j)) (c (g j)) (time (g j) i) : ℝ))
      (fun j => (normalizedDefect C (n (g j)) (c (g j)) 0 : ℝ))
    · intro i _
      exact (hlim i).comp hg.tendsto_atTop
    · exact Filter.Eventually.of_forall (fun j => by exact_mod_cast hrelZ j)
  have hsum : ∑ i, z i = 0 := by exact_mod_cast hsumR
  refine ⟨g, tailCoefficient z, hg, tailCoefficient_ne_zero z (hS z hzS) hsum, ?_⟩
  intro j
  exact (snapshot_relation_to_increments z
    (fun i => normalizedDefect C (n (g j)) (c (g j)) (time (g j) i))
    (hS z hzS) hsum (hrelZ j)).2

end CollatzPrefix
