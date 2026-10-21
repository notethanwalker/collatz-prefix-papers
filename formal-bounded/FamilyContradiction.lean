import DepthBoundDefinitions
import StabilizedFailureFamily
import RepairClusterAssignment
import ActualRepairRatios
import ActualSubspaceSmallness
import ActualSnapshotRelations
import RepairUnitExpansion

namespace CollatzPrefix
open Filter
open scoped Topology BigOperators
variable {ι : Type*} [Fintype ι]

/-- An actual, minimally referenced failure family is impossible. This is the
complete induction step: all valuation, Subspace, and S-unit hypotheses are
proved from the stabilized actual prefix data. -/
theorem stabilized_failure_family_impossible (C : RationalPeriodicDictionary ι)
    (hinj : Function.Injective C.value) (R : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hind : PrefixDepthBound C R ε)
    (D : StabilizedFailureFamily C R (repairDepthProfile ε)) : False := by
  classical
  obtain ⟨K, hK⟩ := hind
  let seed := fun j => (D.sample j).seed
  let len := fun j => (D.sample j).length
  let refs := fun j => (D.sample j).path
  have hex : Tendsto (fun j => (referenceDepth C (refs j) (len j) : ℝ) -
      repairDepthProfile ε (seed j)) atTop atTop := by
    apply tendsto_atTop_mono (fun j => (D.excess j).le)
    exact tendsto_natCast_atTop_atTop
  have hright : ∀ i, Tendsto (fun j => oddOrbit (seed j) (D.position j i+1)) atTop atTop := by
    intro i
    exact (repair_neighbors_tendsto_of_divergent_excess C R (repairDepthProfile ε) K hK
      seed len (fun j => D.position j i) refs
      (fun j => (D.sample j).positive) (fun j => (D.sample j).odd)
      (fun j => (D.sample j).admissible) (fun j => (D.sample j).budget)
      (fun j => D.position_bound j i)
      (fun j => ((mem_repairSet C _ _ _ _).mp ((D.position_enum j _).mpr ⟨i, rfl⟩)).2)
      hex).2
  have hrepair := actual_sorted_repairs_normalized_tendsto C seed len refs (R+1)
    D.position D.beforeLabel D.afterLabel (fun j => (D.sample j).positive)
    (fun j => (D.sample j).admissible) D.position_strictMono D.position_bound
    D.position_enum D.before_eq D.after_eq hright
  have hlim : ∀ i, Tendsto (fun j =>
      (normalizedDefect C (seed j) (refs j) (D.time j i) : ℝ) /
        (normalizedDefect C (seed j) (refs j) 0 : ℝ)) atTop (𝓝 1) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · have he : (fun j => (normalizedDefect C (seed j) (refs j) (D.time j 0) : ℝ) /
          (normalizedDefect C (seed j) (refs j) 0 : ℝ)) = fun _ => (1 : ℝ) := by
        funext j
        rw [D.time_zero]
        apply div_self
        exact_mod_cast ne_of_gt (normalizedDefect_pos C (refs j) (D.sample j).positive
          (D.sample j).admissible (Nat.zero_le _))
      rw [he]
      exact tendsto_const_nhds
    · exact (hrepair (D.partition.lastIndex k)).2
  obtain ⟨η, hη, hsmall⟩ := actual_cluster_eventually_subspace_small C
    (D.partition.countPred+1) seed len refs D.time D.gapEnd D.width
    (fun j => (D.sample j).positive) (fun j => (D.sample j).odd)
    (fun j => (D.sample j).admissible) D.time_zero D.time_le_length
    D.time_le_gapEnd D.gapEnd_le_length D.next_time
    (fun j i _ ht => D.good_gap j i ht) (fun j _ ht => D.cover j ht)
    hlim ε hε hex
  obtain ⟨g, q, hg, hq, hrel⟩ := actual_snapshot_increment_relation C
    (D.partition.countPred+1) (Nat.succ_pos _) seed len refs D.time
    (fun j => (D.sample j).positive) (fun j => (D.sample j).admissible)
    D.time_le_length hlim hη hsmall
  have hgaps (j : ℕ) (i : Fin (D.partition.countPred+1)) :
      normalizedDefect C (seed (g j)) (refs (g j)) (D.partition.clusterLeft (D.position (g j)) i) =
        normalizedDefect C (seed (g j)) (refs (g j)) (D.time (g j) i.castSucc) := by
    have hh := normalizedDefect_good_gap C (seed (g j)) (refs (g j))
      (D.time_le_gapEnd (g j) i.castSucc) (fun _ ht => D.good_gap (g j) i.castSucc ht)
    simpa only [StabilizedFailureFamily.gapEnd, RepairClusterPartition.gapEnd_castSucc] using hh
  have hclusterrel : ∀ j, ∑ i, q i *
      (normalizedDefect C (seed (g j)) (refs (g j)) (D.partition.clusterRight (D.position (g j)) i) -
        normalizedDefect C (seed (g j)) (refs (g j)) (D.partition.clusterLeft (D.position (g j)) i)) = 0 := by
    intro j
    calc
      _ = ∑ i, q i * (normalizedDefect C (seed (g j)) (refs (g j)) (D.time (g j) i.succ) -
          normalizedDefect C (seed (g j)) (refs (g j)) (D.time (g j) i.castSucc)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hgaps j i]
        rfl
      _ = 0 := hrel j
  have hcover : ∀ j k t,
      D.partition.clusterLeft (D.position (g j)) k ≤ t ∧
        t < D.partition.clusterRight (D.position (g j)) k ∧
          ¬ GoodAt C (seed (g j)) (refs (g j)) t ↔
        ∃ i, D.partition.clusterOf i = k ∧ D.position (g j) i = t := by
    intro j k t
    constructor
    · rintro ⟨hlo, hhi, hbad⟩
      have htH : t < len (g j) := hhi.trans_le
        (D.partition.cluster_right_le _ (D.position_bound (g j)) k)
      obtain ⟨i, hi⟩ := (D.position_enum (g j) t).mp
        ((mem_repairSet C _ _ _ _).mpr ⟨htH, hbad⟩)
      refine ⟨i, ?_, hi⟩
      apply (D.partition.mem_cluster_iff_clusterOf_eq _ (D.position_strictMono (g j)) i k).mp
      simpa [hi] using Finset.mem_Ico.mpr ⟨hlo, hhi⟩
    · rintro ⟨i, hik, rfl⟩
      have hm := (D.partition.mem_cluster_iff_clusterOf_eq _
        (D.position_strictMono (g j)) i k).mpr hik
      exact ⟨(Finset.mem_Ico.mp hm).1, (Finset.mem_Ico.mp hm).2,
        ((mem_repairSet C _ _ _ _).mp ((D.position_enum (g j) _).mpr ⟨i, rfl⟩)).2⟩
  obtain ⟨k, hk⟩ : ∃ k, q k ≠ 0 := by
    by_contra! hh
    exact hq (funext hh)
  have hnonzero : ∀ j, q k *
      (normalizedDefect C (seed (g j)) (refs (g j)) (D.partition.clusterRight (D.position (g j)) k) -
        normalizedDefect C (seed (g j)) (refs (g j)) (D.partition.clusterLeft (D.position (g j)) k)) ≠ 0 := by
    intro j
    apply mul_ne_zero hk
    have hrep := D.cluster_has_repair (g j) k
    obtain ⟨t, ht, hbad⟩ := hrep
    have hh := minimal_repairs_cluster_increment_ne_zero C hinj (seed (g j)) (len (g j))
      (refs (g j)) (D.sample (g j)).odd (D.sample (g j)).minimal
      (D.gapEnd (g j) k.castSucc) (D.width k)
      (by rw [← D.next_time]; exact D.time_le_length _ _)
      ⟨t, (Finset.mem_Ico.mp ht).1, by rw [← D.next_time]; exact (Finset.mem_Ico.mp ht).2, hbad⟩
    rw [← D.next_time (g j) k] at hh
    simpa only [StabilizedFailureFamily.time, StabilizedFailureFamily.gapEnd,
      RepairClusterPartition.snapshot_succ, RepairClusterPartition.gapEnd_castSucc] using hh
  apply no_separated_actual_cluster_relation C (fun j => seed (g j)) (fun j => refs (g j))
    D.partition.clusterOf q D.beforeLabel D.afterLabel (fun j => D.position (g j))
    (fun j => D.partition.clusterLeft (D.position (g j)))
    (fun j => D.partition.clusterRight (D.position (g j)))
    (fun j i => (D.partition.cluster_nonempty _ (D.position_strictMono (g j)).monotone i).le)
    (fun j => (D.position_strictMono (g j)).injective) hcover
    (fun j => D.before_eq (g j)) (fun j => D.after_eq (g j)) hclusterrel
    (fun i j hij => (D.partition.cross_cluster_separation D.position D.position_strictMono
      D.separated i j hij).comp hg.tendsto_atTop) k hnonzero

end CollatzPrefix
