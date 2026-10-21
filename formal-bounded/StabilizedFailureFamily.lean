import FailureFamilies
import RepairClusters

namespace CollatzPrefix
open Filter

variable {ι : Type*} [Fintype ι]

/-- Concrete data from an unbounded family after the finite repair labels and
all bounded repair gaps have been stabilized. All prefixes remain globally
minimal, admissible actual prefixes. -/
structure StabilizedFailureFamily (C : RationalPeriodicDictionary ι) (R : ℕ) (F : ℕ → ℝ) where
  sample : ℕ → MinimalRepairPrefix C (R + 1)
  full_budget : ∀ n, repairCount C (sample n).seed (sample n).path (sample n).length = R + 1
  excess : ∀ n : ℕ, (n : ℝ) <
    (referenceDepth C (sample n).path (sample n).length : ℝ) - F (sample n).seed
  position : ℕ → Fin (R + 1) → ℕ
  position_strictMono : ∀ n, StrictMono (position n)
  position_bound : ∀ n i, position n i < (sample n).length
  position_enum : ∀ n t, t ∈ repairSet C (sample n).seed (sample n).path (sample n).length ↔
    ∃ i, position n i = t
  beforeLabel : Fin (R + 1) → ι
  afterLabel : Fin (R + 1) → ι
  before_eq : ∀ n i, (sample n).path (position n i) = beforeLabel i
  after_eq : ∀ n i, (sample n).path (position n i + 1) = afterLabel i
  partition : RepairClusterPartition R
  width : Fin (partition.countPred + 1) → ℕ
  fixed_width : ∀ n i,
    partition.clusterRight (position n) i - partition.clusterLeft (position n) i = width i
  separated : ∀ i : Fin partition.countPred,
    Tendsto (fun n => partition.clusterLeft (position n) i.succ -
      partition.clusterRight (position n) i.castSucc) atTop atTop

/-- The concrete finite-label and fixed-gap extraction. The strict subsequence
is retained explicitly; its pointwise lower bound preserves the growing excess. -/
theorem stabilize_failure_family (C : RationalPeriodicDictionary ι) (R : ℕ) (F : ℕ → ℝ)
    (w : ℕ → MinimalRepairPrefix C (R + 1))
    (hcount : ∀ n, repairCount C (w n).seed (w n).path (w n).length = R + 1)
    (hexcess : ∀ n : ℕ, (n : ℝ) <
      (referenceDepth C (w n).path (w n).length : ℝ) - F (w n).seed) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∃ D : StabilizedFailureFamily C R F,
      ∀ n, D.sample n = w (g n) := by
  classical
  have hp : ∀ n, ∃ p : Fin (R + 1) → ℕ, StrictMono p ∧
      (∀ i, p i < (w n).length) ∧
      (∀ t, t ∈ repairSet C (w n).seed (w n).path (w n).length ↔ ∃ i, p i = t) := by
    intro n
    exact exists_sorted_repairs C (w n).seed (w n).path (w n).length (hcount n)
  choose p hp hbound henum using hp
  let labels : ℕ → (Fin (R + 1) → ι × ι) := fun n i =>
    ((w n).path (p n i), (w n).path (p n i + 1))
  obtain ⟨g, hg, label, hlabel⟩ := finite_label_constant_subsequence labels
  obtain ⟨h, hh, P, hw, hsep⟩ := extract_repair_clusters R (fun n => p (g n)) (fun n => hp (g n))
  choose width hwidth using hw
  let k := g ∘ h
  have hk : StrictMono k := hg.comp hh
  have he : ∀ n : ℕ, (n : ℝ) <
      (referenceDepth C (w (k n)).path (w (k n)).length : ℝ) - F (w (k n)).seed := by
    intro n
    have hn : (n : ℝ) ≤ k n := by exact_mod_cast (hk.le_apply (x := n))
    exact hn.trans_lt (hexcess (k n))
  let D : StabilizedFailureFamily C R F := {
    sample := fun n => w (k n)
    full_budget := fun n => hcount (k n)
    excess := he
    position := fun n => p (k n)
    position_strictMono := fun n => hp (k n)
    position_bound := fun n => hbound (k n)
    position_enum := fun n => henum (k n)
    beforeLabel := fun i => (label i).1
    afterLabel := fun i => (label i).2
    before_eq := by
      intro n i
      exact congrArg Prod.fst (congrFun (hlabel (h n)) i)
    after_eq := by
      intro n i
      exact congrArg Prod.snd (congrFun (hlabel (h n)) i)
    partition := P
    width := width
    fixed_width := fun n i => hwidth i n
    separated := hsep }
  exact ⟨k, hk, D, fun _ => rfl⟩

namespace StabilizedFailureFamily

/-- Further extraction preserves every stabilized combinatorial datum and the
linearly growing excess. This is used when fixing one subspace relation. -/
def subsequence {C : RationalPeriodicDictionary ι} {R : ℕ} {F : ℕ → ℝ}
    (D : StabilizedFailureFamily C R F) (g : ℕ → ℕ) (hg : StrictMono g) :
    StabilizedFailureFamily C R F where
  sample := D.sample ∘ g
  full_budget := fun n => D.full_budget (g n)
  excess := by
    intro n
    have hn : (n : ℝ) ≤ g n := by exact_mod_cast (hg.le_apply (x := n))
    exact hn.trans_lt (D.excess (g n))
  position := D.position ∘ g
  position_strictMono := fun n => D.position_strictMono (g n)
  position_bound := fun n => D.position_bound (g n)
  position_enum := fun n => D.position_enum (g n)
  beforeLabel := D.beforeLabel
  afterLabel := D.afterLabel
  before_eq := fun n => D.before_eq (g n)
  after_eq := fun n => D.after_eq (g n)
  partition := D.partition
  width := D.width
  fixed_width := fun n => D.fixed_width (g n)
  separated := fun i => (D.separated i).comp hg.tendsto_atTop

@[simp] theorem subsequence_sample {C : RationalPeriodicDictionary ι} {R : ℕ} {F : ℕ → ℝ}
    (D : StabilizedFailureFamily C R F) (g : ℕ → ℕ) (hg : StrictMono g) (n : ℕ) :
    (D.subsequence g hg).sample n = D.sample (g n) := rfl

@[simp] theorem subsequence_position {C : RationalPeriodicDictionary ι} {R : ℕ} {F : ℕ → ℝ}
    (D : StabilizedFailureFamily C R F) (g : ℕ → ℕ) (hg : StrictMono g) (n : ℕ) :
    (D.subsequence g hg).position n = D.position (g n) := rfl

/-- Snapshot times associated to a stabilized failure family. -/
def time {C : RationalPeriodicDictionary ι} {R : ℕ} {F : ℕ → ℝ}
    (D : StabilizedFailureFamily C R F) (n : ℕ) : Fin (D.partition.countPred + 2) → ℕ :=
  D.partition.snapshot (D.position n)

/-- Good-gap ends associated to a stabilized failure family. -/
def gapEnd {C : RationalPeriodicDictionary ι} {R : ℕ} {F : ℕ → ℝ}
    (D : StabilizedFailureFamily C R F) (n : ℕ) : Fin (D.partition.countPred + 2) → ℕ :=
  D.partition.gapEnd (D.position n) (D.sample n).length

@[simp] theorem time_zero {C : RationalPeriodicDictionary ι} {R : ℕ} {F : ℕ → ℝ}
    (D : StabilizedFailureFamily C R F) (n : ℕ) : D.time n 0 = 0 := rfl

theorem time_le_gapEnd {C : RationalPeriodicDictionary ι} {R : ℕ} {F : ℕ → ℝ}
    (D : StabilizedFailureFamily C R F) (n : ℕ) (i : Fin (D.partition.countPred + 2)) :
    D.time n i ≤ D.gapEnd n i :=
  D.partition.snapshot_le_gapEnd _ (D.position_strictMono n) (D.position_bound n) i

theorem gapEnd_le_length {C : RationalPeriodicDictionary ι} {R : ℕ} {F : ℕ → ℝ}
    (D : StabilizedFailureFamily C R F) (n : ℕ) (i : Fin (D.partition.countPred + 2)) :
    D.gapEnd n i ≤ (D.sample n).length :=
  D.partition.gapEnd_le _ (D.position_bound n) i

theorem time_le_length {C : RationalPeriodicDictionary ι} {R : ℕ} {F : ℕ → ℝ}
    (D : StabilizedFailureFamily C R F) (n : ℕ) (i : Fin (D.partition.countPred + 2)) :
    D.time n i ≤ (D.sample n).length := (D.time_le_gapEnd n i).trans (D.gapEnd_le_length n i)

theorem next_time {C : RationalPeriodicDictionary ι} {R : ℕ} {F : ℕ → ℝ}
    (D : StabilizedFailureFamily C R F) (n : ℕ) (i : Fin (D.partition.countPred + 1)) :
    D.time n i.succ = D.gapEnd n i.castSucc + D.width i :=
  D.partition.snapshot_succ_eq_gapEnd_add _ (D.position_strictMono n).monotone i (D.fixed_width n i)

theorem good_gap {C : RationalPeriodicDictionary ι} {R : ℕ} {F : ℕ → ℝ}
    (D : StabilizedFailureFamily C R F) (n : ℕ) (i : Fin (D.partition.countPred + 2))
    {t : ℕ} (ht : t ∈ Finset.Ico (D.time n i) (D.gapEnd n i)) :
    GoodAt C (D.sample n).seed (D.sample n).path t :=
  D.partition.gaps_good C (D.sample n).path _ (D.position_strictMono n)
    (D.position_bound n) (D.position_enum n) i ht

theorem cover {C : RationalPeriodicDictionary ι} {R : ℕ} {F : ℕ → ℝ}
    (D : StabilizedFailureFamily C R F) (n : ℕ) {t : ℕ} (ht : t < (D.sample n).length) :
    (∃ i : Fin (D.partition.countPred + 1), t ∈ Finset.Ico (D.gapEnd n i.castSucc) (D.time n i.succ)) ∨
    ∃ i, t ∈ Finset.Ico (D.time n i) (D.gapEnd n i) := by
  simpa [time, gapEnd] using D.partition.cluster_gap_cover (D.position n) ht

theorem cluster_has_repair {C : RationalPeriodicDictionary ι} {R : ℕ} {F : ℕ → ℝ}
    (D : StabilizedFailureFamily C R F) (n : ℕ) (i : Fin (D.partition.countPred + 1)) :
    ∃ t ∈ Finset.Ico (D.gapEnd n i.castSucc) (D.time n i.succ),
      ¬ GoodAt C (D.sample n).seed (D.sample n).path t := by
  simpa [time, gapEnd] using D.partition.contains_repair C (D.sample n).path (D.position n)
    (D.position_strictMono n) (D.position_enum n) i

end StabilizedFailureFamily
end CollatzPrefix
