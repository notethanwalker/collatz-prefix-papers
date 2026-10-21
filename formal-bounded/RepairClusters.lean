import CounterexampleExtraction
import SortedRepairs
import Mathlib.Data.Fin.Basic

namespace CollatzPrefix
open Filter

/-- A partition of the repair indices `0,...,r` into nonempty consecutive blocks.
The endpoints are repair indices, not orbit times. -/
structure RepairClusterPartition (r : ℕ) where
  countPred : ℕ
  first : Fin (countPred + 1) → ℕ
  last : Fin (countPred + 1) → ℕ
  first_zero : first 0 = 0
  last_final : last (Fin.last countPred) = r
  ordered : ∀ i, first i ≤ last i
  last_le : ∀ i, last i ≤ r
  consecutive : ∀ i : Fin countPred, last i.castSucc + 1 = first i.succ
  count_le : countPred ≤ r

namespace RepairClusterPartition

/-- Every repair belongs to one of the blocks. -/
theorem covers {r : ℕ} (P : RepairClusterPartition r) {t : ℕ} (ht : t ≤ r) :
    ∃ i, P.first i ≤ t ∧ t ≤ P.last i := by
  induction t with
  | zero => exact ⟨0, by simp [P.first_zero], Nat.zero_le _⟩
  | succ t ih =>
    obtain ⟨i, hfirst, hlast⟩ := ih (by omega)
    by_cases h : t + 1 ≤ P.last i
    · exact ⟨i, by omega, h⟩
    · have he : P.last i = t := by omega
      revert hfirst hlast h he
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro _ _ _ he
        have := P.last_final
        omega
      · intro _ _ _ he
        refine ⟨j.succ, ?_, ?_⟩
        · have := P.consecutive j
          omega
        · have := P.consecutive j
          have := P.ordered j.succ
          omega

/-- A single block, used for a one-repair family. -/
def singleton : RepairClusterPartition 0 where
  countPred := 0
  first := fun _ => 0
  last := fun _ => 0
  first_zero := rfl
  last_final := rfl
  ordered := fun _ => le_rfl
  last_le := fun _ => le_rfl
  consecutive := Fin.elim0
  count_le := le_rfl

/-- Adjoin the next repair to the final block. -/
def extend {r : ℕ} (P : RepairClusterPartition r) : RepairClusterPartition (r + 1) where
  countPred := P.countPred
  first := P.first
  last := Fin.lastCases (r + 1) (fun i => P.last i.castSucc)
  first_zero := P.first_zero
  last_final := by simp
  ordered := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last] using (P.ordered (Fin.last P.countPred)).trans
        (by rw [P.last_final]; omega)
    · simpa using P.ordered j.castSucc
  last_le := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using (P.last_le j.castSucc).trans (Nat.le_succ r)
  consecutive := by intro i; simpa using P.consecutive i
  count_le := P.count_le.trans (Nat.le_succ r)

/-- Start a fresh singleton block at the next repair. -/
def append {r : ℕ} (P : RepairClusterPartition r) : RepairClusterPartition (r + 1) where
  countPred := P.countPred + 1
  first := Fin.lastCases (r + 1) P.first
  last := Fin.lastCases (r + 1) P.last
  first_zero := by
    change Fin.lastCases (r + 1) P.first (Fin.castSucc (0 : Fin (P.countPred + 1))) = 0
    rw [Fin.lastCases_castSucc]
    exact P.first_zero
  last_final := by simp
  ordered := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using P.ordered j
  last_le := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using (P.last_le j).trans (Nat.le_succ r)
  consecutive := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [P.last_final]
    · simpa [← Fin.castSucc_succ] using P.consecutive j
  count_le := Nat.succ_le_succ P.count_le

end RepairClusterPartition

/-- Once every adjacent repair gap is constant or divergent, the repair indices
split into fixed-width clusters separated by divergent gaps. Neither a positive
initial gap nor a positive terminal gap is required. -/
theorem fixed_gap_repair_clusters (r : ℕ) (p : ℕ → ℕ → ℕ)
    (hmono : ∀ n, Monotone (p n))
    (hgap : ∀ i < r,
      (∃ c, ∀ n, p n (i + 1) - p n i = c) ∨
        Tendsto (fun n => p n (i + 1) - p n i) atTop atTop) :
    ∃ P : RepairClusterPartition r,
      (∀ i, ∃ w, ∀ n, p n (P.last i) - p n (P.first i) = w) ∧
      (∀ i : Fin P.countPred,
        Tendsto (fun n => p n (P.first i.succ) - p n (P.last i.castSucc)) atTop atTop) := by
  induction r with
  | zero =>
    refine ⟨RepairClusterPartition.singleton, ?_, ?_⟩
    · intro i; exact ⟨0, fun _ => Nat.sub_self _⟩
    · intro i; exact Fin.elim0 i
  | succ r ih =>
    obtain ⟨P, hw, hd⟩ := ih (fun i hi => hgap i (by omega))
    rcases hgap r (by omega) with ⟨c, hc⟩ | hc
    · refine ⟨P.extend, ?_, ?_⟩
      · change ∀ i : Fin (P.countPred + 1), ∃ w, ∀ n,
            p n (Fin.lastCases (r + 1) (fun j => P.last j.castSucc) i) - p n (P.first i) = w
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · obtain ⟨w, hw⟩ := hw (Fin.last P.countPred)
          refine ⟨w + c, fun n => ?_⟩
          simp only [Fin.lastCases_last]
          have hw := hw n
          rw [P.last_final] at hw
          have h1 := hmono n (P.ordered (Fin.last P.countPred))
          rw [P.last_final] at h1
          have h2 := hmono n (Nat.le_succ r)
          simp only [Nat.succ_eq_add_one] at h2
          have hc := hc n
          omega
        · simpa only [Fin.lastCases_castSucc] using hw j.castSucc
      · change ∀ i : Fin P.countPred, Tendsto (fun n =>
            p n (P.first i.succ) - p n (Fin.lastCases (r + 1) (fun j => P.last j.castSucc) i.castSucc)) atTop atTop
        intro i
        simpa only [Fin.lastCases_castSucc] using hd i
    · refine ⟨P.append, ?_, ?_⟩
      · change ∀ i : Fin (P.countPred + 2), ∃ w, ∀ n,
            p n (Fin.lastCases (r + 1) P.last i) - p n (Fin.lastCases (r + 1) P.first i) = w
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact ⟨0, fun _ => by simp only [Fin.lastCases_last, Nat.sub_self]⟩
        · simpa only [Fin.lastCases_castSucc] using hw j
      · change ∀ i : Fin (P.countPred + 1), Tendsto (fun n =>
            p n (Fin.lastCases (r + 1) P.first i.succ) -
              p n (Fin.lastCases (r + 1) P.last i.castSucc)) atTop atTop
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [P.last_final] using hc
        · simpa [← Fin.castSucc_succ] using hd j

namespace RepairClusterPartition

/-- The first repair of a cluster, as an index of the repair enumeration. -/
def firstIndex {r : ℕ} (P : RepairClusterPartition r) (i : Fin (P.countPred + 1)) : Fin (r + 1) :=
  ⟨P.first i, Nat.lt_succ_of_le ((P.ordered i).trans (P.last_le i))⟩

/-- The last repair of a cluster, as an index of the repair enumeration. -/
def lastIndex {r : ℕ} (P : RepairClusterPartition r) (i : Fin (P.countPred + 1)) : Fin (r + 1) :=
  ⟨P.last i, Nat.lt_succ_of_le (P.last_le i)⟩

/-- Inclusive left orbit-time endpoint. -/
def clusterLeft {r : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ)
    (i : Fin (P.countPred + 1)) : ℕ := p (P.firstIndex i)

/-- Exclusive right endpoint, one step after the final repair. -/
def clusterRight {r : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ)
    (i : Fin (P.countPred + 1)) : ℕ := p (P.lastIndex i) + 1

theorem cluster_nonempty {r : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ)
    (hp : Monotone p) (i : Fin (P.countPred + 1)) :
    P.clusterLeft p i < P.clusterRight p i := by
  have := hp (show P.firstIndex i ≤ P.lastIndex i from P.ordered i)
  unfold clusterLeft clusterRight
  omega

theorem cluster_right_le {r H : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ)
    (hp : ∀ i, p i < H) (i : Fin (P.countPred + 1)) : P.clusterRight p i ≤ H := by
  exact Nat.succ_le_of_lt (hp _)

theorem cluster_ordered {r : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ)
    (hp : StrictMono p) (i : Fin P.countPred) :
    P.clusterRight p i.castSucc ≤ P.clusterLeft p i.succ := by
  have hi : P.lastIndex i.castSucc < P.firstIndex i.succ := by
    change P.last i.castSucc < P.first i.succ
    have := P.consecutive i
    omega
  exact Nat.succ_le_of_lt (hp hi)

/-- Every enumerated repair is in a cluster interval. -/
theorem repair_covered {r : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ)
    (hp : Monotone p) (j : Fin (r + 1)) :
    ∃ i, p j ∈ Finset.Ico (P.clusterLeft p i) (P.clusterRight p i) := by
  obtain ⟨i, hi, hj⟩ := P.covers (Nat.le_of_lt_succ j.isLt)
  refine ⟨i, Finset.mem_Ico.mpr ⟨hp hi, ?_⟩⟩
  exact Nat.lt_succ_of_le (hp hj)

end RepairClusterPartition

/-- Extract a single subsequence and a fixed finite block partition directly
from an arbitrary sequence of increasing repair enumerations. -/
theorem extract_repair_clusters (r : ℕ) (p : ℕ → Fin (r + 1) → ℕ)
    (hp : ∀ n, StrictMono (p n)) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∃ P : RepairClusterPartition r,
      (∀ i, ∃ w, ∀ n,
        P.clusterRight (p (g n)) i - P.clusterLeft (p (g n)) i = w) ∧
      (∀ i : Fin P.countPred,
        Tendsto (fun n => P.clusterLeft (p (g n)) i.succ -
          P.clusterRight (p (g n)) i.castSucc) atTop atTop) := by
  obtain ⟨g, hg, hgap⟩ := finite_constant_or_divergent_subsequence r
    (fun i n => p n i.succ - p n i.castSucc)
  let q : ℕ → ℕ → ℕ := fun n k => p (g n) ⟨min k r, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hq : ∀ n, Monotone (q n) := by
    intro n a b hab
    exact (hp (g n)).monotone (min_le_min_right r hab)
  have hqgap : ∀ i < r, (∃ c, ∀ n, q n (i + 1) - q n i = c) ∨
      Tendsto (fun n => q n (i + 1) - q n i) atTop atTop := by
    intro i hi
    simpa [q, Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left (show i + 1 ≤ r by omega)]
      using hgap ⟨i, hi⟩
  obtain ⟨P, hw, hd⟩ := fixed_gap_repair_clusters r q hq hqgap
  have hfirst (i : Fin (P.countPred + 1)) : P.first i ≤ r := (P.ordered i).trans (P.last_le i)
  have hqfirst (n : ℕ) (i : Fin (P.countPred + 1)) :
      q n (P.first i) = P.clusterLeft (p (g n)) i := by
    simp [q, RepairClusterPartition.clusterLeft, RepairClusterPartition.firstIndex,
      Nat.min_eq_left (hfirst i)]
  have hqlast (n : ℕ) (i : Fin (P.countPred + 1)) :
      q n (P.last i) + 1 = P.clusterRight (p (g n)) i := by
    simp [q, RepairClusterPartition.clusterRight, RepairClusterPartition.lastIndex,
      Nat.min_eq_left (P.last_le i)]
  refine ⟨g, hg, P, ?_, ?_⟩
  · intro i
    obtain ⟨w, hw⟩ := hw i
    refine ⟨w + 1, fun n => ?_⟩
    rw [← hqfirst, ← hqlast]
    have hm := hq n (P.ordered i)
    have := hw n
    omega
  · intro i
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(tendsto_atTop.mp (hd i)) (b + 1)] with n hn
    rw [← hqfirst, ← hqlast]
    omega

/-- Discrete intermediate-value fact for any finite list of boundaries. -/
theorem exists_boundary_interval (s : ℕ) (f : Fin (s + 1) → ℕ) {t : ℕ}
    (hfirst : f 0 ≤ t) (hlast : t < f (Fin.last s)) :
    ∃ i : Fin s, f i.castSucc ≤ t ∧ t < f i.succ := by
  induction s with
  | zero => have he : (Fin.last 0 : Fin 1) = 0 := rfl; rw [he] at hlast; omega
  | succ s ih =>
    by_cases ht : t < f (Fin.last s).castSucc
    · obtain ⟨i, hi, hj⟩ := ih (fun j => f j.castSucc) (by simpa using hfirst) ht
      exact ⟨i.castSucc, hi, by simpa [← Fin.castSucc_succ] using hj⟩
    · exact ⟨Fin.last s, by omega, by simpa using hlast⟩

namespace RepairClusterPartition

/-- Snapshot times: zero, then the right endpoint of each cluster. -/
def snapshot {r : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ) :
    Fin (P.countPred + 2) → ℕ := Fin.cons 0 (P.clusterRight p)

/-- Ends of the good gaps: each cluster's left endpoint, then the prefix end. -/
def gapEnd {r : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ) (H : ℕ) :
    Fin (P.countPred + 2) → ℕ := Fin.lastCases H (P.clusterLeft p)

@[simp] theorem snapshot_zero {r : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ) :
    P.snapshot p 0 = 0 := rfl

@[simp] theorem snapshot_succ {r : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ)
    (i : Fin (P.countPred + 1)) : P.snapshot p i.succ = P.clusterRight p i := rfl

@[simp] theorem snapshot_last {r : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ) :
    P.snapshot p (Fin.last (P.countPred + 1)) = P.clusterRight p (Fin.last P.countPred) := rfl

@[simp] theorem gapEnd_castSucc {r H : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ)
    (i : Fin (P.countPred + 1)) : P.gapEnd p H i.castSucc = P.clusterLeft p i := by
  exact Fin.lastCases_castSucc i

@[simp] theorem gapEnd_last {r H : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ) :
    P.gapEnd p H (Fin.last (P.countPred + 1)) = H := by exact Fin.lastCases_last

theorem snapshot_le_gapEnd {r H : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ)
    (hp : StrictMono p) (hbound : ∀ i, p i < H) (i : Fin (P.countPred + 2)) :
    P.snapshot p i ≤ P.gapEnd p H i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using P.cluster_right_le p hbound (Fin.last P.countPred)
  · rw [P.gapEnd_castSucc]
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · simpa only [Fin.castSucc_succ, snapshot_succ] using P.cluster_ordered p hp k

theorem gapEnd_le {r H : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ)
    (hbound : ∀ i, p i < H) (i : Fin (P.countPred + 2)) : P.gapEnd p H i ≤ H := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simpa [clusterLeft] using (hbound (P.firstIndex j)).le

/-- The fixed width identity in the form used by the actual three-place bound. -/
theorem snapshot_succ_eq_gapEnd_add {r H : ℕ} (P : RepairClusterPartition r)
    (p : Fin (r + 1) → ℕ) (hp : Monotone p) (i : Fin (P.countPred + 1))
    {w : ℕ} (hw : P.clusterRight p i - P.clusterLeft p i = w) :
    P.snapshot p i.succ = P.gapEnd p H i.castSucc + w := by
  rw [snapshot_succ, gapEnd_castSucc]
  have := P.cluster_nonempty p hp i
  omega

/-- The union of cluster intervals and the good-gap intervals covers the whole prefix. -/
theorem cluster_gap_cover {r H : ℕ} (P : RepairClusterPartition r) (p : Fin (r + 1) → ℕ)
    {t : ℕ} (ht : t < H) :
    (∃ i, t ∈ Finset.Ico (P.clusterLeft p i) (P.clusterRight p i)) ∨
    ∃ i, t ∈ Finset.Ico (P.snapshot p i) (P.gapEnd p H i) := by
  by_cases hlast : t < P.clusterRight p (Fin.last P.countPred)
  · obtain ⟨i, hi, hj⟩ := exists_boundary_interval (P.countPred + 1) (P.snapshot p)
      (by simp) (by simpa using hlast)
    by_cases hleft : t < P.clusterLeft p i
    · exact Or.inr ⟨i.castSucc, Finset.mem_Ico.mpr ⟨hi, by simpa using hleft⟩⟩
    · exact Or.inl ⟨i, Finset.mem_Ico.mpr ⟨by omega, by simpa using hj⟩⟩
  · exact Or.inr ⟨Fin.last (P.countPred + 1), Finset.mem_Ico.mpr
      ⟨by simpa using (Nat.le_of_not_gt hlast), by simpa using ht⟩⟩

variable {ι : Type*} [Fintype ι]

/-- Every complementary gap is genuinely good, including initial and terminal gaps. -/
theorem gaps_good {r H n : ℕ} (P : RepairClusterPartition r)
    (C : RationalPeriodicDictionary ι) (c : ℕ → ι) (p : Fin (r + 1) → ℕ)
    (hp : StrictMono p) (hbound : ∀ i, p i < H)
    (henum : ∀ t, t ∈ repairSet C n c H ↔ ∃ i, p i = t)
    (i : Fin (P.countPred + 2)) {t : ℕ}
    (ht : t ∈ Finset.Ico (P.snapshot p i) (P.gapEnd p H i)) : GoodAt C n c t := by
  revert ht
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro ht
    simp only [snapshot_last, gapEnd_last, Finset.mem_Ico] at ht
    have hfinal : P.lastIndex (Fin.last P.countPred) = Fin.last r := by
      apply Fin.ext
      exact P.last_final
    have hafter : p (Fin.last r) < t := by
      have hh := ht.1
      simp only [clusterRight, hfinal] at hh
      omega
    apply goodAt_after_last_repair C n c H hp henum (Nat.succ_pos r) (htH := ht.2)
    convert hafter using 1 <;> congr 1
  · simp only [gapEnd_castSucc]
    refine Fin.cases ?_ (fun k => ?_) j
    · intro ht
      have hzero : P.firstIndex 0 = 0 := by apply Fin.ext; exact P.first_zero
      apply goodAt_before_first_repair C n c H hp hbound henum (Nat.succ_pos r)
      change t < p 0
      simpa only [clusterLeft, hzero] using (Finset.mem_Ico.mp ht).2
    · intro ht
      simp only [Fin.castSucc_succ, snapshot_succ, Finset.mem_Ico] at ht
      apply goodAt_between_repairs C n c H hp hbound henum
        (i := P.lastIndex k.castSucc) (j := P.firstIndex k.succ) (P.consecutive k)
      · exact Nat.lt_of_succ_le ht.1
      · exact ht.2

/-- Each cluster contains a real repair, not just an exceptional interval. -/
theorem contains_repair {r H n : ℕ} (P : RepairClusterPartition r)
    (C : RationalPeriodicDictionary ι) (c : ℕ → ι) (p : Fin (r + 1) → ℕ)
    (hp : StrictMono p) (henum : ∀ t, t ∈ repairSet C n c H ↔ ∃ i, p i = t)
    (i : Fin (P.countPred + 1)) :
    ∃ t ∈ Finset.Ico (P.clusterLeft p i) (P.clusterRight p i), ¬ GoodAt C n c t := by
  refine ⟨P.clusterLeft p i, Finset.mem_Ico.mpr ⟨le_rfl, P.cluster_nonempty p hp.monotone i⟩, ?_⟩
  exact ((mem_repairSet C n c H _).mp ((henum _).mpr ⟨P.firstIndex i, rfl⟩)).2

end RepairClusterPartition

end CollatzPrefix
