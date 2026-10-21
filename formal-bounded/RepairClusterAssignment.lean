import RepairClusters
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Int.NatAbs

namespace CollatzPrefix
open Filter

namespace RepairClusterPartition

variable {r : ℕ} (P : RepairClusterPartition r)

/-- The left repair-index endpoints are strictly increasing. -/
theorem first_strictMono : StrictMono P.first := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have := P.ordered i.castSucc
  have := P.consecutive i
  omega

/-- The right repair-index endpoints are strictly increasing. -/
theorem last_strictMono : StrictMono P.last := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have := P.ordered i.succ
  have := P.consecutive i
  omega

/-- Every earlier block ends before a later block begins. -/
theorem last_lt_first_of_lt {i j : Fin (P.countPred + 1)} (hij : i < j) :
    P.last i < P.first j := by
  have hi : i.val < P.countPred := by have := j.isLt; exact Nat.lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt)
  let k : Fin P.countPred := ⟨i.val, hi⟩
  have hcast : k.castSucc = i := Fin.ext rfl
  have hsucc : k.succ ≤ j := by change i.val + 1 ≤ j.val; exact hij
  have hcon := P.consecutive k
  have hmono := P.first_strictMono.monotone hsucc
  rw [hcast] at hcon
  omega

/-- A repair index cannot lie in two different blocks. -/
theorem block_unique {t : ℕ} {i j : Fin (P.countPred + 1)}
    (hi : P.first i ≤ t ∧ t ≤ P.last i)
    (hj : P.first j ≤ t ∧ t ≤ P.last j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := P.last_lt_first_of_lt h; omega
  · exact h
  · have := P.last_lt_first_of_lt h; omega

/-- The unique cluster containing an enumerated repair. -/
noncomputable def clusterOf (j : Fin (r + 1)) : Fin (P.countPred + 1) :=
  Classical.choose (P.covers (Nat.le_of_lt_succ j.isLt))

theorem clusterOf_spec (j : Fin (r + 1)) :
    P.first (P.clusterOf j) ≤ j.val ∧ j.val ≤ P.last (P.clusterOf j) :=
  Classical.choose_spec (P.covers (Nat.le_of_lt_succ j.isLt))

theorem clusterOf_eq_iff (j : Fin (r + 1)) (i : Fin (P.countPred + 1)) :
    P.clusterOf j = i ↔ P.first i ≤ j.val ∧ j.val ≤ P.last i := by
  constructor
  · intro h; simpa [h] using P.clusterOf_spec j
  · intro h; exact P.block_unique (P.clusterOf_spec j) h

/-- Membership in a cluster's orbit-time interval is exactly its index assignment. -/
theorem mem_cluster_iff_clusterOf_eq (p : Fin (r + 1) → ℕ) (hp : StrictMono p)
    (j : Fin (r + 1)) (i : Fin (P.countPred + 1)) :
    p j ∈ Finset.Ico (P.clusterLeft p i) (P.clusterRight p i) ↔ P.clusterOf j = i := by
  rw [P.clusterOf_eq_iff, Finset.mem_Ico]
  change (p (P.firstIndex i) ≤ p j ∧ p j < p (P.lastIndex i) + 1) ↔ _
  rw [Nat.lt_succ_iff, hp.le_iff_le, hp.le_iff_le]
  rfl

/-- Repairs in strictly ordered clusters have strictly ordered repair indices. -/
theorem index_lt_of_clusterOf_lt {i j : Fin (r + 1)}
    (hij : P.clusterOf i < P.clusterOf j) : i < j := by
  have hi := P.clusterOf_spec i
  have hj := P.clusterOf_spec j
  have h := P.last_lt_first_of_lt hij
  change i.val < j.val
  omega

/-- Divergence of the adjacent inter-cluster gaps separates every two repairs
assigned to different clusters. -/
theorem cross_cluster_separation (p : ℕ → Fin (r + 1) → ℕ)
    (hp : ∀ n, StrictMono (p n))
    (hgap : ∀ k : Fin P.countPred,
      Tendsto (fun n => P.clusterLeft (p n) k.succ -
        P.clusterRight (p n) k.castSucc) atTop atTop)
    (i j : Fin (r + 1)) (hij : P.clusterOf i ≠ P.clusterOf j) :
    Tendsto (fun n => ((p n i : ℤ) - p n j).natAbs) atTop atTop := by
  have hordered : ∀ a b : Fin (r + 1), P.clusterOf a < P.clusterOf b →
      Tendsto (fun n => ((p n a : ℤ) - p n b).natAbs) atTop atTop := by
    intro a b hab
    have ha : (P.clusterOf a).val < P.countPred :=
      Nat.lt_of_lt_of_le hab (Nat.le_of_lt_succ (P.clusterOf b).isLt)
    let k : Fin P.countPred := ⟨(P.clusterOf a).val, ha⟩
    have hcast : k.castSucc = P.clusterOf a := Fin.ext rfl
    have hsucc : k.succ ≤ P.clusterOf b := by exact hab
    apply tendsto_atTop.mpr
    intro m
    filter_upwards [(tendsto_atTop.mp (hgap k)) m] with n hn
    have ha' : p n a ≤ p n (P.lastIndex k.castSucc) := by
      apply (hp n).monotone
      change a.val ≤ P.last k.castSucc
      rw [hcast]
      exact (P.clusterOf_spec a).2
    have hb' : p n (P.firstIndex k.succ) ≤ p n b := by
      apply (hp n).monotone
      change P.first k.succ ≤ b.val
      exact (P.first_strictMono.monotone hsucc).trans (P.clusterOf_spec b).1
    have hab' : p n a ≤ p n b := (hp n).monotone (le_of_lt (P.index_lt_of_clusterOf_lt hab))
    rw [Int.natAbs_natCast_sub_natCast_of_le hab']
    change m ≤ p n (P.firstIndex k.succ) - (p n (P.lastIndex k.castSucc) + 1) at hn
    omega
  rcases lt_or_gt_of_ne hij with h | h
  · exact hordered i j h
  · have heq : (fun n => ((p n i : ℤ) - p n j).natAbs) =
        (fun n => ((p n j : ℤ) - p n i).natAbs) := by
      funext n
      rw [← Int.natAbs_neg, neg_sub]
    rw [heq]
    exact hordered j i h

end RepairClusterPartition
end CollatzPrefix
