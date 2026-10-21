import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Defs

/-!
# Turning snapshot relations into cluster-increment relations

The coefficients are the literal tail sums of the original rational relation.
The summation-by-parts identity and preservation of a nonzero coefficient
vector are algebraic and require no asymptotic or Diophantine hypotheses.
-/

namespace CollatzPrefix
open scoped BigOperators

/-- The coefficient of the `i`th consecutive snapshot increment is the sum
of all coefficients strictly to its right. -/
def tailCoefficient {s : ℕ} (z : Fin (s+1) → ℚ) (i : Fin s) : ℚ :=
  ∑ j : Fin (s+1), if i.val < j.val then z j else 0

@[simp] theorem tailCoefficient_last (s : ℕ) (z : Fin (s+2) → ℚ) :
    tailCoefficient z (Fin.last s) = z (Fin.last (s+1)) := by
  unfold tailCoefficient
  rw [Fin.sum_univ_castSucc]
  have hzero : (∑ j : Fin (s+1), if s < j.val then z j.castSucc else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp only [ite_eq_right (by omega : ¬ s < j.val)]
  simpa using hzero

@[simp] theorem tailCoefficient_castSucc (s : ℕ) (z : Fin (s+2) → ℚ) (i : Fin s) :
    tailCoefficient z i.castSucc =
      tailCoefficient (fun j : Fin (s+1) => z j.castSucc) i + z (Fin.last (s+1)) := by
  unfold tailCoefficient
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, ite_eq_left (by omega : i.val < s+1)]

theorem snapshot_delta_sum (s : ℕ) (Z : Fin (s+1) → ℚ) :
    (∑ i : Fin s, (Z i.succ - Z i.castSucc)) = Z (Fin.last s) - Z 0 := by
  have hfirst := Fin.sum_univ_succ Z
  have hlast := Fin.sum_univ_castSucc Z
  rw [Finset.sum_sub_distrib]
  linarith

/-- Exact discrete summation by parts, without assuming either relation. -/
theorem snapshot_tail_identity (s : ℕ) (z Z : Fin (s+1) → ℚ) :
    (∑ i : Fin s, tailCoefficient z i * (Z i.succ - Z i.castSucc)) =
      (∑ j, z j * Z j) - (∑ j, z j) * Z 0 := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [tailCoefficient_castSucc, tailCoefficient_last]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hi := ih (fun j => z j.castSucc) (fun j => Z j.castSucc)
    have ht := snapshot_delta_sum s (fun j => Z j.castSucc)
    simp only [Fin.castSucc_zero] at hi ht
    rw [Fin.sum_univ_castSucc (fun j => z j * Z j), Fin.sum_univ_castSucc z]
    have hcomm (i : Fin s) : i.castSucc.succ = i.succ.castSucc := by ext; rfl
    simp_rw [hcomm]
    rw [hi, ht]
    simp only [Fin.succ_last]
    ring

/-- A zero-total nonzero snapshot relation has nonzero tail coefficients. -/
theorem tailCoefficient_ne_zero {s : ℕ} (z : Fin (s+1) → ℚ)
    (hz : z ≠ 0) (hsum : ∑ j, z j = 0) : tailCoefficient z ≠ 0 := by
  intro htail
  apply hz
  funext j
  have hi := snapshot_tail_identity s z (Pi.single j 1)
  simp only [htail, Pi.zero_apply, zero_mul, Finset.sum_const_zero, hsum, sub_zero] at hi
  simpa [Pi.single_apply] using hi.symm

/-- The relation used for exceptional-subspace elimination: a nonzero
zero-total snapshot relation becomes a nonzero relation on the increments. -/
theorem snapshot_relation_to_increments {s : ℕ} (z Z : Fin (s+1) → ℚ)
    (hz : z ≠ 0) (hsum : ∑ j, z j = 0) (hrel : ∑ j, z j * Z j = 0) :
    tailCoefficient z ≠ 0 ∧
      ∑ i : Fin s, tailCoefficient z i * (Z i.succ - Z i.castSucc) = 0 := by
  refine ⟨tailCoefficient_ne_zero z hz hsum, ?_⟩
  rw [snapshot_tail_identity, hsum, hrel]
  simp

end CollatzPrefix
