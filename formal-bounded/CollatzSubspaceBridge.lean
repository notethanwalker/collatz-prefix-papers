import DiophantineApproximation.RepetitionSubspaces
import DiophantineApproximation.RationalPlaces
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The Subspace Theorem for Collatz cluster snapshots

The only deep input is the proved rational specialization of the p-adic
Subspace Theorem in Ralf Stephan's Apache-2.0 licensed Subspace-Theorems
repository, pinned by the surrounding package. We specialize its infinite
forms to consecutive differences and the final coordinate, and its finite
places to precisely 2 and 3. No Collatz conclusion or Diophantine assertion
is introduced as an assumption or axiom here.
-/

open Module NumberField
open scoped BigOperators

namespace CollatzPrefix

def clusterForms (s : ℕ) : Fin (s + 1) → Dual ℚ (Fin (s + 1) → ℚ) :=
  Fin.lastCases (LinearMap.proj (Fin.last s))
    (fun i : Fin s => (LinearMap.proj i.succ : Dual ℚ (Fin (s+1) → ℚ)) - LinearMap.proj i.castSucc)

@[simp] theorem clusterForms_last (s : ℕ) (x : Fin (s+1) → ℚ) :
    clusterForms s (Fin.last s) x = x (Fin.last s) := by simp [clusterForms]

@[simp] theorem clusterForms_castSucc (s : ℕ) (i : Fin s) (x : Fin (s+1) → ℚ) :
    clusterForms s i.castSucc x = x i.succ - x i.castSucc := by simp [clusterForms]

theorem clusterForms_transform_injective (s : ℕ) :
    Function.Injective (LinearMap.pi (clusterForms s)) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  ext i
  induction i using Fin.reverseInduction with
  | last =>
    have hh := congrFun hx (Fin.last s)
    simpa using hh
  | cast i ih =>
    have hh := congrFun hx i.castSucc
    change clusterForms s i.castSucc x = 0 at hh
    rw [clusterForms_castSucc] at hh
    change x i.succ = 0 at ih
    change x i.castSucc = 0
    linarith

theorem clusterForms_linearIndependent (s : ℕ) : LinearIndependent ℚ (clusterForms s) := by
  have hi := LinearMap.dualMap_injective_of_surjective
    (LinearMap.surjective_of_injective (clusterForms_transform_injective s))
  have h := ((Pi.basisFun ℚ (Fin (s+1))).dualBasis.linearIndependent).map'
    (LinearMap.pi (clusterForms s)).dualMap (LinearMap.ker_eq_bot.mpr hi)
  convert h using 1
  funext i
  ext x
  simp

/-- The exact three-place product occurring in the cluster argument. -/
noncomputable def clusterThreePlaceProduct (s : ℕ) (X : Fin (s+1) → ℤ) : ℝ :=
  (∏ i : Fin s, |(X i.succ : ℝ) - (X i.castSucc : ℝ)|) *
    |(X (Fin.last s) : ℝ)| *
    (∏ i, ((padicNorm 2 (X i : ℚ) : ℚ) : ℝ)) *
    (∏ i, ((padicNorm 3 (X i : ℚ) : ℚ) : ℝ))

theorem clusterForms_arch_product (s : ℕ) (X : Fin (s+1) → ℤ) :
    (∏ i, Rat.infinitePlace.1
      (clusterForms s i (fun k => algebraMap ℚ ℚ (X k : ℚ)))) =
      (∏ i : Fin s, |(X i.succ : ℝ) - (X i.castSucc : ℝ)|) *
        |(X (Fin.last s) : ℝ)| := by
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [Fin.prod_univ_castSucc]
  simp only [clusterForms_castSucc, clusterForms_last,
    ← InfinitePlace.coe_apply, Rat.infinitePlace_apply,
    Rat.cast_abs, Rat.cast_sub, Rat.cast_intCast]

theorem integer_iSup_abs_eq_norm {ι : Type*} [Fintype ι] [Nonempty ι] (X : ι → ℤ) :
    (⨆ i, |(X i : ℝ)|) = ‖fun i => (X i : ℝ)‖ := by
  apply le_antisymm
  · apply ciSup_le
    intro i
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun i => (X i : ℝ)) i
  · apply (pi_norm_le_iff_of_nonempty (fun i => (X i : ℝ))).mpr
    intro i
    simpa only [Real.norm_eq_abs] using
      le_ciSup (Finite.bddAbove_range (fun i => |(X i : ℝ)|)) i

/-- Integer snapshot vectors with the paper's small three-place product lie
in finitely many proper rational subspaces. The norm is the ordinary finite
sup norm, and the inequality includes equality at the threshold. -/
theorem cluster_three_place_subspaces (s : ℕ) (hs : 0 < s) {η : ℝ} (hη : 0 < η) :
    ∃ T : Finset (Submodule ℚ (Fin (s+1) → ℚ)),
      (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ X : Fin (s+1) → ℤ, X ≠ 0 →
        clusterThreePlaceProduct s X ≤ ‖fun i => (X i : ℝ)‖ ^ (-η) →
        ∃ W ∈ T, (fun i => (X i : ℚ)) ∈ W := by
  classical
  have : Nontrivial (Fin (s+1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  let p3 : Nat.Primes := ⟨3, Nat.prime_three⟩
  have hp23 : p2 ≠ p3 := by
    intro h
    have hv := congrArg Subtype.val h
    norm_num [p2, p3] at hv
  obtain ⟨T, hT, hcover⟩ := Rat.exists_finset_submodule_of_prod_mul_prod_padicNorm_le
    (F := ℚ) Rat.infinitePlace.1 (by exact ⟨AbsoluteValue.ext fun _ => rfl⟩)
    (clusterForms s) (clusterForms_linearIndependent s) {p2, p3} hη
  refine ⟨T, hT, fun X hX hprod => ?_⟩
  apply hcover X
  · intro hzero
    apply hX
    ext i
    change X i = 0
    exact Int.cast_eq_zero.mp (show (X i : ℚ) = 0 from congrFun hzero i)
  · rw [clusterForms_arch_product, Finset.prod_pair hp23, integer_iSup_abs_eq_norm]
    simpa only [p2, p3, clusterThreePlaceProduct, mul_assoc] using hprod

/-- A finite family of proper rational subspaces admits a finite family of
nonzero coefficient vectors annihilating every covered point. -/
theorem finite_relations_of_proper_subspaces {ι : Type*} [Fintype ι]
    (T : Finset (Submodule ℚ (ι → ℚ))) (hT : ∀ W ∈ T, W ≠ ⊤) :
    ∃ Z : Finset (ι → ℚ), (∀ z ∈ Z, z ≠ 0) ∧
      ∀ x : ι → ℚ, (∃ W ∈ T, x ∈ W) →
        ∃ z ∈ Z, ∑ i, z i * x i = 0 := by
  classical
  have hex : ∀ W : T, ∃ z : ι → ℚ, z ≠ 0 ∧
      ∀ x ∈ (W : Submodule ℚ (ι → ℚ)), ∑ i, z i * x i = 0 := by
    intro W
    obtain ⟨f, hf0, hWf⟩ := W.val.exists_le_ker_of_lt_top (hT W.val W.property).lt_top
    let z : ι → ℚ := fun i => f (fun j => if i = j then 1 else 0)
    have hf : ∀ x, f x = ∑ i, z i * x i := by
      intro x
      rw [LinearMap.pi_apply_eq_sum_univ f x]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_eq_mul, mul_comm]
    refine ⟨z, ?_, fun x hx => (hf x).symm.trans (LinearMap.mem_ker.mp (hWf hx))⟩
    intro hz
    apply hf0
    apply LinearMap.ext
    intro x
    rw [hf, hz]
    simp
  choose z hz0 hz using hex
  refine ⟨Finset.univ.image z, ?_, ?_⟩
  · intro a ha
    obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp ha
    exact hz0 W
  · intro x hx
    obtain ⟨W, hWT, hxW⟩ := hx
    refine ⟨z ⟨W, hWT⟩, Finset.mem_image.mpr ⟨⟨W, hWT⟩, Finset.mem_univ _, rfl⟩, ?_⟩
    exact hz ⟨W, hWT⟩ x hxW

/-- The three-place Subspace Theorem in the precise relation-vector form
used to begin elimination of exceptional Collatz cluster subspaces. -/
theorem cluster_three_place_relations (s : ℕ) (hs : 0 < s) {η : ℝ} (hη : 0 < η) :
    ∃ Z : Finset (Fin (s+1) → ℚ), (∀ z ∈ Z, z ≠ 0) ∧
      ∀ X : Fin (s+1) → ℤ, X ≠ 0 →
        clusterThreePlaceProduct s X ≤ ‖fun i => (X i : ℝ)‖ ^ (-η) →
        ∃ z ∈ Z, ∑ i, z i * (X i : ℚ) = 0 := by
  obtain ⟨T, hT, hcover⟩ := cluster_three_place_subspaces s hs hη
  obtain ⟨Z, hZ, hrel⟩ := finite_relations_of_proper_subspaces T hT
  exact ⟨Z, hZ, fun X hX hp => hrel _ (hcover X hX hp)⟩

end CollatzPrefix
