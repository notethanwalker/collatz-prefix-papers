import PrefixRepairs
import Mathlib.Data.Finset.Sort

/-!
# Increasing enumeration of the actual repair set

The cardinality in `repairCount` determines an increasing enumeration of all
repair positions. Its consecutive gaps, as well as its initial and terminal
gaps, consist exclusively of good steps.
-/

namespace CollatzPrefix

/-- Enumerate a finite set of positions in strictly increasing order. -/
theorem exists_sorted_positions (R : Finset ℕ) {r H : ℕ}
    (hcard : R.card = r) (hbound : ∀ t ∈ R, t < H) :
    ∃ p : Fin r → ℕ, StrictMono p ∧ (∀ i, p i < H) ∧
      (∀ t, t ∈ R ↔ ∃ i, p i = t) := by
  let e := R.orderEmbOfFin hcard
  refine ⟨e, e.strictMono, ?_, ?_⟩
  · intro i
    exact hbound _ (R.orderEmbOfFin_mem hcard i)
  · intro t
    have hrange := R.range_orderEmbOfFin hcard
    exact Set.ext_iff.mp hrange t |>.symm

variable {ι : Type*} [Fintype ι]

/-- The repair count is the length of a strictly increasing enumeration of
exactly the repair positions in the prefix. -/
theorem exists_sorted_repairs (C : RationalPeriodicDictionary ι) (n : ℕ)
    (c : ℕ → ι) (H : ℕ) {r : ℕ} (hr : repairCount C n c H = r) :
    ∃ p : Fin r → ℕ, StrictMono p ∧ (∀ i, p i < H) ∧
      (∀ t, t ∈ repairSet C n c H ↔ ∃ i, p i = t) := by
  apply exists_sorted_positions (repairSet C n c H) hr
  intro t ht
  exact ((mem_repairSet C n c H t).mp ht).1

/-- A step before the first enumerated repair is good. -/
theorem goodAt_before_first_repair (C : RationalPeriodicDictionary ι) (n : ℕ)
    (c : ℕ → ι) (H : ℕ) {r : ℕ} {p : Fin r → ℕ}
    (hmono : StrictMono p) (hbound : ∀ i, p i < H)
    (henum : ∀ t, t ∈ repairSet C n c H ↔ ∃ i, p i = t)
    (hr : 0 < r) {t : ℕ} (ht : t < p ⟨0, hr⟩) : GoodAt C n c t := by
  by_contra hbad
  have hmem : t ∈ repairSet C n c H :=
    (mem_repairSet C n c H t).mpr ⟨ht.trans (hbound _), hbad⟩
  obtain ⟨i, hi⟩ := (henum t).mp hmem
  have hle := hmono.monotone (show (⟨0, hr⟩ : Fin r) ≤ i by exact Nat.zero_le _)
  omega

/-- Every step strictly between consecutive repair positions is good. -/
theorem goodAt_between_repairs (C : RationalPeriodicDictionary ι) (n : ℕ)
    (c : ℕ → ι) (H : ℕ) {r : ℕ} {p : Fin r → ℕ}
    (hmono : StrictMono p) (hbound : ∀ i, p i < H)
    (henum : ∀ t, t ∈ repairSet C n c H ↔ ∃ i, p i = t)
    {i j : Fin r} (hij : i.val + 1 = j.val) {t : ℕ}
    (hit : p i < t) (htj : t < p j) : GoodAt C n c t := by
  by_contra hbad
  have hmem : t ∈ repairSet C n c H :=
    (mem_repairSet C n c H t).mpr ⟨htj.trans (hbound _), hbad⟩
  obtain ⟨k, hk⟩ := (henum t).mp hmem
  have hik : i < k := hmono.lt_iff_lt.mp (by omega : p i < p k)
  have hkj : k < j := hmono.lt_iff_lt.mp (by omega : p k < p j)
  have hik' : i.val < k.val := hik
  have hkj' : k.val < j.val := hkj
  omega

/-- Every step after the last repair and still inside the prefix is good. -/
theorem goodAt_after_last_repair (C : RationalPeriodicDictionary ι) (n : ℕ)
    (c : ℕ → ι) (H : ℕ) {r : ℕ} {p : Fin r → ℕ}
    (hmono : StrictMono p)
    (henum : ∀ t, t ∈ repairSet C n c H ↔ ∃ i, p i = t)
    (hr : 0 < r) {t : ℕ}
    (ht : p ⟨r - 1, Nat.sub_lt hr (by omega)⟩ < t) (htH : t < H) :
    GoodAt C n c t := by
  by_contra hbad
  have hmem : t ∈ repairSet C n c H :=
    (mem_repairSet C n c H t).mpr ⟨htH, hbad⟩
  obtain ⟨i, hi⟩ := (henum t).mp hmem
  have hle := hmono.monotone
    (show i ≤ (⟨r - 1, Nat.sub_lt hr (by omega)⟩ : Fin r) by
      change i.val ≤ r - 1
      omega)
  omega

/-- The enumeration is empty precisely when every step of the prefix is good. -/
theorem goodAt_of_empty_repair_enumeration (C : RationalPeriodicDictionary ι) (n : ℕ)
    (c : ℕ → ι) (H : ℕ) {p : Fin 0 → ℕ}
    (henum : ∀ t, t ∈ repairSet C n c H ↔ ∃ i, p i = t)
    {t : ℕ} (ht : t < H) : GoodAt C n c t := by
  by_contra hbad
  have hmem := (mem_repairSet C n c H t).mpr ⟨ht, hbad⟩
  obtain ⟨i, _⟩ := (henum t).mp hmem
  exact Fin.elim0 i

end CollatzPrefix
