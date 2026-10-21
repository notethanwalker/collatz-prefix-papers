import PrefixRepairs

namespace CollatzPrefix
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The valuation at the start of a good gap pays for its entire reference
depth and leaves one factor of two at the odd endpoint. -/
theorem good_gap_valuation (C : RationalPeriodicDictionary ι) {n h l u : ℕ}
    (c : ℕ → ι) (hn : 0 < n) (hodd : Odd n) (had : Admissible C n h)
    (hlu : l ≤ u) (huh : u ≤ h)
    (hgood : ∀ t ∈ Finset.Ico l u, GoodAt C n c t) :
    (∑ t ∈ Finset.Ico l u, C.exponent (c t)) + 1 ≤
      padicValInt 2 (C.defect (oddOrbit n l) (c l)) := by
  have had' : Admissible C (oddOrbit n l) (u - l) :=
    admissible_suffix C had (by omega)
  have hg : ∀ t < u - l, GoodAt C (oddOrbit n l) (fun t => c (l + t)) t := by
    intro t ht
    apply (goodAt_shift C n l t c).mpr
    exact hgood (l + t) (by simp only [Finset.mem_Ico]; omega)
  have hv := periodic_no_repair_valuation C (oddOrbit (oddOrbit n l))
    (fun t => c (l + t)) (u - l)
    (fun t _ => oddOrbit_odd (oddOrbit_odd hodd l) t)
    (fun t ht => ne_of_gt (C.defect_pos_of_value_lt
      (admissible_value_lt C (oddOrbit_pos hn l) had' ht _)))
    (fun t _ => oddOrbit_succ _ t) (fun t ht => (hg t ht).2) (fun t ht => (hg t ht).1)
  simpa [Finset.sum_Ico_eq_sum_range] using hv

private theorem nat_sum_union_le {α : Type*} [DecidableEq α]
    (P Q : Finset α) (f : α → ℕ) :
    (∑ a ∈ P ∪ Q, f a) ≤ (∑ a ∈ P, f a) + ∑ a ∈ Q, f a := by
  have hh : (∑ a ∈ P ∪ Q, f a) + (∑ a ∈ P ∩ Q, f a) =
      (∑ a ∈ P, f a) + ∑ a ∈ Q, f a := Finset.sum_union_inter
  omega

private theorem nat_sum_biUnion_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (G : α → Finset β) (f : β → ℕ) :
    (∑ t ∈ S.biUnion G, f t) ≤ ∑ i ∈ S, ∑ t ∈ G i, f t := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (nat_sum_union_le (G i) (S.biUnion G) f).trans (Nat.add_le_add_left ih _)

/-- A finite cover bound; overlaps do not require disjointness, because all
weights are nonnegative. -/
theorem weighted_cover_bound (b : ℕ → ℕ) (h : ℕ) (P : Finset ℕ)
    (G : κ → Finset ℕ) (M : ℕ) (hb : ∀ t, b t ≤ M)
    (hcover : ∀ t < h, t ∈ P ∨ ∃ i, t ∈ G i) :
    (∑ t ∈ Finset.range h, b t) ≤ P.card * M + ∑ i, ∑ t ∈ G i, b t := by
  classical
  have hsub : Finset.range h ⊆ P ∪ Finset.univ.biUnion G := by
    intro t ht
    rcases hcover t (Finset.mem_range.mp ht) with ht | ⟨i, hi⟩
    · exact Finset.mem_union_left _ ht
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩)
  have hP : (∑ t ∈ P, b t) ≤ P.card * M := by
    calc
      _ ≤ ∑ _t ∈ P, M := Finset.sum_le_sum (fun t _ => hb t)
      _ = _ := by simp
  calc
    _ ≤ ∑ t ∈ P ∪ Finset.univ.biUnion G, b t :=
      Finset.sum_le_sum_of_subset hsub
    _ ≤ (∑ t ∈ P, b t) + ∑ t ∈ Finset.univ.biUnion G, b t := nat_sum_union_le _ _ _
    _ ≤ P.card * M + ∑ i, ∑ t ∈ G i, b t :=
      Nat.add_le_add hP (nat_sum_biUnion_le _ _ _)

/-- The finite valuation inequality used in the three-place product estimate.
Any bounded-size exceptional set and good gaps covering its complement suffice. -/
theorem good_gap_valuation_cover (C : RationalPeriodicDictionary ι)
    {n h : ℕ} (c : ℕ → ι) (hn : 0 < n) (hodd : Odd n) (had : Admissible C n h)
    (lo hi : κ → ℕ) (P : Finset ℕ)
    (hle : ∀ i, lo i ≤ hi i) (hhi : ∀ i, hi i ≤ h)
    (hgood : ∀ i, ∀ t ∈ Finset.Ico (lo i) (hi i), GoodAt C n c t)
    (hcover : ∀ t < h, t ∈ P ∨ ∃ i, t ∈ Finset.Ico (lo i) (hi i)) :
    referenceDepth C c h + Fintype.card κ ≤
      (∑ i, padicValInt 2 (C.defect (oddOrbit n (lo i)) (c (lo i)))) +
        P.card * exponentCap C := by
  have hv := Finset.sum_le_sum (s := (Finset.univ : Finset κ)) (fun i _ =>
    good_gap_valuation C c hn hodd had (hle i) (hhi i) (hgood i))
  have hc := weighted_cover_bound (fun t => C.exponent (c t)) h P
    (fun i => Finset.Ico (lo i) (hi i)) (exponentCap C)
    (fun t => exponent_le_cap C (c t)) hcover
  simp [Finset.sum_add_distrib] at hv
  unfold referenceDepth
  omega

end CollatzPrefix
