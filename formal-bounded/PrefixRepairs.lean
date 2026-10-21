import BoundedDeviations

/-! Actual accelerated prefixes, repair counts, and finite valuation reductions. -/

namespace CollatzPrefix
open scoped BigOperators

def oddOrbit (n t : ℕ) : ℕ := accelerated^[t] n

@[simp] theorem oddOrbit_zero (n : ℕ) : oddOrbit n 0 = n := rfl

theorem oddOrbit_succ (n t : ℕ) : oddOrbit n (t + 1) = accelerated (oddOrbit n t) :=
  Function.iterate_succ_apply' accelerated t n

theorem oddOrbit_add (n t k : ℕ) : oddOrbit n (t + k) = oddOrbit (oddOrbit n t) k := by
  unfold oddOrbit
  rw [Nat.add_comm t k, Function.iterate_add_apply]

theorem oddOrbit_pos {n : ℕ} (hn : 0 < n) (t : ℕ) : 0 < oddOrbit n t := by
  cases t with
  | zero => exact hn
  | succ t => rw [oddOrbit_succ]; exact accelerated_pos _

theorem oddOrbit_odd {n : ℕ} (hn : Odd n) (t : ℕ) : Odd (oddOrbit n t) := by
  cases t with
  | zero => exact hn
  | succ t => rw [oddOrbit_succ]; exact accelerated_odd _

def actualDepth (n h : ℕ) : ℕ :=
  ∑ t ∈ Finset.range h, acceleratedExponent (oddOrbit n t)

variable {ι : Type*} [Fintype ι]

def referenceDepth (C : RationalPeriodicDictionary ι) (c : ℕ → ι) (h : ℕ) : ℕ :=
  ∑ t ∈ Finset.range h, C.exponent (c t)

def GoodAt (C : RationalPeriodicDictionary ι) (n : ℕ) (c : ℕ → ι) (t : ℕ) : Prop :=
  acceleratedExponent (oddOrbit n t) = C.exponent (c t) ∧ c (t + 1) = C.next (c t)

noncomputable def repairSet (C : RationalPeriodicDictionary ι) (n : ℕ) (c : ℕ → ι)
    (h : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range h).filter (fun t => ¬ GoodAt C n c t)

noncomputable def repairCount (C : RationalPeriodicDictionary ι) (n : ℕ) (c : ℕ → ι)
    (h : ℕ) : ℕ := (repairSet C n c h).card

theorem mem_repairSet (C : RationalPeriodicDictionary ι) (n : ℕ) (c : ℕ → ι)
    (h t : ℕ) : t ∈ repairSet C n c h ↔ t < h ∧ ¬ GoodAt C n c t := by
  classical
  simp [repairSet]

/-- The paper's two domain alternatives, without a redundant maximum/ceiling.
The second says every actual state is at least `2*max |c|+2`. -/
def Admissible (C : RationalPeriodicDictionary ι) (n h : ℕ) : Prop :=
  (∀ i, C.value i < 0) ∨
    ∀ t ≤ h, ∀ i, 2 * |C.value i| + 2 ≤ (oddOrbit n t : ℚ)

theorem admissible_value_lt (C : RationalPeriodicDictionary ι) {n h : ℕ}
    (hn : 0 < n) (had : Admissible C n h) {t : ℕ} (ht : t ≤ h) (i : ι) :
    C.value i < (oddOrbit n t : ℚ) := by
  rcases had with hneg | hlarge
  · have hp : (0 : ℚ) < oddOrbit n t := by exact_mod_cast oddOrbit_pos hn t
    exact (hneg i).trans hp
  · have ha := le_abs_self (C.value i)
    have hp := abs_nonneg (C.value i)
    have hl := hlarge t ht i
    linarith

theorem admissible_prefix (C : RationalPeriodicDictionary ι) {n h k : ℕ}
    (had : Admissible C n h) (hk : k ≤ h) : Admissible C n k := by
  rcases had with hneg | hlarge
  · exact Or.inl hneg
  · exact Or.inr (fun t ht i => hlarge t (ht.trans hk) i)

theorem admissible_suffix (C : RationalPeriodicDictionary ι) {n h l k : ℕ}
    (had : Admissible C n h) (hk : l + k ≤ h) : Admissible C (oddOrbit n l) k := by
  rcases had with hneg | hlarge
  · exact Or.inl hneg
  · apply Or.inr
    intro t ht i
    rw [← oddOrbit_add]
    exact hlarge (l + t) (by omega) i

theorem length_le_referenceDepth (C : RationalPeriodicDictionary ι) (c : ℕ → ι) (h : ℕ) :
    h ≤ referenceDepth C c h := by
  calc
    h = ∑ _t ∈ Finset.range h, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun t _ => C.exponent_pos (c t))

def exponentCap (C : RationalPeriodicDictionary ι) : ℕ := ∑ i, C.exponent i

theorem exponent_le_cap (C : RationalPeriodicDictionary ι) (i : ι) :
    C.exponent i ≤ exponentCap C := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (C.exponent j)) (Finset.mem_univ i)

def initialValuationCap (C : RationalPeriodicDictionary ι) (n : ℕ) : ℕ :=
  ∑ i, padicValInt 2 (C.defect n i)

theorem no_repair_length_le (C : RationalPeriodicDictionary ι) {n h : ℕ}
    (c : ℕ → ι) (hn : 0 < n) (hodd : Odd n) (had : Admissible C n h)
    (hgood : ∀ t < h, GoodAt C n c t) : h ≤ initialValuationCap C n := by
  have hv := periodic_no_repair_valuation C (oddOrbit n) c h
    (fun t _ => oddOrbit_odd hodd t)
    (fun t ht => ne_of_gt (C.defect_pos_of_value_lt (admissible_value_lt C hn had ht _)))
    (fun t _ => oddOrbit_succ n t) (fun t ht => (hgood t ht).2)
    (fun t ht => (hgood t ht).1)
  have hi : padicValInt 2 (C.defect n (c 0)) ≤ initialValuationCap C n :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (padicValInt 2 (C.defect n j)))
      (Finset.mem_univ (c 0))
  have hl := length_le_referenceDepth C c h
  unfold referenceDepth at hl
  simp only [oddOrbit_zero] at hv
  omega

theorem repairCount_zero_iff (C : RationalPeriodicDictionary ι) (n h : ℕ)
    (c : ℕ → ι) : repairCount C n c h = 0 ↔ ∀ t < h, GoodAt C n c t := by
  classical
  simp only [repairCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem,
    mem_repairSet]
  simp only [not_and, not_not]

theorem repairCount_mono (C : RationalPeriodicDictionary ι) (n : ℕ)
    (c : ℕ → ι) {h k : ℕ} (hk : h ≤ k) : repairCount C n c h ≤ repairCount C n c k := by
  apply Finset.card_le_card
  intro t ht
  rw [mem_repairSet] at ht ⊢
  exact ⟨ht.1.trans_le hk, ht.2⟩

theorem goodAt_shift (C : RationalPeriodicDictionary ι) (n l t : ℕ) (c : ℕ → ι) :
    GoodAt C (oddOrbit n l) (fun k => c (l + k)) t ↔ GoodAt C n c (l + t) := by
  simp [GoodAt, ← oddOrbit_add, Nat.add_assoc]

theorem exists_first_repair (C : RationalPeriodicDictionary ι) (n h : ℕ)
    (c : ℕ → ι) (hr : repairCount C n c h ≠ 0) :
    ∃ t < h, ¬ GoodAt C n c t ∧ ∀ j < t, GoodAt C n c j := by
  classical
  have hne : (repairSet C n c h).Nonempty := Finset.card_ne_zero.mp hr
  let t := (repairSet C n c h).min' hne
  have ht := (mem_repairSet C n c h t).mp (Finset.min'_mem _ hne)
  refine ⟨t, ht.1, ht.2, ?_⟩
  intro j hj
  by_contra hbad
  have hm : j ∈ repairSet C n c h := (mem_repairSet C n c h j).mpr ⟨hj.trans ht.1, hbad⟩
  have := Finset.min'_le _ j hm
  omega

/-- A suffix after a repair spends at least one fewer repair than the full prefix. -/
theorem repairCount_suffix_after_repair (C : RationalPeriodicDictionary ι) (n h t : ℕ)
    (c : ℕ → ι) (ht : t < h) (hbad : ¬ GoodAt C n c t) :
    repairCount C (oddOrbit n (t + 1)) (fun j => c (t + 1 + j)) (h - (t + 1)) + 1 ≤
      repairCount C n c h := by
  classical
  let T := repairSet C (oddOrbit n (t + 1)) (fun j => c (t + 1 + j)) (h - (t + 1))
  have hnot : t ∉ T.image (fun j => t + 1 + j) := by
    simp only [Finset.mem_image]
    rintro ⟨j, _, hj⟩
    omega
  have hsub : insert t (T.image (fun j => t + 1 + j)) ⊆ repairSet C n c h := by
    intro j hj
    rcases Finset.mem_insert.mp hj with hj | hj
    · subst j
      exact (mem_repairSet C n c h t).mpr ⟨ht, hbad⟩
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      have hk' := (mem_repairSet C _ _ _ k).mp hk
      apply (mem_repairSet C n c h _).mpr
      refine ⟨by omega, ?_⟩
      exact fun hg => hk'.2 ((goodAt_shift C n (t + 1) k c).mpr hg)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective] at hc
  · exact hc
  · intro j k hjk
    dsimp only at hjk
    omega

/-- An explicit (very crude) finite length cap, used only to exclude bounded
starting states in a family violating the asymptotic estimate. -/
def prefixLengthCap (C : RationalPeriodicDictionary ι) : ℕ → ℕ → ℕ
  | 0, n => initialValuationCap C n
  | R + 1, n => initialValuationCap C n + 1 +
      ∑ t ∈ Finset.range (initialValuationCap C n + 1),
        prefixLengthCap C R (oddOrbit n (t + 1))

theorem length_le_prefixLengthCap (C : RationalPeriodicDictionary ι) (R : ℕ)
    {n h : ℕ} (c : ℕ → ι) (hn : 0 < n) (hodd : Odd n)
    (had : Admissible C n h) (hr : repairCount C n c h ≤ R) :
    h ≤ prefixLengthCap C R n := by
  induction R generalizing n h c with
  | zero =>
    apply no_repair_length_le C c hn hodd had
    exact (repairCount_zero_iff C n h c).mp (Nat.eq_zero_of_le_zero hr)
  | succ R ih =>
    by_cases hz : repairCount C n c h = 0
    · have hh := no_repair_length_le C c hn hodd had ((repairCount_zero_iff C n h c).mp hz)
      simp only [prefixLengthCap]
      omega
    obtain ⟨t, ht, hbad, hgood⟩ := exists_first_repair C n h c hz
    have htb : t ≤ initialValuationCap C n :=
      no_repair_length_le C c hn hodd (admissible_prefix C had ht.le) hgood
    have hs := repairCount_suffix_after_repair C n h t c ht hbad
    have htail := ih (fun j => c (t + 1 + j)) (oddOrbit_pos hn _) (oddOrbit_odd hodd _)
      (admissible_suffix C had (by omega : t + 1 + (h - (t + 1)) ≤ h)) (by omega)
    have hterm : prefixLengthCap C R (oddOrbit n (t + 1)) ≤
        ∑ j ∈ Finset.range (initialValuationCap C n + 1),
          prefixLengthCap C R (oddOrbit n (j + 1)) :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (prefixLengthCap C R (oddOrbit n (j + 1))))
        (show t ∈ Finset.range (initialValuationCap C n + 1) by simp; omega)
    simp only [prefixLengthCap]
    omega

/-- A reference path minimizing the repair count always exists. -/
theorem exists_minimal_repairs (C : RationalPeriodicDictionary ι) (n h : ℕ) (c : ℕ → ι) :
    ∃ c' : ℕ → ι, repairCount C n c' h ≤ repairCount C n c h ∧
      ∀ c'' : ℕ → ι, repairCount C n c' h ≤ repairCount C n c'' h := by
  classical
  have hex : ∃ k : ℕ, ∃ c' : ℕ → ι, repairCount C n c' h = k := ⟨_, c, rfl⟩
  obtain ⟨c', hc'⟩ := Nat.find_spec hex
  refine ⟨c', ?_, ?_⟩
  · rw [hc']
    exact Nat.find_min' hex ⟨c, rfl⟩
  · intro c''
    rw [hc']
    exact Nat.find_min' hex ⟨c'', rfl⟩

theorem referenceDepth_le_cap_mul (C : RationalPeriodicDictionary ι) (c : ℕ → ι) (h : ℕ) :
    referenceDepth C c h ≤ h * exponentCap C := by
  calc
    _ ≤ ∑ _t ∈ Finset.range h, exponentCap C :=
      Finset.sum_le_sum (fun t _ => exponent_le_cap C (c t))
    _ = _ := by simp

/-- Two reference depths differ only where one of the references needs repair. -/
theorem referenceDepth_le_add_repairs (C : RationalPeriodicDictionary ι)
    (n h : ℕ) (c c' : ℕ → ι) :
    referenceDepth C c h ≤ referenceDepth C c' h +
      (repairCount C n c h + repairCount C n c' h) * exponentCap C := by
  classical
  let S := repairSet C n c h ∪ repairSet C n c' h
  have hsub : S ⊆ Finset.range h := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact Finset.mem_range.mpr ((mem_repairSet C n c h t).mp ht).1
    · exact Finset.mem_range.mpr ((mem_repairSet C n c' h t).mp ht).1
  have hterm : ∀ t ∈ Finset.range h,
      C.exponent (c t) ≤ C.exponent (c' t) + if t ∈ S then exponentCap C else 0 := by
    intro t ht
    by_cases hb : t ∈ S
    · simp only [if_pos hb]
      exact (exponent_le_cap C _).trans (Nat.le_add_left _ _)
    · have hg : GoodAt C n c t := by
        by_contra hg
        exact hb (Finset.mem_union_left _ ((mem_repairSet C n c h t).mpr
          ⟨Finset.mem_range.mp ht, hg⟩))
      have hg' : GoodAt C n c' t := by
        by_contra hg'
        exact hb (Finset.mem_union_right _ ((mem_repairSet C n c' h t).mpr
          ⟨Finset.mem_range.mp ht, hg'⟩))
      simp only [if_neg hb, add_zero]
      exact le_of_eq (hg.1.symm.trans hg'.1)
  have hsum := Finset.sum_le_sum hterm
  have hfilter : (Finset.range h).filter (fun t => t ∈ S) = S := by
    ext t
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun ht => hsub ht
  have hpen : (∑ t ∈ Finset.range h, if t ∈ S then exponentCap C else 0) =
      S.card * exponentCap C := by
    rw [← Finset.sum_filter, hfilter]
    simp
  rw [Finset.sum_add_distrib, hpen] at hsum
  exact hsum.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (Finset.card_union_le _ _)) _)

end CollatzPrefix
