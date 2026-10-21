import ZeroCluster
import PrefixRepairs

/-!
# Splicing zero-repair reference intervals

Endpoint-preserving replacement creates no boundary repairs. Replacing an
interval containing a repair by an exact reference orbit strictly reduces
the total repair count. This is the combinatorial step used after the
zero-cluster lemma.
-/

namespace CollatzPrefix
variable {ι : Type*}

/-- Replace the labels on a closed interval, leaving all other labels alone. -/
def spliceReference (c d : ℕ → ι) (l k : ℕ) (t : ℕ) : ι :=
  if l ≤ t ∧ t ≤ k then d t else c t

theorem spliceReference_eq_replacement (c d : ℕ → ι) {l k t : ℕ}
    (htl : l ≤ t) (htk : t ≤ k) : spliceReference c d l k t = d t := by
  simp [spliceReference, htl, htk]

theorem spliceReference_eq_original (c d : ℕ → ι) {l k t : ℕ}
    (hl : d l = c l) (hk : d k = c k) (ht : t ≤ l ∨ k ≤ t) :
    spliceReference c d l k t = c t := by
  unfold spliceReference
  split_ifs with hmem
  · rcases ht with htl | hkt
    · have he : t = l := by omega
      simpa [he] using hl
    · have he : t = k := by omega
      simpa [he] using hk
  · rfl

variable [Fintype ι]

theorem spliceReference_good_inside (C : RationalPeriodicDictionary ι)
    (n : ℕ) (c d : ℕ → ι) {l k t : ℕ}
    (htl : l ≤ t) (htk : t < k) (hd : GoodAt C n d t) :
    GoodAt C n (spliceReference c d l k) t := by
  unfold GoodAt at hd ⊢
  rw [spliceReference_eq_replacement c d htl (by omega),
    spliceReference_eq_replacement c d (by omega : l ≤ t + 1) (by omega)]
  exact hd

theorem spliceReference_good_outside (C : RationalPeriodicDictionary ι)
    (n : ℕ) (c d : ℕ → ι) {l k t : ℕ}
    (hl : d l = c l) (hk : d k = c k) (ht : t < l ∨ k ≤ t) :
    GoodAt C n (spliceReference c d l k) t ↔ GoodAt C n c t := by
  unfold GoodAt
  rw [spliceReference_eq_original c d hl hk (by omega : t ≤ l ∨ k ≤ t),
    spliceReference_eq_original c d hl hk (by omega : t + 1 ≤ l ∨ k ≤ t + 1)]

/-- Every repair after a good splice was already a repair before the splice. -/
theorem spliceReference_repairSet_subset (C : RationalPeriodicDictionary ι)
    (n h : ℕ) (c d : ℕ → ι) {l k : ℕ}
    (hl : d l = c l) (hk : d k = c k)
    (hd : ∀ t, l ≤ t → t < k → GoodAt C n d t) :
    repairSet C n (spliceReference c d l k) h ⊆ repairSet C n c h := by
  intro t ht
  rw [mem_repairSet] at ht ⊢
  refine ⟨ht.1, ?_⟩
  by_cases hi : l ≤ t ∧ t < k
  · exact (ht.2 (spliceReference_good_inside C n c d hi.1 hi.2 (hd t hi.1 hi.2))).elim
  · exact fun hg => ht.2 ((spliceReference_good_outside C n c d hl hk (by omega)).mpr hg)

/-- A good splice strictly reduces the total repair count if it covers even
one original repair. In particular there are no newly created boundary repairs. -/
theorem spliceReference_repairCount_lt (C : RationalPeriodicDictionary ι)
    (n h : ℕ) (c d : ℕ → ι) {l k : ℕ}
    (hl : d l = c l) (hk : d k = c k) (hkh : k ≤ h)
    (hd : ∀ t, l ≤ t → t < k → GoodAt C n d t)
    (hr : ∃ t, l ≤ t ∧ t < k ∧ ¬ GoodAt C n c t) :
    repairCount C n (spliceReference c d l k) h < repairCount C n c h := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨spliceReference_repairSet_subset C n h c d hl hk hd, ?_⟩
  intro heq
  rcases hr with ⟨t, htl, htk, hbad⟩
  have ht : t ∈ repairSet C n c h := (mem_repairSet C n c h t).mpr ⟨by omega, hbad⟩
  rw [← heq, mem_repairSet] at ht
  exact ht.2 (spliceReference_good_inside C n c d htl htk (hd t htl htk))

/-- The natural accelerated orbit satisfies the rational affine step exactly. -/
theorem oddOrbit_affineStep (n t : ℕ) :
    affineStep (acceleratedExponent (oddOrbit n t)) (oddOrbit n t : ℚ) =
      (oddOrbit n (t + 1) : ℚ) := by
  unfold affineStep
  rw [oddOrbit_succ]
  apply (div_eq_iff (by positivity : (2 : ℚ) ^ acceleratedExponent (oddOrbit n t) ≠ 0)).mpr
  have hn := accelerated_numerator (oddOrbit n t)
  exact_mod_cast (by simpa only [Nat.mul_comm] using hn.symm)

/-- Splitting the actual cumulative exponent at an interval boundary. -/
theorem actualDepth_interval (n l h : ℕ) :
    actualDepth n (l + h) = actualDepth n l +
      affineExponentSum (fun t => acceleratedExponent (oddOrbit n (l + t))) h := by
  simp only [actualDepth, affineExponentSum, Finset.sum_range_add]

/-- The paper's normalized defect, for the actual accelerated orbit. -/
def normalizedDefect (C : RationalPeriodicDictionary ι) (n : ℕ)
    (c : ℕ → ι) (t : ℕ) : ℚ :=
  (2 : ℚ) ^ actualDepth n t / 3 ^ t * ((oddOrbit n t : ℚ) - C.value (c t))

/-- A zero normalized increment on an interval containing a repair contradicts
minimality of the total repair count. This is the paper's nonzero-cluster lemma,
with all affine-word and reference-splicing steps included. -/
theorem minimal_repairs_cluster_increment_ne_zero (C : RationalPeriodicDictionary ι)
    (hinj : Function.Injective C.value) (n H : ℕ) (c : ℕ → ι) (hodd : Odd n)
    (hmin : ∀ d : ℕ → ι, repairCount C n c H ≤ repairCount C n d H)
    (l h : ℕ) (hbound : l + h ≤ H)
    (hr : ∃ t, l ≤ t ∧ t < l + h ∧ ¬ GoodAt C n c t) :
    normalizedDefect C n c (l + h) - normalizedDefect C n c l ≠ 0 := by
  intro hz
  let x : ℕ → ℚ := fun t => (oddOrbit n (l + t) : ℚ)
  let a : ℕ → ℕ := fun t => acceleratedExponent (oddOrbit n (l + t))
  have ha : ∀ t < h, 0 < a t := fun t _ =>
    acceleratedExponent_pos (oddOrbit_odd hodd (l + t))
  have hs : ∀ t < h, affineStep (a t) (x t) = x (t + 1) := by
    intro t _
    simpa [a, x, Nat.add_assoc] using oddOrbit_affineStep n (l + t)
  have hz' : (2 : ℚ) ^ (actualDepth n l + affineExponentSum a h) / 3 ^ (l + h) *
      (x h - C.value (c (l + h))) =
      2 ^ actualDepth n l / 3 ^ l * (x 0 - C.value (c l)) := by
    have he := sub_eq_zero.mp hz
    simpa [normalizedDefect, actualDepth_interval, a, x] using he
  obtain ⟨d, hd₀, hdh, hgood⟩ := C.zero_cluster_replacement_shifted hinj
    x a h l (actualDepth n l) (c l) (c (l + h)) ha hs hz'
  let d' : ℕ → ι := fun t => d (t - l)
  have hd'l : d' l = c l := by simpa [d'] using hd₀
  have hd'k : d' (l + h) = c (l + h) := by simpa [d'] using hdh
  have hd'good : ∀ t, l ≤ t → t < l + h → GoodAt C n d' t := by
    intro t htl hth
    have ht : t - l < h := by omega
    have hh := hgood (t - l) ht
    have he : l + (t - l) = t := by omega
    have he' : t + 1 - l = t - l + 1 := by omega
    refine ⟨?_, ?_⟩
    · simpa only [a, he, d'] using hh.2
    · simpa only [d', he'] using hh.1
  have hlt := spliceReference_repairCount_lt C n H c d' hd'l hd'k hbound hd'good hr
  have hle := hmin (spliceReference c d' l (l + h))
  omega

end CollatzPrefix
