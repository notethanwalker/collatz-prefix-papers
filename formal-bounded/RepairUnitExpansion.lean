import IntegerSnapshots
import ClusterUnitElimination

/-!
# Actual repair increments as fixed-coefficient S-unit sums

The identities below derive the unit terms from accelerated Collatz orbits,
remove good steps by telescoping, and allow coefficients that vanish by
restricting to their nonzero support before applying S-unit finiteness.
-/
namespace CollatzPrefix
open Filter
open scoped BigOperators Classical

section ZeroCoefficients
variable {α : Type*} [Fintype α]

/-- Deleting zero-coefficient positions preserves any supported finite sum. -/
theorem sum_nonzero_support (a f : α → ℚ) (hf : ∀ i, a i = 0 → f i = 0) :
    (∑ i : {i // a i ≠ 0}, f i) = ∑ i, f i := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => a i ≠ 0)) (by simp) f]
  exact Finset.sum_filter_of_ne (fun i _ hi hai => hi (hf i hai))

/-- The same support deletion commutes with selecting a cluster. -/
theorem sum_nonzero_support_filter {κ : Type*} [DecidableEq κ]
    (a f : α → ℚ) (hf : ∀ i, a i = 0 → f i = 0) (cluster : α → κ) (c : κ) :
    (∑ i ∈ Finset.univ.filter (fun i : {i // a i ≠ 0} => cluster i = c), f i) =
      ∑ i ∈ Finset.univ.filter (fun i => cluster i = c), f i := by
  classical
  simp only [Finset.sum_filter]
  exact sum_nonzero_support a (fun i => if cluster i = c then f i else 0)
    (fun i hai => by simp [hf i hai])

/-- S-unit localization remains valid with zero coefficients, which are discarded
by a proved support restriction rather than an extra nonvanishing assumption. -/
theorem eventually_cluster_sum_eq_zero_allow_zero {κ : Type*} [DecidableEq κ]
    (a : α → ℚ) (cluster : α → κ) (u t : ℕ → α → ℕ)
    (hzero : ∀ n, (∑ i, a i * (2 : ℚ) ^ u n i / 3 ^ t n i) = 0)
    (hsep : ∀ i j, cluster i ≠ cluster j →
      Tendsto (fun n => ((t n i : ℤ) - t n j).natAbs) atTop atTop) :
    ∀ᶠ n in atTop, ∀ c,
      (∑ i ∈ Finset.univ.filter (fun i => cluster i = c),
        a i * (2 : ℚ) ^ u n i / 3 ^ t n i) = 0 := by
  let S := {i // a i ≠ 0}
  have hs : ∀ n, (∑ i : S, a i * (2 : ℚ) ^ u n i / 3 ^ t n i) = 0 := by
    intro n
    exact (sum_nonzero_support a (fun i => a i * (2 : ℚ) ^ u n i / 3 ^ t n i)
      (fun i hi => by simp [hi])).trans (hzero n)
  have hev := ClusterElimination.eventually_cluster_sum_eq_zero
    (fun i : S => a i) (fun i => i.property) (fun i => cluster i)
    (fun n i => u n i) (fun n i => t n i) hs (fun i j => hsep i j)
  filter_upwards [hev] with n hn c
  rw [← sum_nonzero_support_filter a _ (fun i hi => by simp [hi]) cluster c]
  exact hn c

end ZeroCoefficients

variable {ι : Type*} [Fintype ι]

/-- The exact two S-unit terms contributed by one weighted repair increment. -/
theorem weighted_normalizedDefect_increment (C : RationalPeriodicDictionary ι)
    (n : ℕ) (c : ℕ → ι) (q : ℚ) (t : ℕ) :
    q * (normalizedDefect C n c (t + 1) - normalizedDefect C n c t) =
      (q * (3 * C.value (c t) + 1)) * (2 : ℚ) ^ actualDepth n t / 3 ^ (t + 1) +
        (-q * C.value (c (t + 1))) * (2 : ℚ) ^ actualDepth n (t + 1) / 3 ^ (t + 1) := by
  rw [normalizedDefect_increment]
  simp only [pow_succ]
  field_simp
  ring

/-- Telescoping over an interval requires only its repair positions: good-step
increments vanish identically, not just asymptotically. -/
theorem normalizedDefect_eq_sum_repairs (C : RationalPeriodicDictionary ι)
    (n : ℕ) (c : ℕ → ι) {l u : ℕ} (hlu : l ≤ u) :
    normalizedDefect C n c u - normalizedDefect C n c l =
      ∑ t ∈ (Finset.Ico l u).filter (fun t => ¬ GoodAt C n c t),
        (normalizedDefect C n c (t + 1) - normalizedDefect C n c t) := by
  classical
  rw [Finset.sum_filter_of_ne]
  · exact (Finset.sum_Ico_sub _ hlu).symm
  · intro t _ hne hgood
    exact hne (sub_eq_zero.mpr (normalizedDefect_good_step C n c hgood))

/-- Any injective enumeration of precisely the repairs in an interval gives
its exact normalized endpoint increment. -/
theorem normalizedDefect_eq_sum_enumerated_repairs {α : Type*} [Fintype α]
    (C : RationalPeriodicDictionary ι) (n : ℕ) (c : ℕ → ι)
    {l u : ℕ} (hlu : l ≤ u) (p : α → ℕ) (S : Finset α)
    (hinj : Function.Injective p)
    (hcover : ∀ t, l ≤ t ∧ t < u ∧ ¬ GoodAt C n c t ↔ ∃ i ∈ S, p i = t) :
    normalizedDefect C n c u - normalizedDefect C n c l =
      ∑ i ∈ S, (normalizedDefect C n c (p i + 1) - normalizedDefect C n c (p i)) := by
  classical
  rw [normalizedDefect_eq_sum_repairs C n c hlu]
  symm
  apply Finset.sum_bij (fun i _ => p i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_Ico, and_assoc]
    exact (hcover _).mpr ⟨i, hi, rfl⟩
  · intro i _ j _ h
    exact hinj h
  · intro t ht
    have ht' : l ≤ t ∧ t < u ∧ ¬ GoodAt C n c t := by
      simpa only [Finset.mem_filter, Finset.mem_Ico, and_assoc] using ht
    obtain ⟨i, hi, hpi⟩ := (hcover t).mp ht'
    exact ⟨i, hi, hpi⟩
  · intro i hi
    rfl

/-- The two fixed coefficients associated with a repair after fixing its labels. -/
def repairUnitCoefficient {α κ : Type*} (C : RationalPeriodicDictionary ι)
    (cluster : α → κ) (q : κ → ℚ) (before after : α → ι) (p : α × Bool) : ℚ :=
  if p.2 then q (cluster p.1) * (3 * C.value (before p.1) + 1)
  else -q (cluster p.1) * C.value (after p.1)

/-- The pre- and post-repair cumulative powers of two. -/
def repairUnitExponent {α : Type*} (n : ℕ) (time : α → ℕ) (p : α × Bool) : ℕ :=
  actualDepth n (if p.2 then time p.1 else time p.1 + 1)

/-- Pairwise expansion of an actual repair for fixed endpoint labels. -/
theorem weighted_increment_eq_bool_sum {α κ : Type*}
    (C : RationalPeriodicDictionary ι) (n : ℕ) (c : ℕ → ι)
    (cluster : α → κ) (q : κ → ℚ) (before after : α → ι) (time : α → ℕ)
    (hbefore : ∀ i, c (time i) = before i) (hafter : ∀ i, c (time i + 1) = after i)
    (i : α) :
    q (cluster i) * (normalizedDefect C n c (time i + 1) - normalizedDefect C n c (time i)) =
      ∑ b : Bool, repairUnitCoefficient C cluster q before after (i, b) *
        (2 : ℚ) ^ repairUnitExponent n time (i, b) / 3 ^ (time i + 1) := by
  rw [weighted_normalizedDefect_increment, Fintype.sum_bool]
  simp [repairUnitCoefficient, repairUnitExponent, hbefore, hafter]

/-- Filtering a product index by its first coordinate commutes with the second sum. -/
theorem sum_filter_prod_fst {α β κ : Type*} [Fintype α] [Fintype β] [DecidableEq κ]
    (cluster : α → κ) (f : α × β → ℚ) (c : κ) :
    (∑ p ∈ Finset.univ.filter (fun p => cluster p.1 = c), f p) =
      ∑ i ∈ Finset.univ.filter (fun i => cluster i = c), ∑ b, f (i, b) := by
  classical
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : cluster i = c <;> simp [h]

/-- The exact arithmetic localization theorem for actual weighted repair increments.
Fixed pre/post labels supply the fixed rational coefficients; no expansion identity
or nonzero-coefficient hypothesis is required from the caller. -/
theorem eventually_weighted_repair_cluster_sum_eq_zero
    {α κ : Type*} [Fintype α] [DecidableEq κ]
    (C : RationalPeriodicDictionary ι) (seed : ℕ → ℕ) (refs : ℕ → ℕ → ι)
    (cluster : α → κ) (q : κ → ℚ) (before after : α → ι) (time : ℕ → α → ℕ)
    (hbefore : ∀ n i, refs n (time n i) = before i)
    (hafter : ∀ n i, refs n (time n i + 1) = after i)
    (hzero : ∀ n, (∑ i, q (cluster i) *
      (normalizedDefect C (seed n) (refs n) (time n i + 1) -
        normalizedDefect C (seed n) (refs n) (time n i))) = 0)
    (hsep : ∀ i j, cluster i ≠ cluster j →
      Tendsto (fun n => ((time n i : ℤ) - time n j).natAbs) atTop atTop) :
    ∀ᶠ n in atTop, ∀ k,
      (∑ i ∈ Finset.univ.filter (fun i => cluster i = k), q (cluster i) *
        (normalizedDefect C (seed n) (refs n) (time n i + 1) -
          normalizedDefect C (seed n) (refs n) (time n i))) = 0 := by
  have hsum : ∀ n, (∑ p : α × Bool, repairUnitCoefficient C cluster q before after p *
      (2 : ℚ) ^ repairUnitExponent (seed n) (time n) p / 3 ^ (time n p.1 + 1)) = 0 := by
    intro n
    rw [Fintype.sum_prod_type]
    simp_rw [← weighted_increment_eq_bool_sum C (seed n) (refs n) cluster q before after
      (time n) (hbefore n) (hafter n)]
    exact hzero n
  have hsep' : ∀ p r : α × Bool, cluster p.1 ≠ cluster r.1 →
      Tendsto (fun n => (((time n p.1 + 1 : ℕ) : ℤ) - (time n r.1 + 1)).natAbs)
        atTop atTop := by
    intro p r h
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_add_right_eq_sub] using hsep p.1 r.1 h
  have hev := eventually_cluster_sum_eq_zero_allow_zero
    (repairUnitCoefficient C cluster q before after) (fun p => cluster p.1)
    (fun n => repairUnitExponent (seed n) (time n))
    (fun n p => time n p.1 + 1) hsum hsep'
  filter_upwards [hev] with n hn k
  have hh := hn k
  rw [sum_filter_prod_fst] at hh
  simp_rw [← weighted_increment_eq_bool_sum C (seed n) (refs n) cluster q before after
    (time n) (hbefore n) (hafter n)] at hh
  exact hh

/-- An enumerated cluster's weighted repair sum is its weighted endpoint increment. -/
theorem weighted_cluster_sum_eq_endpoints {α κ : Type*} [Fintype α] [DecidableEq κ]
    (C : RationalPeriodicDictionary ι) (n : ℕ) (c : ℕ → ι)
    (cluster : α → κ) (q : κ → ℚ) (time : α → ℕ) (k : κ)
    {l u : ℕ} (hlu : l ≤ u) (hinj : Function.Injective time)
    (hcover : ∀ t, l ≤ t ∧ t < u ∧ ¬ GoodAt C n c t ↔
      ∃ i, cluster i = k ∧ time i = t) :
    (∑ i ∈ Finset.univ.filter (fun i => cluster i = k), q (cluster i) *
      (normalizedDefect C n c (time i + 1) - normalizedDefect C n c (time i))) =
      q k * (normalizedDefect C n c u - normalizedDefect C n c l) := by
  have hexp := normalizedDefect_eq_sum_enumerated_repairs C n c hlu time
    (Finset.univ.filter (fun i => cluster i = k)) hinj (by
      intro t
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hcover t)
  rw [hexp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- **Actual endpoint localization.** A fixed rational relation among separated
clusters of actual repairs eventually vanishes in every weighted cluster. -/
theorem eventually_weighted_cluster_endpoints_eq_zero
    {α κ : Type*} [Fintype α] [Fintype κ] [DecidableEq κ]
    (C : RationalPeriodicDictionary ι) (seed : ℕ → ℕ) (refs : ℕ → ℕ → ι)
    (cluster : α → κ) (q : κ → ℚ) (before after : α → ι) (time : ℕ → α → ℕ)
    (lo hi : ℕ → κ → ℕ)
    (horder : ∀ n k, lo n k ≤ hi n k)
    (hinj : ∀ n, Function.Injective (time n))
    (hcover : ∀ n k t, lo n k ≤ t ∧ t < hi n k ∧ ¬ GoodAt C (seed n) (refs n) t ↔
      ∃ i, cluster i = k ∧ time n i = t)
    (hbefore : ∀ n i, refs n (time n i) = before i)
    (hafter : ∀ n i, refs n (time n i + 1) = after i)
    (hzero : ∀ n, (∑ k, q k *
      (normalizedDefect C (seed n) (refs n) (hi n k) -
        normalizedDefect C (seed n) (refs n) (lo n k))) = 0)
    (hsep : ∀ i j, cluster i ≠ cluster j →
      Tendsto (fun n => ((time n i : ℤ) - time n j).natAbs) atTop atTop) :
    ∀ᶠ n in atTop, ∀ k, q k *
      (normalizedDefect C (seed n) (refs n) (hi n k) -
        normalizedDefect C (seed n) (refs n) (lo n k)) = 0 := by
  have hexp := fun n k => weighted_cluster_sum_eq_endpoints C (seed n) (refs n)
    cluster q (time n) k (horder n k) (hinj n) (hcover n k)
  have hsum : ∀ n, (∑ i, q (cluster i) *
      (normalizedDefect C (seed n) (refs n) (time n i + 1) -
        normalizedDefect C (seed n) (refs n) (time n i))) = 0 := by
    intro n
    rw [← Finset.sum_fiberwise Finset.univ cluster]
    simp_rw [hexp n]
    exact hzero n
  have hev := eventually_weighted_repair_cluster_sum_eq_zero C seed refs cluster q before after time
    hbefore hafter hsum hsep
  filter_upwards [hev] with n hn k
  rw [← hexp n k]
  exact hn k

/-- **Exceptional-subspace contradiction for actual Collatz clusters.**
A nonzero weighted cluster increment cannot persist in a separated family
satisfying the fixed endpoint relation. -/
theorem no_separated_actual_cluster_relation
    {α κ : Type*} [Fintype α] [Fintype κ] [DecidableEq κ]
    (C : RationalPeriodicDictionary ι) (seed : ℕ → ℕ) (refs : ℕ → ℕ → ι)
    (cluster : α → κ) (q : κ → ℚ) (before after : α → ι) (time : ℕ → α → ℕ)
    (lo hi : ℕ → κ → ℕ)
    (horder : ∀ n k, lo n k ≤ hi n k)
    (hinj : ∀ n, Function.Injective (time n))
    (hcover : ∀ n k t, lo n k ≤ t ∧ t < hi n k ∧ ¬ GoodAt C (seed n) (refs n) t ↔
      ∃ i, cluster i = k ∧ time n i = t)
    (hbefore : ∀ n i, refs n (time n i) = before i)
    (hafter : ∀ n i, refs n (time n i + 1) = after i)
    (hzero : ∀ n, (∑ k, q k *
      (normalizedDefect C (seed n) (refs n) (hi n k) -
        normalizedDefect C (seed n) (refs n) (lo n k))) = 0)
    (hsep : ∀ i j, cluster i ≠ cluster j →
      Tendsto (fun n => ((time n i : ℤ) - time n j).natAbs) atTop atTop)
    (k : κ)
    (hnonzero : ∀ n, q k *
      (normalizedDefect C (seed n) (refs n) (hi n k) -
        normalizedDefect C (seed n) (refs n) (lo n k)) ≠ 0) : False := by
  obtain ⟨n, hn⟩ := (eventually_weighted_cluster_endpoints_eq_zero C seed refs cluster q before after
    time lo hi horder hinj hcover hbefore hafter hzero hsep).exists
  exact hnonzero n (hn k)

end CollatzPrefix
