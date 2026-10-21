import DiophantineApproximation.UnitEquationSeveral
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.Logic.Equiv.Option
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring

/-!
Exceptional-subspace elimination for bounded Collatz repair clusters.
The arithmetic input is the proved nondegenerate unit-equation theorem from
`DiophantineApproximation.UnitEquationSeveral` in Ralf Stephan's
Subspace-Theorems repository, commit 09835cb23557ae5ae0cf55a9c4ab9055f5d60338
(Apache 2.0). The minimal-subsum extraction proof below is adapted from that source.

The final theorems prove uniform cluster localization and its sequence contradiction.
They do not by themselves prove the paper's preceding Collatz reductions or height estimates.
-/
namespace CollatzPrefix.ClusterElimination

open Finset

variable {ι : Type*} [Fintype ι]

/-- A zero sum with no proper nonempty vanishing subsum. -/
def MinimalZero (z : ι → ℚ) : Prop :=
  (∑ i, z i) = 0 ∧
  ∀ I : Finset ι, I.Nonempty → I ≠ univ → (∑ i ∈ I, z i) ≠ 0

/-- Remove a distinguished term from a minimal zero sum and normalize it to one. -/
theorem normalized_unit_equation (a x : Option ι → ℚˣ)
    (hz : MinimalZero (fun i => (a i : ℚ) * x i)) :
    (∑ i, ((-(a (some i) / a none) : ℚˣ) : ℚ) *
      (x (some i) / x none : ℚˣ)) = 1 ∧
    ∀ I : Finset ι, I.Nonempty →
      (∑ i ∈ I, ((-(a (some i) / a none) : ℚˣ) : ℚ) *
        (x (some i) / x none : ℚˣ)) ≠ 0 := by
  classical
  have hterm (i : ι) :
      ((-(a (some i) / a none) : ℚˣ) : ℚ) *
        (x (some i) / x none : ℚˣ) =
      -((a (some i) : ℚ) * x (some i)) / ((a none : ℚ) * x none) := by
    simp only [Units.val_neg, Units.val_div_eq_div_val]
    field_simp
  have hden : (a none : ℚ) * x none ≠ 0 := mul_ne_zero (a none).ne_zero (x none).ne_zero
  constructor
  · have hs := hz.1
    rw [Fintype.sum_option] at hs
    simp_rw [hterm]
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
    have he : -(∑ i, (a (some i) : ℚ) * x (some i)) = (a none : ℚ) * x none := by
      linarith
    rw [he, div_self hden]
  · intro I hI hzero
    let J : Finset (Option ι) := I.map ⟨some, Option.some_injective ι⟩
    have hJ : J.Nonempty := hI.map
    have hproper : J ≠ univ := by
      intro h
      have : (none : Option ι) ∈ J := h.symm ▸ mem_univ _
      simp [J] at this
    apply hz.2 J hJ hproper
    simp_rw [hterm] at hzero
    rw [← Finset.sum_div, Finset.sum_neg_distrib] at hzero
    have hs : (∑ i ∈ I, (a (some i) : ℚ) * x (some i)) = 0 := by
      exact neg_eq_zero.mp ((div_eq_zero_iff).mp hzero |>.resolve_right hden)
    simpa [J] using hs

/-- Reindexing does not change minimality. -/
theorem MinimalZero.comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι)
    {z : ι → ℚ} (hz : MinimalZero z) : MinimalZero (z ∘ e) := by
  classical
  constructor
  · simpa [Function.comp_def] using (e.sum_comp z).trans hz.1
  · intro I hI hproper hzero
    let J := I.map e.toEmbedding
    have hJ : J.Nonempty := hI.map
    have hJproper : J ≠ univ := by
      intro h
      apply hproper
      apply Finset.eq_univ_of_forall
      intro i
      have hi : e i ∈ J := h.symm ▸ mem_univ _
      simpa [J] using hi
    apply hz.2 J hJ hJproper
    simpa [J, Function.comp_def] using hzero

omit [Fintype ι] in
/-- Extract a minimal vanishing subsum. Adapted from Ralf Stephan's
`NumberField.exists_subset_nonempty_sum_eq_zero_forall_ne_zero`
(Subspace-Theorems, Apache 2.0). -/
theorem exists_minimal_zero_subset (z : ι → ℚ) {s : Finset ι}
    (hs : s.Nonempty) (h0 : ∑ i ∈ s, z i = 0) :
    ∃ J ⊆ s, J.Nonempty ∧ ∑ i ∈ J, z i = 0 ∧
      ∀ I ⊆ J, I.Nonempty → I ≠ J → ∑ i ∈ I, z i ≠ 0 := by
  classical
  obtain ⟨J, hJ, hmin⟩ :=
    (s.powerset.filter fun J ↦ J.Nonempty ∧ ∑ i ∈ J, z i = 0).exists_min_image
      Finset.card ⟨s, by simp [hs, h0]⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hJ
  refine ⟨J, hJ.1, hJ.2.1, hJ.2.2, fun I hIJ hI hne hI0 ↦ ?_⟩
  have hlt : I.card < J.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hIJ, hne⟩)
  exact hlt.not_ge (hmin _ (by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hIJ.trans hJ.1, hI, hI0⟩))

omit [Fintype ι] in
/-- If every minimal zero subsum is confined to one cluster, each cluster sums to zero. -/
theorem cluster_sum_eq_zero_of_minimal_monochromatic {κ : Type*} [DecidableEq κ]
    (z : ι → ℚ) (cluster : ι → κ) (s : Finset ι)
    (hs : ∑ i ∈ s, z i = 0)
    (hmono : ∀ J ⊆ s, J.Nonempty → (∑ i ∈ J, z i) = 0 →
      (∀ I ⊆ J, I.Nonempty → I ≠ J → ∑ i ∈ I, z i ≠ 0) →
      ∀ i ∈ J, ∀ j ∈ J, cluster i = cluster j)
    (c : κ) : ∑ i ∈ s.filter (fun i => cluster i = c), z i = 0 := by
  classical
  revert hs hmono
  refine Finset.strongInductionOn s ?_
  intro s ih hs hmono
  by_cases hempty : s = ∅
  · simp [hempty]
  obtain ⟨J, hJs, hJ, hJzero, hJmin⟩ :=
    exists_minimal_zero_subset z (Finset.nonempty_iff_ne_empty.mpr hempty) hs
  have hrest : ∑ i ∈ s \ J, z i = 0 := by
    have := Finset.sum_sdiff hJs (f := z)
    rw [hs, hJzero, add_zero] at this
    exact this
  have hrestc := ih (s \ J) (Finset.sdiff_ssubset hJs hJ) hrest
    (fun K hK => hmono K (hK.trans Finset.sdiff_subset))
  have hJc : ∑ i ∈ J.filter (fun i => cluster i = c), z i = 0 := by
    obtain ⟨j, hj⟩ := hJ
    by_cases hjc : cluster j = c
    · have heq : J.filter (fun i => cluster i = c) = J := by
        apply Finset.filter_eq_self.mpr
        intro i hi
        exact (hmono J hJs ⟨j, hj⟩ hJzero hJmin i hi j hj).trans hjc
      rw [heq, hJzero]
    · have heq : J.filter (fun i => cluster i = c) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i hi hic
        apply hjc
        exact (hmono J hJs ⟨j, hj⟩ hJzero hJmin j hj i hi).trans hic
      simp [heq]
  have hsub : J.filter (fun i => cluster i = c) ⊆ s.filter (fun i => cluster i = c) :=
    Finset.filter_subset_filter _ hJs
  have hdiff : s.filter (fun i => cluster i = c) \ J.filter (fun i => cluster i = c) =
      (s \ J).filter (fun i => cluster i = c) := by
    ext i
    simp only [mem_sdiff, mem_filter]
    tauto
  have hsum := Finset.sum_sdiff hsub (f := z)
  rw [hdiff, hrestc, hJc, zero_add] at hsum
  exact hsum.symm

/-- Normalized minimal zero sums have only finitely many projective vectors. -/
theorem finite_normalized_minimal_zero_option (Γ : Subgroup ℚˣ)
    (a : Option ι → ℚˣ)
    (hfinite : {y : ι → ℚˣ | (∀ i, y i ∈ Γ) ∧
      (∑ i, ((-(a (some i) / a none) : ℚˣ) : ℚ) * y i) = 1 ∧
      ∀ I : Finset ι, I.Nonempty →
        (∑ i ∈ I, ((-(a (some i) / a none) : ℚˣ) : ℚ) * y i) ≠ 0}.Finite) :
    {w : Option ι → ℚˣ | ∃ x : Option ι → ℚˣ,
      (∀ i, x i ∈ Γ) ∧ MinimalZero (fun i => (a i : ℚ) * x i) ∧
      w = fun i => (a i * x i) / (a none * x none)}.Finite := by
  classical
  let f : (ι → ℚˣ) → (Option ι → ℚˣ) :=
    fun y i => i.elim 1 (fun j => a (some j) / a none * y j)
  apply (hfinite.image f).subset
  rintro w ⟨x, hx, hz, rfl⟩
  refine ⟨fun i => x (some i) / x none, ?_, ?_⟩
  · exact ⟨fun i => Γ.div_mem (hx _) (hx _), normalized_unit_equation a x hz⟩
  · funext i
    cases i with
    | none => simp [f]
    | some j => dsimp [f]; exact div_mul_div_comm _ _ _ _

/-- All pairwise term ratios occurring in minimal zero sums. -/
def minimalZeroRatios (Γ : Subgroup ℚˣ) (a : ι → ℚˣ) : Set ℚˣ :=
  {r | ∃ x : ι → ℚˣ, (∀ i, x i ∈ Γ) ∧
    MinimalZero (fun i => (a i : ℚ) * x i) ∧
    ∃ i j, r = (a i * x i) / (a j * x j)}

/-- Pairwise ratios are images of the normalized projective vectors. -/
theorem finite_minimalZeroRatios_option (Γ : Subgroup ℚˣ) (a : Option ι → ℚˣ)
    (hfinite : {w : Option ι → ℚˣ | ∃ x : Option ι → ℚˣ,
      (∀ i, x i ∈ Γ) ∧ MinimalZero (fun i => (a i : ℚ) * x i) ∧
      w = fun i => (a i * x i) / (a none * x none)}.Finite) :
    (minimalZeroRatios Γ a).Finite := by
  classical
  have hp := hfinite.prod (Set.finite_univ : (Set.univ : Set (Option ι × Option ι)).Finite)
  apply (hp.image (fun p => p.1 p.2.1 / p.1 p.2.2)).subset
  rintro r ⟨x, hx, hz, i, j, rfl⟩
  refine ⟨(fun k => (a k * x k) / (a none * x none), (i, j)), ?_, ?_⟩
  · exact ⟨⟨x, hx, hz, rfl⟩, Set.mem_univ _⟩
  · dsimp
    simp only [div_div_div_cancel_right]

/-- A finite reindexing preserves the set of projective ratios. -/
theorem minimalZeroRatios_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι)
    (Γ : Subgroup ℚˣ) (a : ι → ℚˣ) :
    minimalZeroRatios Γ a ⊆ minimalZeroRatios Γ (a ∘ e) := by
  rintro r ⟨x, hx, hz, i, j, rfl⟩
  refine ⟨x ∘ e, fun i => hx (e i), hz.comp_equiv e, e.symm i, e.symm j, ?_⟩
  simp

/-- S-unit finiteness gives finite projective term ratios for minimal zero sums.
The only Diophantine input is the proved unit-equation theorem. -/
theorem finite_minimalZeroRatios (Γ : Subgroup ℚˣ) (hΓ : Γ.FG)
    (a : ι → ℚˣ) : (minimalZeroRatios Γ a).Finite := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    have he : minimalZeroRatios Γ a = ∅ := by
      ext r
      simp [minimalZeroRatios]
    rw [he]
    exact Set.finite_empty
  | inr h =>
    let i₀ : ι := Classical.choice h
    let e := Equiv.optionSubtypeNe i₀
    apply (finite_minimalZeroRatios_option Γ (a ∘ e) ?_).subset
      (minimalZeroRatios_equiv e Γ a)
    apply finite_normalized_minimal_zero_option
    exact NumberField.finite_setOf_sum_mem_eq_one Γ hΓ _

/-- The two generators for the unit group used by the repair expansion. -/
def twoUnit : ℚˣ := Units.mk0 2 (by norm_num)
def threeUnit : ℚˣ := Units.mk0 3 (by norm_num)

/-- The multiplicative group generated by 2 and 3. -/
def group23 : Subgroup ℚˣ := Subgroup.closure ({twoUnit, threeUnit} : Set ℚˣ)

theorem group23_fg : group23.FG :=
  (Subgroup.fg_iff _).mpr ⟨_, rfl, Set.toFinite _⟩

/-- A positive `{2,3}`-unit. -/
def unit23 (u t : ℕ) : ℚˣ := twoUnit ^ u / threeUnit ^ t

@[simp] theorem unit23_val (u t : ℕ) :
    (unit23 u t : ℚ) = (2 : ℚ) ^ u / 3 ^ t := by
  simp [unit23, twoUnit, threeUnit]

theorem unit23_mem (u t : ℕ) : unit23 u t ∈ group23 := by
  apply Subgroup.div_mem
  · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _

/-- The 3-adic valuation records exactly the time exponent. -/
theorem valuation_term (a : ℚˣ) (u t : ℕ) :
    padicValRat 3 ((a : ℚ) * (2 : ℚ) ^ u / 3 ^ t) = padicValRat 3 a - t := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : padicValRat 3 (2 : ℚ) = 0 := by
    change padicValRat 3 ((2 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by decide)]
    rfl
  have h3 : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by norm_num)
  rw [padicValRat.div (mul_ne_zero a.ne_zero (pow_ne_zero _ (by norm_num)))
      (pow_ne_zero _ (by norm_num)),
    padicValRat.mul a.ne_zero (pow_ne_zero _ (by norm_num)),
    padicValRat.pow 2, padicValRat.pow 3, h2, h3]
  simp

/-- For fixed coefficient labels, a fixed projective ratio determines a time difference. -/
theorem time_difference_eq_valuation (a b : ℚˣ) (u v t s : ℕ) :
    (t : ℤ) - s = padicValRat 3 a - padicValRat 3 b -
      padicValRat 3 ((a * unit23 u t / (b * unit23 v s) : ℚˣ) : ℚ) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Units.val_div_eq_div_val,
    padicValRat.div (a * unit23 u t).ne_zero (b * unit23 v s).ne_zero]
  simp only [Units.val_mul, unit23_val, ← mul_div_assoc]
  rw [valuation_term, valuation_term]
  ring

/-- Minimal zero sums with fixed coefficients have uniformly bounded time differences. -/
theorem exists_minimal_time_bound (a : ι → ℚˣ) :
    ∃ M : ℕ, ∀ u t : ι → ℕ,
      MinimalZero (fun i => (a i : ℚ) * (2 : ℚ) ^ u i / 3 ^ t i) →
      ∀ i j, ((t i : ℤ) - t j).natAbs ≤ M := by
  classical
  have hfinite := (finite_minimalZeroRatios group23 group23_fg a).prod
    (Set.finite_univ : (Set.univ : Set (ι × ι)).Finite)
  let f : ℚˣ × (ι × ι) → ℕ := fun p =>
    (padicValRat 3 (a p.2.1) - padicValRat 3 (a p.2.2) -
      padicValRat 3 (p.1 : ℚ)).natAbs
  obtain ⟨M, hM⟩ := (hfinite.image f).bddAbove
  refine ⟨M, fun u t hz i j => ?_⟩
  rw [time_difference_eq_valuation (a i) (a j) (u i) (u j) (t i) (t j)]
  apply hM
  refine ⟨(a i * unit23 (u i) (t i) / (a j * unit23 (u j) (t j)), (i, j)), ?_, rfl⟩
  refine ⟨?_, Set.mem_univ _⟩
  refine ⟨fun k => unit23 (u k) (t k), fun k => unit23_mem _ _, ?_, i, j, rfl⟩
  simpa only [unit23_val, ← mul_div_assoc] using hz

omit [Fintype ι] in
/-- A minimal zero sum on a finite subset is a minimal zero sum on its subtype. -/
theorem minimalZero_subtype (z : ι → ℚ) (J : Finset ι)
    (hzero : ∑ i ∈ J, z i = 0)
    (hmin : ∀ I ⊆ J, I.Nonempty → I ≠ J → ∑ i ∈ I, z i ≠ 0) :
    MinimalZero (fun i : J => z i) := by
  classical
  constructor
  · simpa only [← Finset.sum_attach J z, Finset.univ_eq_attach] using hzero
  · intro I hI hproper hIz
    let e : J ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
    let K := I.map e
    have hKJ : K ⊆ J := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact j.property
    have hKproper : K ≠ J := by
      intro h
      apply hproper
      apply Finset.eq_univ_of_forall
      intro i
      have hi : (i : ι) ∈ K := h.symm ▸ i.property
      obtain ⟨j, hj, heq⟩ := Finset.mem_map.mp hi
      have : j = i := Subtype.ext heq
      exact this ▸ hj
    apply hmin K hKJ hI.map hKproper
    simpa [K, e] using hIz

/-- One bound works for every minimal subsum of a fixed list of coefficients. -/
theorem exists_subsum_time_bound (a : ι → ℚˣ) :
    ∃ M : ℕ, ∀ u t : ι → ℕ, ∀ J : Finset ι,
      (∑ i ∈ J, (a i : ℚ) * (2 : ℚ) ^ u i / 3 ^ t i) = 0 →
      (∀ I ⊆ J, I.Nonempty → I ≠ J →
        ∑ i ∈ I, (a i : ℚ) * (2 : ℚ) ^ u i / 3 ^ t i ≠ 0) →
      ∀ i ∈ J, ∀ j ∈ J, ((t i : ℤ) - t j).natAbs ≤ M := by
  classical
  choose M hM using fun J : Finset ι => exists_minimal_time_bound (fun i : J => a i)
  refine ⟨Finset.univ.sup M, fun u t J hzero hmin i hi j hj => ?_⟩
  have hbound := hM J (fun k => u k) (fun k => t k)
    (minimalZero_subtype (fun k => (a k : ℚ) * (2 : ℚ) ^ u k / 3 ^ t k) J hzero hmin)
    ⟨i, hi⟩ ⟨j, hj⟩
  exact hbound.trans (Finset.le_sup (Finset.mem_univ J))

/-- **Uniform localization of repair sums.** Once time gaps between different clusters
are sufficiently large, a vanishing sum of fixed-coefficient `{2,3}`-units vanishes
separately in every cluster. The bound depends only on the finite coefficient list.
No partition, subsequence, or constancy of projective ratios is assumed. -/
theorem exists_cluster_separation_bound {κ : Type*} [DecidableEq κ]
    (a : ι → ℚˣ) :
    ∃ M : ℕ, ∀ (cluster : ι → κ) (u t : ι → ℕ),
      (∑ i, (a i : ℚ) * (2 : ℚ) ^ u i / 3 ^ t i) = 0 →
      (∀ i j, cluster i ≠ cluster j → M < ((t i : ℤ) - t j).natAbs) →
      ∀ c, (∑ i ∈ Finset.univ.filter (fun i => cluster i = c),
        (a i : ℚ) * (2 : ℚ) ^ u i / 3 ^ t i) = 0 := by
  classical
  obtain ⟨M, hM⟩ := exists_subsum_time_bound a
  refine ⟨M, fun cluster u t hzero hsep c => ?_⟩
  apply cluster_sum_eq_zero_of_minimal_monochromatic _ cluster univ hzero
  intro J _ _ hJzero hJmin i hi j hj
  by_contra hne
  exact (hsep i j hne).not_ge (hM u t J hJzero hJmin i hi j hj)

/-- Rational-coefficient form of uniform cluster localization. -/
theorem exists_cluster_separation_bound_rat {κ : Type*} [DecidableEq κ]
    (a : ι → ℚ) (ha : ∀ i, a i ≠ 0) :
    ∃ M : ℕ, ∀ (cluster : ι → κ) (u t : ι → ℕ),
      (∑ i, a i * (2 : ℚ) ^ u i / 3 ^ t i) = 0 →
      (∀ i j, cluster i ≠ cluster j → M < ((t i : ℤ) - t j).natAbs) →
      ∀ c, (∑ i ∈ Finset.univ.filter (fun i => cluster i = c),
        a i * (2 : ℚ) ^ u i / 3 ^ t i) = 0 := by
  simpa using exists_cluster_separation_bound (κ := κ) (fun i => Units.mk0 (a i) (ha i))

/-- Sequence form: separated clusters of a vanishing repair sum eventually vanish individually. -/
theorem eventually_cluster_sum_eq_zero {κ : Type*} [DecidableEq κ]
    (a : ι → ℚ) (ha : ∀ i, a i ≠ 0) (cluster : ι → κ)
    (u t : ℕ → ι → ℕ)
    (hzero : ∀ n, (∑ i, a i * (2 : ℚ) ^ u n i / 3 ^ t n i) = 0)
    (hsep : ∀ i j, cluster i ≠ cluster j →
      Filter.Tendsto (fun n => ((t n i : ℤ) - t n j).natAbs)
        Filter.atTop Filter.atTop) :
    ∀ᶠ n in Filter.atTop, ∀ c,
      (∑ i ∈ Finset.univ.filter (fun i => cluster i = c),
        a i * (2 : ℚ) ^ u n i / 3 ^ t n i) = 0 := by
  obtain ⟨M, hM⟩ := exists_cluster_separation_bound_rat (κ := κ) a ha
  have hev : ∀ᶠ n in Filter.atTop, ∀ i j,
      cluster i ≠ cluster j → M < ((t n i : ℤ) - t n j).natAbs := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases h : cluster i = cluster j
    · exact Filter.Eventually.of_forall (fun _ hne => (hne h).elim)
    · exact ((hsep i j h).eventually_gt_atTop M).mono (fun _ hn _ => hn)
  exact hev.mono (fun n hn => hM cluster (u n) (t n) (hzero n) hn)

/-- **Exceptional-subspace contradiction.** A vanishing family of fixed-coefficient
repair sums cannot contain an everywhere nonzero cluster separated from the others. -/
theorem no_separated_nonzero_cluster {κ : Type*} [DecidableEq κ]
    (a : ι → ℚ) (ha : ∀ i, a i ≠ 0) (cluster : ι → κ)
    (u t : ℕ → ι → ℕ)
    (hzero : ∀ n, (∑ i, a i * (2 : ℚ) ^ u n i / 3 ^ t n i) = 0)
    (hsep : ∀ i j, cluster i ≠ cluster j →
      Filter.Tendsto (fun n => ((t n i : ℤ) - t n j).natAbs)
        Filter.atTop Filter.atTop)
    (c : κ)
    (hnonzero : ∀ n,
      (∑ i ∈ Finset.univ.filter (fun i => cluster i = c),
        a i * (2 : ℚ) ^ u n i / 3 ^ t n i) ≠ 0) : False := by
  obtain ⟨n, hn⟩ := (eventually_cluster_sum_eq_zero a ha cluster u t hzero hsep).exists
  exact hnonzero n (hn c)

end CollatzPrefix.ClusterElimination
