import BoundedDeviations

/-!
# Zero-increment clusters follow the exact reference orbit

A finite positive-exponent affine word with odd 2-adic endpoints must follow
its unique exact accelerated rational orbit. The proof runs backwards from
the endpoint and does not require a denominator-divisibility argument.
-/

namespace CollatzPrefix

/-- A nonzero rational with exact 2-adic valuation zero. Nonzeroness is
explicit because `padicValRat` assigns the value zero to zero itself. -/
def TwoAdicOdd (q : ℚ) : Prop := q ≠ 0 ∧ padicValRat 2 q = 0

theorem two_power_valuation (a : ℕ) : padicValRat 2 ((2 : ℚ) ^ a) = a := by
  rw [padicValRat.pow]
  change _ * padicValRat 2 ((2 : ℕ) : ℚ) = _
  rw [padicValRat.self (by norm_num), mul_one]

/-- A positive-exponent affine predecessor of an odd rational is odd. -/
theorem twoAdicOdd_predecessor {q r : ℚ} {a : ℕ}
    (ha : 0 < a) (hr : TwoAdicOdd r)
    (hs : affineStep a q = r) : TwoAdicOdd q := by
  have htwo : (2 : ℚ) ^ a ≠ 0 := by positivity
  have heq : (2 : ℚ) ^ a * r = 3 * q + 1 := by
    simpa [mul_comm] using ((div_eq_iff htwo).mp hs).symm
  have hval : padicValRat 2 ((2 : ℚ) ^ a * r) = a := by
    rw [padicValRat.mul htwo hr.1, two_power_valuation, hr.2, add_zero]
  have hsub : (2 : ℚ) ^ a * r - 1 ≠ 0 := by
    intro hz
    have he : (2 : ℚ) ^ a * r = 1 := sub_eq_zero.mp hz
    rw [he, padicValRat.one] at hval
    omega
  have hsubval : padicValRat 2 ((2 : ℚ) ^ a * r - 1) = 0 := by
    have he := padicValRat.add_eq_min (p := 2)
      (q := (2 : ℚ) ^ a * r) (r := -1)
      (by simpa [sub_eq_add_neg] using hsub) (mul_ne_zero htwo hr.1) (by norm_num)
      (by simpa [hval] using (show (a : ℤ) ≠ 0 by omega))
    simpa [sub_eq_add_neg, hval, min_eq_right (show (0 : ℤ) ≤ a by omega)] using he
  have hqeq : q = ((2 : ℚ) ^ a * r - 1) / 3 := by linarith [heq]
  rw [TwoAdicOdd, hqeq]
  constructor
  · exact div_ne_zero hsub (by norm_num)
  · rw [padicValRat.div hsub (by norm_num), hsubval]
    have hthree : padicValRat 2 (3 : ℚ) = 0 := by
      change padicValRat 2 ((3 : ℕ) : ℚ) = 0
      rw [padicValRat.of_nat]
      norm_cast
      exact padicValNat.eq_zero_of_not_dvd (by norm_num)
    simp [hthree]

/-- Oddness propagates backwards through an arbitrary finite positive-exponent
word, without any integrality assumption on intermediate rationals. -/
theorem affine_run_twoAdicOdd (q : ℕ → ℚ) (a : ℕ → ℕ) (h : ℕ)
    (ha : ∀ t < h, 0 < a t)
    (hs : ∀ t < h, affineStep (a t) (q t) = q (t + 1))
    (he : TwoAdicOdd (q h)) : ∀ t ≤ h, TwoAdicOdd (q t) := by
  induction h with
  | zero => intro t ht; simpa only [Nat.le_zero.mp ht] using he
  | succ h ih =>
    have hh := twoAdicOdd_predecessor (ha h (by omega)) he (hs h (by omega))
    have hp := ih (fun t ht => ha t (by omega)) (fun t ht => hs t (by omega)) hh
    intro t ht
    by_cases ht' : t ≤ h
    · exact hp t ht'
    · have : t = h + 1 := by omega
      simpa only [this] using he

/-- An odd output identifies the exponent as the exact 2-adic valuation. -/
theorem affine_exponent_exact {q r : ℚ} {a : ℕ}
    (hr : TwoAdicOdd r) (hs : affineStep a q = r) :
    padicValRat 2 (3 * q + 1) = a := by
  have htwo : (2 : ℚ) ^ a ≠ 0 := by positivity
  have heq : 3 * q + 1 = (2 : ℚ) ^ a * r := by
    exact (div_eq_iff htwo).mp hs |>.trans (mul_comm _ _)
  rw [heq, padicValRat.mul htwo hr.1, two_power_valuation, hr.2, add_zero]

namespace RationalPeriodicDictionary
variable {ι : Type*} [Fintype ι] (C : RationalPeriodicDictionary ι)

theorem value_ne_zero (i : ι) : C.value i ≠ 0 := by
  have hp : C.numerator i ≠ 0 := by
    intro hz
    have ho := C.numerator_odd i
    simp [hz, Int.odd_iff] at ho
  exact div_ne_zero (by exact_mod_cast hp)
    (by exact_mod_cast ne_of_gt C.denominator_pos)

theorem value_twoAdicOdd (i : ι) : TwoAdicOdd (C.value i) :=
  ⟨C.value_ne_zero i, C.value_valuation i⟩

/-- Any positive-exponent affine path from one dictionary value to another
follows the exact dictionary trajectory at every step. -/
theorem affine_path_follows_dictionary (q : ℕ → ℚ) (a : ℕ → ℕ) (h : ℕ)
    (c₀ c₁ : ι) (ha : ∀ t < h, 0 < a t)
    (hs : ∀ t < h, affineStep (a t) (q t) = q (t + 1))
    (hstart : q 0 = C.value c₀) (hend : q h = C.value c₁) :
    (∀ t ≤ h, q t = C.value ((C.next^[t]) c₀)) ∧
    (∀ t < h, a t = C.exponent ((C.next^[t]) c₀)) := by
  have hodd := affine_run_twoAdicOdd q a h ha hs
    (by rw [hend]; exact C.value_twoAdicOdd c₁)
  have hv : ∀ t ≤ h, q t = C.value ((C.next^[t]) c₀) := by
    intro t ht
    induction t with
    | zero => simpa using hstart
    | succ t ih =>
      have hprev := ih (by omega)
      have ha' : a t = C.exponent ((C.next^[t]) c₀) := by
        have hval := affine_exponent_exact (hodd (t + 1) (by omega)) (hs t (by omega))
        rw [hprev, C.exponent_eq_valuation] at hval
        exact_mod_cast hval.symm
      rw [← hs t (by omega), hprev, ha', C.value_step]
      simp only [Function.iterate_succ_apply']
  refine ⟨hv, ?_⟩
  intro t ht
  have hval := affine_exponent_exact (hodd (t + 1) (by omega)) (hs t ht)
  rw [hv t (by omega), C.exponent_eq_valuation] at hval
  exact_mod_cast hval.symm

/-- Distinct dictionary values turn endpoint value equality into literal
endpoint label equality, so replacement preserves both boundary labels. -/
theorem affine_path_endpoint_label (hinj : Function.Injective C.value)
    (q : ℕ → ℚ) (a : ℕ → ℕ) (h : ℕ) (c₀ c₁ : ι)
    (ha : ∀ t < h, 0 < a t)
    (hs : ∀ t < h, affineStep (a t) (q t) = q (t + 1))
    (hstart : q 0 = C.value c₀) (hend : q h = C.value c₁) :
    (C.next^[h]) c₀ = c₁ := by
  apply hinj
  exact ((C.affine_path_follows_dictionary q a h c₀ c₁ ha hs hstart hend).1 h le_rfl).symm.trans hend

end RationalPeriodicDictionary

/-- Evaluate a finite affine word, retaining its intermediate values. -/
def affineRun (a : ℕ → ℕ) (q : ℚ) : ℕ → ℚ
  | 0 => q
  | t + 1 => affineStep (a t) (affineRun a q t)

/-- The sum of the exponents before time `h`. -/
def affineExponentSum (a : ℕ → ℕ) (h : ℕ) : ℕ :=
  ∑ t ∈ Finset.range h, a t

/-- Exact cancellation of the linear expansion of an affine word. -/
theorem affine_run_difference (x : ℕ → ℚ) (a : ℕ → ℕ) (q : ℚ) (h : ℕ)
    (hs : ∀ t < h, affineStep (a t) (x t) = x (t + 1)) :
    (2 : ℚ) ^ affineExponentSum a h / 3 ^ h *
      (x h - affineRun a q h) = x 0 - q := by
  induction h with
  | zero => simp [affineExponentSum, affineRun]
  | succ h ih =>
    have hp := ih (fun t ht => hs t (by omega))
    rw [affineExponentSum, Finset.sum_range_succ]
    rw [← hs h (by omega), affineRun]
    rw [defect_unchanged]
    exact hp

/-- Zero change in the normalized endpoint defect is exactly the assertion
that the affine word sends the initial reference to the terminal reference. -/
theorem zero_normalized_defect_endpoint (x : ℕ → ℚ) (a : ℕ → ℕ)
    (q r : ℚ) (h : ℕ)
    (hs : ∀ t < h, affineStep (a t) (x t) = x (t + 1))
    (hz : (2 : ℚ) ^ affineExponentSum a h / 3 ^ h * (x h - r) = x 0 - q) :
    affineRun a q h = r := by
  have hd := affine_run_difference x a q h hs
  have hw : (2 : ℚ) ^ affineExponentSum a h / 3 ^ h ≠ 0 := by positivity
  have he : x h - affineRun a q h = x h - r :=
    mul_left_cancel₀ hw (hd.trans hz.symm)
  linarith

namespace RationalPeriodicDictionary
variable {ι : Type*} [Fintype ι] (C : RationalPeriodicDictionary ι)

/-- The zero-cluster lemma: when the normalized defect has zero increment,
all internal reference labels can be replaced by genuine dictionary steps.
The replacement agrees with both original endpoint labels and has no repairs. -/
theorem zero_cluster_replacement (hinj : Function.Injective C.value)
    (x : ℕ → ℚ) (a : ℕ → ℕ) (h : ℕ) (c₀ c₁ : ι)
    (ha : ∀ t < h, 0 < a t)
    (hs : ∀ t < h, affineStep (a t) (x t) = x (t + 1))
    (hz : (2 : ℚ) ^ affineExponentSum a h / 3 ^ h *
      (x h - C.value c₁) = x 0 - C.value c₀) :
    ∃ c : ℕ → ι, c 0 = c₀ ∧ c h = c₁ ∧
      ∀ t < h, c (t + 1) = C.next (c t) ∧ a t = C.exponent (c t) := by
  let q := affineRun a (C.value c₀)
  have hq : ∀ t < h, affineStep (a t) (q t) = q (t + 1) := fun _ _ => rfl
  have hq₀ : q 0 = C.value c₀ := rfl
  have hqh : q h = C.value c₁ := zero_normalized_defect_endpoint x a _ _ h hs hz
  have hp := C.affine_path_follows_dictionary q a h c₀ c₁ ha hq hq₀ hqh
  refine ⟨fun t => (C.next^[t]) c₀, rfl, ?_, ?_⟩
  · exact C.affine_path_endpoint_label hinj q a h c₀ c₁ ha hq hq₀ hqh
  · intro t ht
    exact ⟨by simp only [Function.iterate_succ_apply'], hp.2 t ht⟩

/-- The same replacement statement with arbitrary initial time and accumulated
exponent, as in the paper's global normalization `Z_t = 2^A_t / 3^t · (n_t-c_t)`.
The nonzero common scale cancels, so no bound on either offset is needed. -/
theorem zero_cluster_replacement_shifted (hinj : Function.Injective C.value)
    (x : ℕ → ℚ) (a : ℕ → ℕ) (h s A : ℕ) (c₀ c₁ : ι)
    (ha : ∀ t < h, 0 < a t)
    (hs : ∀ t < h, affineStep (a t) (x t) = x (t + 1))
    (hz : (2 : ℚ) ^ (A + affineExponentSum a h) / 3 ^ (s + h) *
      (x h - C.value c₁) = 2 ^ A / 3 ^ s * (x 0 - C.value c₀)) :
    ∃ c : ℕ → ι, c 0 = c₀ ∧ c h = c₁ ∧
      ∀ t < h, c (t + 1) = C.next (c t) ∧ a t = C.exponent (c t) := by
  apply C.zero_cluster_replacement hinj x a h c₀ c₁ ha hs
  have hw : (2 : ℚ) ^ A / 3 ^ s ≠ 0 := by positivity
  apply mul_left_cancel₀ hw
  calc
    2 ^ A / 3 ^ s * (2 ^ affineExponentSum a h / 3 ^ h * (x h - C.value c₁)) =
      2 ^ (A + affineExponentSum a h) / 3 ^ (s + h) * (x h - C.value c₁) := by
        simp only [pow_add]
        field_simp
    _ = _ := hz

end RationalPeriodicDictionary
end CollatzPrefix
