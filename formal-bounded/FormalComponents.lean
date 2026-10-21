import Mathlib.Data.Nat.ModEq
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic

/-!
Checked components of the two accompanying papers.
This file does NOT yet prove either paper's main asymptotic theorem.
No Collatz-specific assertion is introduced as an axiom.
-/
namespace CollatzPrefix

/-- The shortcut Collatz map on natural numbers, including zero. -/
def shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The first `r` parity bits, in chronological order. -/
def parityPrefix : ℕ → ℕ → List ℕ
  | 0, _ => []
  | r + 1, n => n % 2 :: parityPrefix r (shortcut n)

@[simp] theorem parityPrefix_length (r n : ℕ) :
    (parityPrefix r n).length = r := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih => simp [parityPrefix, ih]

theorem shortcut_even (n : ℕ) (h : n % 2 = 0) :
    2 * shortcut n = n := by
  simp only [shortcut, if_pos h]
  omega

theorem shortcut_odd (n : ℕ) (h : n % 2 = 1) :
    shortcut n = 3 * (n / 2) + 2 := by
  have he : n % 2 ≠ 0 := by omega
  simp only [shortcut, if_neg he]
  omega

theorem shortcut_odd_numerator (n : ℕ) (h : n % 2 = 1) :
    2 * shortcut n = 3 * n + 1 := by
  rw [shortcut_odd n h]
  omega

theorem shortcut_pos {n : ℕ} (hn : 0 < n) : 0 < shortcut n := by
  by_cases h : n % 2 = 0
  · have := shortcut_even n h
    omega
  · have hodd : n % 2 = 1 := by omega
    have := shortcut_odd_numerator n hodd
    omega

/-- Parity words determine their starting residue modulo `2^r`. -/
theorem parityPrefix_residue (r : ℕ) : ∀ n m : ℕ,
    parityPrefix r n = parityPrefix r m → Nat.ModEq (2 ^ r) n m := by
  induction r with
  | zero => intro n m _; simp [Nat.ModEq]; omega
  | succ r ih =>
    intro n m h
    have bits := List.cons.inj h
    have hp : n % 2 = m % 2 := bits.1
    have ht : Nat.ModEq (2 ^ r) (shortcut n) (shortcut m) := ih _ _ bits.2
    have hquot : Nat.ModEq (2 ^ r) (n / 2) (m / 2) := by
      by_cases he : n % 2 = 0
      · have hm : m % 2 = 0 := by omega
        simpa [shortcut, he, hm] using ht
      · have hn : n % 2 = 1 := by omega
        have hm : m % 2 = 1 := by omega
        rw [shortcut_odd n hn, shortcut_odd m hm] at ht
        have hmul := ht.add_right_cancel' 2
        exact hmul.cancel_left_of_coprime
          ((show Nat.Coprime 2 3 by decide).pow_left r).gcd_eq_one
    have hdoubled := (hquot.mul_left' 2).add_right (n % 2)
    have hn : 2 * (n / 2) + n % 2 = n := by omega
    have hm : 2 * (m / 2) + n % 2 = m := by omega
    simpa [hn, hm, pow_succ, Nat.mul_comm] using hdoubled

/-- Consequently, distinct starts below `2^r` have distinct parity words. -/
theorem parityPrefix_injective_below (r : ℕ) {n m : ℕ}
    (hn : n < 2 ^ r) (hm : m < 2 ^ r)
    (h : parityPrefix r n = parityPrefix r m) : n = m := by
  have hmod := parityPrefix_residue r n m h
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] using hmod

/-- The finite sampling map used in the entropy argument is injective. -/
theorem sampled_words_injective {M r : ℕ} (x : Fin M → ℕ)
    (hx : Function.Injective x) (hb : ∀ i, x i < 2 ^ r) :
    Function.Injective (fun i => parityPrefix r (x i)) := by
  intro i j h
  exact hx (parityPrefix_injective_below r (hb i) (hb j) h)

section RationalRepairs

/-- An actual rational affine step with a chosen integer exponent. -/
def affineStep (a : ℕ) (n : ℚ) : ℚ := (3 * n + 1) / 2 ^ a

/-- Exact normalized defect increment (paper 2, equation (1)). -/
theorem defect_increment (n c c' : ℚ) (a A t : ℕ) :
    (2 : ℚ) ^ (A + a) / 3 ^ (t + 1) * (affineStep a n - c') -
      2 ^ A / 3 ^ t * (n - c) =
    ((3 * c + 1) * 2 ^ A - c' * 2 ^ (A + a)) / 3 ^ (t + 1) := by
  unfold affineStep
  simp only [pow_add, pow_one]
  field_simp
  ring

/-- A genuine matching reference step has zero defect increment. -/
theorem defect_unchanged (n c : ℚ) (a A t : ℕ) :
    (2 : ℚ) ^ (A + a) / 3 ^ (t + 1) *
      (affineStep a n - affineStep a c) =
    2 ^ A / 3 ^ t * (n - c) := by
  unfold affineStep
  simp only [pow_add, pow_one]
  field_simp
  ring

/-- The ratio identity, under its actual nonzero-denominator conditions. -/
theorem defect_ratio (n n' c c' : ℚ) (a A t : ℕ)
    (hn : n ≠ 0) (hn' : n' ≠ 0) (hd : n - c ≠ 0)
    (hstep : n' = affineStep a n) :
    ((2 : ℚ) ^ (A + a) / 3 ^ (t + 1) * (n' - c')) /
      (2 ^ A / 3 ^ t * (n - c)) =
    (1 + 1 / (3 * n)) * (1 - c' / n') / (1 - c / n) := by
  have hnc : 1 - c / n ≠ 0 := by
    intro h
    have he : n - c = 0 := by
      field_simp at h
      linarith
    exact hd he
  have hrel : (2 : ℚ) ^ a * n' = 3 * n + 1 := by
    rw [hstep, affineStep]
    field_simp
  simp only [pow_add, pow_one]
  field_simp
  linear_combination (n' - c') * hrel

end RationalRepairs

section EntropyPacking
open scoped BigOperators

/-- Gibbs' finite inequality for positive masses whose sum is at most one. -/
theorem finite_log_mass_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → ℝ) (hP : ∀ i, 0 < P i) (hs : ∑ i, P i ≤ 1) :
    (Fintype.card ι : ℝ) * Real.log (Fintype.card ι) ≤ - ∑ i, Real.log (P i) := by
  let N : ℝ := Fintype.card ι
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  have hlog : ∀ i, Real.log (N * P i) = Real.log N + Real.log (P i) := by
    intro i
    exact Real.log_mul (ne_of_gt hN) (ne_of_gt (hP i))
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Real.log_le_sub_one_of_pos (mul_pos hN (hP i)))
  simp_rw [hlog] at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum] at h
  have hs' : N * (∑ i, P i) ≤ N := by nlinarith
  change N * Real.log N ≤ _
  simp only [mul_one] at h
  change N * Real.log N + (∑ i, Real.log (P i)) ≤ N * (∑ i, P i) - N at h
  linarith

/-- Bit values in the reals. -/
def bitReal (b : Bool) : ℝ := if b then 1 else 0

/-- Bernoulli product mass of a finite binary word. -/
def wordMass {r : ℕ} (q : ℝ) (w : Fin r → Bool) : ℝ :=
  ∏ j, if w j then q else 1 - q

theorem wordMass_pos {r : ℕ} {q : ℝ} (hq : 0 < q) (hq' : q < 1)
    (w : Fin r → Bool) : 0 < wordMass q w := by
  apply Finset.prod_pos
  intro j _
  split <;> linarith

theorem wordMass_total (r : ℕ) (q : ℝ) :
    (∑ w : Fin r → Bool, wordMass q w) = 1 := by
  unfold wordMass
  calc
    _ = ∏ _j : Fin r, ∑ b : Bool, (if b then q else 1 - q) :=
      (Fintype.prod_sum (fun (_j : Fin r) (b : Bool) => if b then q else 1 - q)).symm
    _ = 1 := by simp [Fintype.sum_bool]

theorem wordMass_log {r : ℕ} {q : ℝ} (hq : 0 < q) (hq' : q < 1)
    (w : Fin r → Bool) :
    Real.log (wordMass q w) =
      (∑ j, bitReal (w j)) * Real.log q +
      ((r : ℝ) - ∑ j, bitReal (w j)) * Real.log (1 - q) := by
  have hnonzero : ∀ j ∈ (Finset.univ : Finset (Fin r)),
      (if w j then q else 1 - q) ≠ 0 := by
    intro j _
    split <;> linarith
  rw [wordMass, Real.log_prod hnonzero]
  have hterm : ∀ j, Real.log (if w j then q else 1 - q) =
      bitReal (w j) * Real.log q + (1 - bitReal (w j)) * Real.log (1 - q) := by
    intro j
    cases h : w j <;> simp [h, bitReal]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  simp [Finset.sum_sub_distrib]

/-- The entropy packing inequality for distinct words with a lower bound
on the total number of one-bits. Logs and entropy here use natural units. -/
theorem entropy_packing {M r : ℕ} (hM : 0 < M)
    (w : Fin M → Fin r → Bool) (hw : Function.Injective w)
    {q : ℝ} (hq : 1 / 2 ≤ q) (hq' : q < 1)
    (hbias : (M : ℝ) * r * q ≤ ∑ i, ∑ j, bitReal (w i j)) :
    Real.log M ≤ (r : ℝ) * Real.binEntropy q := by
  classical
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < 1 - q := by linarith
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hsum : (∑ i, wordMass q (w i)) ≤ 1 := by
    calc
      _ = ∑ v ∈ Finset.univ.image w, wordMass q v := by
        rw [Finset.sum_image]
        exact fun a _ b _ h => hw h
      _ ≤ ∑ v : Fin r → Bool, wordMass q v := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro v _ _
        exact (wordMass_pos hq0 hq' v).le
      _ = 1 := wordMass_total r q
  have hg := finite_log_mass_bound (fun i => wordMass q (w i))
    (fun i => wordMass_pos hq0 hq' (w i)) hsum
  simp only [Fintype.card_fin] at hg
  simp_rw [wordMass_log hq0 hq'] at hg
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hg
  have hlogs : Real.log (1 - q) ≤ Real.log q :=
    Real.log_le_log hq1 (by linarith)
  have hgap := mul_nonneg (sub_nonneg.mpr hbias) (sub_nonneg.mpr hlogs)
  have hb : Real.binEntropy q = -q * Real.log q - (1 - q) * Real.log (1 - q) := by
    simp [Real.binEntropy, Real.log_inv]
    ring
  rw [hb]
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  nlinarith

/-- The degenerate all-one endpoint is handled combinatorially. -/
theorem entropy_packing_endpoint {M r : ℕ} (hM : 0 < M)
    (w : Fin M → Fin r → Bool) (hw : Function.Injective w)
    (hbias : (M : ℝ) * r ≤ ∑ i, ∑ j, bitReal (w i j)) :
    Real.log M ≤ (r : ℝ) * Real.binEntropy 1 := by
  classical
  have hbit0 (i : Fin M) (j : Fin r) : 0 ≤ 1 - bitReal (w i j) := by
    cases h : w i j <;> simp [bitReal, h]
  have hrow0 (i : Fin M) : 0 ≤ ∑ j, (1 - bitReal (w i j)) :=
    Finset.sum_nonneg (fun j _ => hbit0 i j)
  have hzero : (∑ i, ∑ j, (1 - bitReal (w i j))) = 0 := by
    have hnonneg := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hrow0 i)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at *
    linarith
  have hrow (i : Fin M) : (∑ j, (1 - bitReal (w i j))) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hrow0 i)).mp hzero i (Finset.mem_univ i)
  have hall (i : Fin M) (j : Fin r) : w i j = true := by
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hbit0 i j)).mp
      (hrow i) j (Finset.mem_univ j)
    cases h : w i j <;> simp_all [bitReal]
  have hM1 : M = 1 := by
    by_contra he
    have htwo : 1 < M := by omega
    let i : Fin M := ⟨0, hM⟩
    let j : Fin M := ⟨1, htwo⟩
    have heq : w i = w j := by
      funext k
      rw [hall i k, hall j k]
    have hval := congrArg Fin.val (hw heq)
    dsimp [i, j] at hval
    omega
  simp [hM1]

end EntropyPacking

section WindowBoundary
open scoped BigOperators

/-- A shifted chronological window loses at most its offset. -/
theorem shifted_window_lower (b : ℕ → ℝ) (hb0 : ∀ t, 0 ≤ b t)
    (hb1 : ∀ t, b t ≤ 1) (M j : ℕ) :
    (∑ t ∈ Finset.range M, b t) - j ≤
      ∑ t ∈ Finset.range M, b (t + j) := by
  have hleft := Finset.sum_range_add b j M
  have hright := Finset.sum_range_add b M j
  have hprefix : (∑ t ∈ Finset.range j, b t) ≤ (j : ℝ) := by
    calc
      _ ≤ ∑ _t ∈ Finset.range j, (1 : ℝ) := Finset.sum_le_sum (fun t _ => hb1 t)
      _ = j := by simp
  have hsuffix : 0 ≤ ∑ t ∈ Finset.range j, b (M + t) := by
    exact Finset.sum_nonneg (fun t _ => hb0 (M + t))
  have hshift : (∑ t ∈ Finset.range M, b (j + t)) =
      ∑ t ∈ Finset.range M, b (t + j) := by
    apply Finset.sum_congr rfl
    intro t _
    rw [Nat.add_comm]
  rw [hshift] at hleft
  rw [Nat.add_comm j M] at hleft
  linarith

/-- The exact triangular boundary correction, in real arithmetic. -/
theorem sum_range_cast (r : ℕ) :
    (∑ j ∈ Finset.range r, (j : ℝ)) = (r : ℝ) * (r - 1) / 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem all_windows_lower (b : ℕ → ℝ) (hb0 : ∀ t, 0 ≤ b t)
    (hb1 : ∀ t, b t ≤ 1) (M r : ℕ) :
    (r : ℝ) * (∑ t ∈ Finset.range M, b t) - (r : ℝ) * (r - 1) / 2 ≤
      ∑ j ∈ Finset.range r, ∑ t ∈ Finset.range M, b (t + j) := by
  have h := Finset.sum_le_sum (s := Finset.range r)
    (fun j _ => shifted_window_lower b hb0 hb1 M j)
  simpa [Finset.sum_sub_distrib, sum_range_cast] using h

end WindowBoundary

section OrbitEntropy
open scoped BigOperators

def orbitBit (n t : ℕ) : Bool := (shortcut^[t] n) % 2 == 1

theorem parity_bit_nat (n : ℕ) :
    (if n % 2 == 1 then (1 : ℕ) else 0) = n % 2 := by
  split <;> simp_all

theorem parityPrefix_ofFn (r n : ℕ) :
    parityPrefix r n = List.ofFn (fun j : Fin r =>
      if orbitBit n j then (1 : ℕ) else 0) := by
  induction r generalizing n with
  | zero => simp [parityPrefix]
  | succ r ih =>
    rw [parityPrefix, ih, List.ofFn_succ]
    congr 1
    · exact (parity_bit_nat n).symm

def chronologicalWord (n : ℕ) {M r : ℕ} (i : Fin M) (j : Fin r) : Bool :=
  orbitBit n (i.val + j.val)

theorem chronologicalWord_injective {M r : ℕ} (n : ℕ)
    (hinj : Function.Injective (fun i : Fin M => shortcut^[i.val] n))
    (hb : ∀ i : Fin M, shortcut^[i.val] n < 2 ^ r) :
    Function.Injective (chronologicalWord n : Fin M → Fin r → Bool) := by
  intro i k h
  apply hinj
  apply parityPrefix_injective_below r (hb i) (hb k)
  rw [parityPrefix_ofFn, parityPrefix_ofFn]
  congr 1
  funext j
  have he := congrFun h j
  have hbit (a b : ℕ) : orbitBit (shortcut^[a] n) b = orbitBit n (a + b) := by
    unfold orbitBit
    rw [Nat.add_comm a b, Function.iterate_add_apply]
  simp only [hbit]
  exact congrArg (fun b : Bool => if b then (1 : ℕ) else 0) he

/-- The chronological finite entropy bound, including `q = 1`.
The height hypothesis is the exact bounding fact used in the paper.
Natural-log units make the conclusion equivalent to the base-two statement. -/
theorem chronological_entropy {M r : ℕ} (hM : 0 < M) (n : ℕ)
    (hinj : Function.Injective (fun i : Fin M => shortcut^[i.val] n))
    (hb : ∀ i : Fin M, shortcut^[i.val] n < 2 ^ r)
    {q : ℝ} (hq : 1 / 2 ≤ q) (hq' : q ≤ 1)
    (hqdef : q = (∑ t ∈ Finset.range M, bitReal (orbitBit n t)) / M -
      ((r : ℝ) - 1) / (2 * M)) :
    Real.log M ≤ (r : ℝ) * Real.binEntropy q := by
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hn0 : ∀ t, 0 ≤ bitReal (orbitBit n t) := by
    intro t
    cases h : orbitBit n t <;> simp [h, bitReal]
  have hn1 : ∀ t, bitReal (orbitBit n t) ≤ 1 := by
    intro t
    cases h : orbitBit n t <;> simp [h, bitReal]
  have hpacking : ∀ (w : Fin M → Fin r → Bool), Function.Injective w →
      (M : ℝ) * r * q ≤ ∑ i, ∑ j, bitReal (w i j) →
      Real.log M ≤ (r : ℝ) * Real.binEntropy q := by
    intro w hw hbi
    rcases lt_or_eq_of_le hq' with hlt | heq
    · exact entropy_packing hM w hw hq hlt hbi
    · rw [heq] at hbi ⊢
      exact entropy_packing_endpoint hM w hw (by simpa using hbi)
  apply hpacking (chronologicalWord n)
    (chronologicalWord_injective n hinj hb)
  have hwin := all_windows_lower (fun t => bitReal (orbitBit n t)) hn0 hn1 M r
  have heq : (∑ i : Fin M, ∑ j : Fin r, bitReal (chronologicalWord n i j)) =
      ∑ j ∈ Finset.range r, ∑ i ∈ Finset.range M, bitReal (orbitBit n (i + j)) := by
    rw [Finset.sum_comm]
    simp only [chronologicalWord]
    simp_rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [dif_pos (Finset.mem_range.mp hj)]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [dif_pos (Finset.mem_range.mp hi)]
  rw [heq]
  have halg : (M : ℝ) * r * q =
      (r : ℝ) * (∑ t ∈ Finset.range M, bitReal (orbitBit n t)) -
      (r : ℝ) * (r - 1) / 2 := by
    rw [hqdef]
    field_simp <;> ring
  rw [halg]
  exact hwin

end OrbitEntropy

section ShallowPrefixes

/-- Exact multiplication for any finite sequence of shallow steps. -/
theorem shallow_prefix_identity (x : ℕ → ℕ) (h : ℕ)
    (hs : ∀ t < h, 2 * x (t + 1) = 3 * x t + 1) :
    2 ^ h * (x h + 1) = 3 ^ h * (x 0 + 1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hi := ih (fun t ht => hs t (by omega))
    have he := hs h (by omega)
    simp only [pow_succ]
    nlinarith [congrArg (fun z : ℕ => 2 ^ h * z) he]

/-- A shallow prefix forces divisibility of its initial value plus one. -/
theorem shallow_prefix_divisibility (x : ℕ → ℕ) (h : ℕ)
    (hs : ∀ t < h, 2 * x (t + 1) = 3 * x t + 1) :
    2 ^ h ∣ x 0 + 1 := by
  have hi := shallow_prefix_identity x h hs
  have hd : 2 ^ h ∣ 3 ^ h * (x 0 + 1) := by
    rw [← hi]
    exact dvd_mul_right _ _
  exact (((show Nat.Coprime 2 3 by decide).pow_left h).pow_right h).dvd_of_dvd_mul_left hd

/-- The exact coefficient-one height inequality in the zero-repair case. -/
theorem shallow_prefix_bound (x : ℕ → ℕ) (h : ℕ)
    (hs : ∀ t < h, 2 * x (t + 1) = 3 * x t + 1) :
    2 ^ h ≤ x 0 + 1 :=
  Nat.le_of_dvd (by omega) (shallow_prefix_divisibility x h hs)

end ShallowPrefixes

section ExactGrowth
open scoped BigOperators

/-- The real logarithmic identity for an odd shortcut step. -/
theorem odd_log_identity (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hstep : 2 * y = 3 * x + 1) :
    Real.log y - Real.log x = Real.log 3 - Real.log 2 +
      Real.log (1 + 1 / (3 * x)) := by
  have hc : 0 < 1 + 1 / (3 * x) := by positivity
  have hf : 3 * x * (1 + 1 / (3 * x)) = 3 * x + 1 := by
    field_simp
  have hl := congrArg Real.log hstep
  rw [Real.log_mul (by norm_num) (ne_of_gt hy), ← hf,
    Real.log_mul (ne_of_gt (mul_pos (by norm_num) hx)) (ne_of_gt hc),
    Real.log_mul (by norm_num) (ne_of_gt hx)] at hl
  linarith

theorem even_log_identity (x y : ℝ) (_hx : 0 < x) (hy : 0 < y)
    (hstep : 2 * y = x) :
    Real.log y - Real.log x = -Real.log 2 := by
  have hl := congrArg Real.log hstep
  rw [Real.log_mul (by norm_num) (ne_of_gt hy)] at hl
  linarith

theorem orbit_pos (n : ℕ) (hn : 0 < n) (t : ℕ) : 0 < shortcut^[t] n := by
  induction t with
  | zero => exact hn
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact shortcut_pos ih

noncomputable def correction (x : ℕ) : ℝ :=
  if x % 2 = 0 then 0 else Real.log (1 + 1 / (3 * (x : ℝ)))

/-- The exact one-step logarithmic growth identity for the actual map. -/
theorem shortcut_log_growth (n : ℕ) (hn : 0 < n) :
    Real.log (shortcut n) - Real.log n =
      bitReal (n % 2 == 1) * Real.log 3 - Real.log 2 + correction n := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnnext : 0 < (shortcut n : ℝ) := by exact_mod_cast shortcut_pos hn
  by_cases he : n % 2 = 0
  · have hh : n % 2 ≠ 1 := by omega
    have hs : (2 : ℝ) * (shortcut n : ℝ) = (n : ℝ) := by
      exact_mod_cast shortcut_even n he
    simpa [bitReal, he, correction] using
      even_log_identity (n : ℝ) (shortcut n : ℝ) hnreal hnnext hs
  · have ho : n % 2 = 1 := by omega
    simp only [bitReal, ho, beq_self_eq_true, ↓reduceIte, one_mul,
      correction, if_neg he]
    apply odd_log_identity (n : ℝ) (shortcut n : ℝ) hnreal hnnext
    exact_mod_cast shortcut_odd_numerator n ho

/-- The finite exact growth identity, in natural-log units. -/
theorem orbit_log_growth (n : ℕ) (hn : 0 < n) (M : ℕ) :
    Real.log (shortcut^[M] n) - Real.log n =
      (∑ t ∈ Finset.range M, bitReal (orbitBit n t)) * Real.log 3 -
      (M : ℝ) * Real.log 2 +
      ∑ t ∈ Finset.range M, correction (shortcut^[t] n) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have he := shortcut_log_growth (shortcut^[M] n) (orbit_pos n hn M)
    rw [Function.iterate_succ_apply']
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    unfold orbitBit at *
    linarith

/-- The positive correction is bounded by its reciprocal term. -/
theorem correction_bound (n : ℕ) (hn : 0 < n) :
    0 ≤ correction n ∧ correction n ≤ 1 / (3 * (n : ℝ)) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold correction
  split
  · constructor <;> positivity
  · have hc : 0 < 1 + 1 / (3 * (n : ℝ)) := by positivity
    constructor
    · exact Real.log_nonneg (by
        have : 0 ≤ 1 / (3 * (n : ℝ)) := by positivity
        linarith)
    · have h := Real.log_le_sub_one_of_pos hc
      linarith

end ExactGrowth

section PositiveFiniteEntropy
open scoped BigOperators

/-- Finite chronological entropy for a positive orbit. The only size input is
that the sampled actual states lie below `2^r`; in the paper `r` is chosen
from their maximum. No probabilistic assumption about the orbit is made. -/
theorem positive_chronological_entropy {M r : ℕ} (hM : 0 < M) (n : ℕ)
    (hn : 0 < n)
    (hinj : Function.Injective (fun i : Fin M => shortcut^[i.val] n))
    (hb : ∀ i : Fin M, shortcut^[i.val] n < 2 ^ r)
    {q : ℝ} (hq : 1 / 2 ≤ q)
    (hqdef : q = (∑ t ∈ Finset.range M, bitReal (orbitBit n t)) / M -
      ((r : ℝ) - 1) / (2 * M)) :
    Real.log M ≤ (r : ℝ) * Real.binEntropy q := by
  have hr : 0 < r := by
    by_contra he
    have hr0 : r = 0 := by omega
    have hh := hb ⟨0, hM⟩
    simp only [hr0, pow_zero, Function.iterate_zero, id_eq] at hh
    omega
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hrs : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hs : (∑ t ∈ Finset.range M, bitReal (orbitBit n t)) ≤ (M : ℝ) := by
    calc
      _ ≤ ∑ _t ∈ Finset.range M, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t _
        cases h : orbitBit n t <;> simp [bitReal, h]
      _ = M := by simp
  have hdiv : (∑ t ∈ Finset.range M, bitReal (orbitBit n t)) / M ≤ 1 := by
    apply (div_le_iff₀ hMreal).mpr
    simpa using hs
  have hq1 : q ≤ 1 := by
    rw [hqdef]
    have hc : 0 ≤ ((r : ℝ) - 1) / (2 * M) := div_nonneg (by linarith) (by positivity)
    linarith
  exact chronological_entropy hM n hinj hb hq hq1 hqdef

end PositiveFiniteEntropy

end CollatzPrefix
