import FormalComponents
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Order.Filter.Cofinite

/-!
# Vanishing mean logarithmic correction for an injective orbit

An injective sequence of natural numbers escapes every finite set. Consequently,
the reciprocal upper bound on each positive shortcut correction tends to zero.
Cesàro convergence then gives the vanishing mean correction needed in the
asymptotic entropy argument. No rate of escape is assumed.
-/

namespace CollatzPrefix

open Filter
open scoped BigOperators Topology

/-- The actual states of an injective shortcut orbit tend to infinity. -/
theorem injective_orbit_tendsto_atTop (n : ℕ)
    (hinj : Function.Injective (fun t : ℕ => shortcut^[t] n)) :
    Tendsto (fun t : ℕ => shortcut^[t] n) atTop atTop :=
  hinj.nat_tendsto_atTop

/-- Every individual logarithmic correction vanishes along a positive
injective shortcut orbit. -/
theorem orbit_correction_tendsto_zero (n : ℕ) (hn : 0 < n)
    (hinj : Function.Injective (fun t : ℕ => shortcut^[t] n)) :
    Tendsto (fun t : ℕ => correction (shortcut^[t] n)) atTop (𝓝 0) := by
  have hstates : Tendsto (fun t : ℕ => (shortcut^[t] n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (injective_orbit_tendsto_atTop n hinj)
  have hreciprocal : Tendsto (fun t : ℕ => 1 / (3 * (shortcut^[t] n : ℝ)))
      atTop (𝓝 0) :=
    (hstates.const_mul_atTop (by norm_num : (0 : ℝ) < 3)).const_div_atTop 1
  exact squeeze_zero
    (fun t => (correction_bound _ (orbit_pos n hn t)).1)
    (fun t => (correction_bound _ (orbit_pos n hn t)).2)
    hreciprocal

/-- The mean correction along a positive injective shortcut orbit tends to
zero. This is sufficient for the entropy-height limit, without a quantitative
harmonic-sum estimate. -/
theorem orbit_correction_mean_tendsto_zero (n : ℕ) (hn : 0 < n)
    (hinj : Function.Injective (fun t : ℕ => shortcut^[t] n)) :
    Tendsto
      (fun M : ℕ => (∑ t ∈ Finset.range M, correction (shortcut^[t] n)) / (M : ℝ))
      atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv, mul_comm] using
    (orbit_correction_tendsto_zero n hn hinj).cesaro

end CollatzPrefix
