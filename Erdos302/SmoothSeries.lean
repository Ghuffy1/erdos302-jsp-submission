import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-! Exact convergence of the reciprocal series on any fixed finite set of
allowed prime factors. This is the summability input for the proposed smooth
prefix formula, independently of its connection to the extremal function. -/

namespace Erdos302

open scoped BigOperators

noncomputable def reciprocalHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp [mul_comm]

theorem reciprocalHom_prime_norm_lt_one {p : ℕ} (hp : p.Prime) :
    ‖reciprocalHom p‖ < 1 := by
  change ‖(p : ℝ)⁻¹‖ < 1
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
  exact inv_lt_one_of_one_lt₀ hp'

theorem smooth_reciprocal_hasSum (P : Finset ℕ) :
    HasSum (fun n : Nat.factoredNumbers P => ((n : ℕ) : ℝ)⁻¹)
      (∏ p ∈ P with p.Prime, (1 - (p : ℝ)⁻¹)⁻¹) := by
  exact (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalHom) (fun hp => reciprocalHom_prime_norm_lt_one hp) P).2

theorem smooth_reciprocal_summable (P : Finset ℕ) :
    Summable (fun n : Nat.factoredNumbers P => ((n : ℕ) : ℝ)⁻¹) :=
  (smooth_reciprocal_hasSum P).summable

theorem smooth_weighted_summable (P : Finset ℕ)
    (w : Nat.factoredNumbers P → ℝ)
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) :
    Summable (fun n => w n / (n : ℕ)) := by
  apply Summable.of_nonneg_of_le (fun n => div_nonneg (hw0 n) (Nat.cast_nonneg _))
    (fun n => ?_) (smooth_reciprocal_summable P)
  simpa only [one_div] using div_le_div_of_nonneg_right (hw1 n) (Nat.cast_nonneg (n : ℕ))

theorem smooth_weighted_sum_le (P : Finset ℕ)
    (w : Nat.factoredNumbers P → ℝ)
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) :
    (∑' n, w n / (n : ℕ)) ≤ ∏ p ∈ P with p.Prime, (1 - (p : ℝ)⁻¹)⁻¹ := by
  rw [← (smooth_reciprocal_hasSum P).tsum_eq]
  apply (smooth_weighted_summable P w hw0 hw1).tsum_le_tsum (fun n => ?_)
    (smooth_reciprocal_summable P)
  simpa only [one_div] using div_le_div_of_nonneg_right (hw1 n) (Nat.cast_nonneg (n : ℕ))

end Erdos302
