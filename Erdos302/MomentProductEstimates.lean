import Erdos302.PositiveMoment
import Erdos302.ReciprocalPrimeSums

namespace Erdos302

theorem moment_factor_log_bound {z p : ℝ} (hz1 : 1 ≤ z) (hz2 : z < 2) (hp2 : 2 ≤ p) :
    Real.log (1 + (z - 1) / (p - z)) ≤
      (z - 1) * p⁻¹ + ((z - 1) * z / (1 - z / 2)) * p⁻¹ ^ 2 := by
  have hz0 : 0 ≤ z := by linarith
  have hp0 : 0 < p := by linarith
  have hpz : 0 < p - z := by linarith
  have hd : 0 < 1 - z / 2 := by linarith
  have hnum : 0 ≤ (z - 1) * z := mul_nonneg (by linarith) hz0
  have hf : 0 < 1 + (z - 1) / (p - z) := by positivity
  have hden : (1 - z / 2) * p ^ 2 ≤ p * (p - z) := by
    have h := mul_nonneg (sub_nonneg.mpr hp2) (mul_nonneg hz0 hp0.le)
    nlinarith
  have herr : (z - 1) * z / (p * (p - z)) ≤
      (z - 1) * z / ((1 - z / 2) * p ^ 2) :=
    div_le_div_of_nonneg_left hnum (mul_pos hd (sq_pos_of_pos hp0)) hden
  calc
    Real.log (1 + (z - 1) / (p - z)) ≤ (z - 1) / (p - z) := by
      have h := Real.log_le_sub_one_of_pos hf
      linarith
    _ = (z - 1) * p⁻¹ + (z - 1) * z / (p * (p - z)) := by field_simp <;> ring
    _ ≤ (z - 1) * p⁻¹ + (z - 1) * z / ((1 - z / 2) * p ^ 2) := add_le_add le_rfl herr
    _ = (z - 1) * p⁻¹ + ((z - 1) * z / (1 - z / 2)) * p⁻¹ ^ 2 := by
      field_simp <;> ring

theorem log_momentProduct_bound (z : ℝ) (hz1 : 1 ≤ z) (hz2 : z < 2)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Real.log (momentProduct P z) ≤
      (z - 1) * (∑ p ∈ P, (p : ℝ)⁻¹) + (z - 1) * z / (1 - z / 2) := by
  let C : ℝ := (z - 1) * z / (1 - z / 2)
  have hC : 0 ≤ C := div_nonneg (mul_nonneg (sub_nonneg.mpr hz1) (by linarith)) (by linarith)
  have hf : ∀ p ∈ P, 1 + (z - 1) / ((p : ℝ) - z) ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hpz : 0 < (p : ℝ) - z := by linarith
    have hpos : 0 < 1 + (z - 1) / ((p : ℝ) - z) := by positivity
    exact hpos.ne'
  unfold momentProduct
  rw [Real.log_prod hf]
  calc
    (∑ p ∈ P, Real.log (1 + (z - 1) / ((p : ℝ) - z))) ≤
        ∑ p ∈ P, ((z - 1) * (p : ℝ)⁻¹ + C * (p : ℝ)⁻¹ ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      exact moment_factor_log_bound hz1 hz2 (by exact_mod_cast (hP p hp).two_le)
    _ = (z - 1) * (∑ p ∈ P, (p : ℝ)⁻¹) + C * (∑ p ∈ P, (p : ℝ)⁻¹ ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (z - 1) * (∑ p ∈ P, (p : ℝ)⁻¹) + C := by
      have h := mul_le_mul_of_nonneg_left (prime_reciprocal_square_sum_le_one P hP) hC
      simpa only [mul_one] using add_le_add (le_refl ((z - 1) * (∑ p ∈ P, (p : ℝ)⁻¹))) h

theorem primeMoment_exponential_bound (z : ℝ) (hz1 : 1 ≤ z) (hz2 : z < 2)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    primeMoment P z N ≤ (N : ℝ) * Real.exp
      ((z - 1) * (∑ p ∈ P, (p : ℝ)⁻¹) + (z - 1) * z / (1 - z / 2)) := by
  have hprod : momentProduct P z ≤ Real.exp
      ((z - 1) * (∑ p ∈ P, (p : ℝ)⁻¹) + (z - 1) * z / (1 - z / 2)) :=
    Real.le_exp_of_log_le (log_momentProduct_bound z hz1 hz2 P hP)
  exact (primeMoment_product_bound z hz1 hz2 P hP N).trans
    (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg N))

end Erdos302
