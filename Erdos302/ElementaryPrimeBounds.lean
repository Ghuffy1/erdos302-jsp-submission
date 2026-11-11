import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

namespace Erdos302

theorem log_le_sqrt_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ Real.sqrt x := by
  have hxpos : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have he := Real.add_one_le_exp (Real.log x / 4)
  have hs := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log x / 4 + 1) he 2
  have hexp : (Real.exp (Real.log x / 4)) ^ 2 = Real.sqrt x := by
    calc
      (Real.exp (Real.log x / 4)) ^ 2 = Real.exp (Real.log x / 2) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      _ = Real.sqrt (Real.exp (Real.log x)) := Real.exp_half _
      _ = Real.sqrt x := by rw [Real.exp_log hxpos]
  rw [hexp] at hs
  nlinarith [sq_nonneg (Real.log x - 4)]

theorem psi_le_four_mul {x : ℝ} (hx : 0 ≤ x) : Chebyshev.psi x ≤ 4 * x := by
  by_cases hx1 : 1 ≤ x
  · have hpsi := Chebyshev.psi_le hx1
    have hl := log_le_sqrt_of_one_le hx1
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hlog4 : Real.log 4 ≤ 2 := by
      calc
        Real.log 4 = Real.log ((2 : ℝ) ^ 2) := by norm_num
        _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
        _ ≤ 2 := by linarith
    have hm := mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg x)
    have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
    have h4 := mul_le_mul_of_nonneg_right hlog4 hx
    nlinarith
  · rw [Chebyshev.psi_eq_zero_of_lt_two (by linarith)]
    positivity

end Erdos302
