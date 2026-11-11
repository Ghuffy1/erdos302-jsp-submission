import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Exact rational and logarithmic parameters for the strengthened removal
estimate. The analytic estimates using them are proved in the later modules. -/

namespace Erdos302.Parameters

noncomputable def A : ℝ := 53 / 50
noncomputable def z : ℝ := 561 / 500
noncomputable def q : ℝ := 20 / 13
noncomputable def theta : ℝ := 169 / 400
noncomputable def gamma : ℝ := 2197 / 8000
noncomputable def beta : ℝ := 693 / 400
noncomputable def kappa : ℝ := 7 / 80
noncomputable def delta : ℝ := 1 / 140
noncomputable def M : ℝ := 3 * A * Real.log q
noncomputable def H : ℝ := M - beta

theorem theta_eq : theta = (q ^ 2)⁻¹ := by norm_num [theta, q]
theorem gamma_eq : gamma = (q ^ 3)⁻¹ := by norm_num [gamma, q]
theorem beta_eq : beta = 3 * (1 - theta) := by norm_num [beta, theta]

theorem q_pow_four_lt_z_pow_fifteen : q ^ 4 < z ^ 15 := by norm_num [q, z]

theorem log_z_lower :
    2 * ((61 / 1061 : ℝ) + (61 / 1061 : ℝ) ^ 3 / 3) ≤ Real.log z := by
  have h := Real.sum_range_le_log_div (x := (61 / 1061 : ℝ))
    (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ, z] at h ⊢
  linarith

theorem chernoff_gap : 1 / 52000 < A * Real.log z - z + 1 := by
  have h := log_z_lower
  norm_num [A, z] at *
  linarith

theorem log_q_lower : 14 / 33 ≤ Real.log q := by
  have h := Real.sum_range_le_log_div (x := (7 / 33 : ℝ))
    (by norm_num) (by norm_num) 1
  norm_num [Finset.sum_range_succ, q] at h ⊢
  linarith

theorem log_q_upper : Real.log q < 431 / 1000 := by
  have h := Real.log_div_le_sum_range_add (x := (7 / 33 : ℝ))
    (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ, q] at h ⊢
  linarith

theorem log_q_upper_sharp : Real.log q < 4308 / 10000 := by
  have h := Real.log_div_le_sum_range_add (x := (7 / 33 : ℝ))
    (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ, q] at h ⊢
  linarith

theorem summation_exponents :
    -(1 / 2 : ℝ) < H ∧ H < 0 ∧ H + gamma < -kappa := by
  have hL := log_q_lower
  have hU := log_q_upper_sharp
  dsimp [H, M, A, beta, gamma, kappa] at *
  constructor
  · linarith
  constructor <;> linarith

theorem log_q_vs_log_z : 4 * Real.log q < 15 * Real.log z := by
  have hq : 0 < q := by norm_num [q]
  have hz : 0 < z := by norm_num [z]
  have h := Real.log_lt_log (pow_pos hq 4) q_pow_four_lt_z_pow_fifteen
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem rate_identity : kappa - (9 / 112 : ℝ) = delta := by
  norm_num [kappa, delta]

theorem irregular_coefficient : (500000 : ℝ) * z = 561000 := by
  norm_num [z]

theorem square_sieve_coefficient :
    (32 : ℝ) * 27 * 768 ^ 2 + 144 = 509608080 ∧
    (509608080 : ℝ) < 10 ^ 9 := by norm_num

theorem block_coefficient :
    (9 : ℝ) * 10 ^ 10 * (4 * 10 ^ 9) = 36 * 10 ^ 19 := by norm_num

theorem tail_coefficients :
    (36 : ℝ) * 10 ^ 19 * 46 < 10 ^ 23 ∧
    (36 : ℝ) * 10 ^ 19 * 38 < 10 ^ 23 := by norm_num

end Erdos302.Parameters
