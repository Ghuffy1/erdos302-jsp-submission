import Erdos302.PrimeReciprocalBounds
import Erdos302.MomentProductEstimates

namespace Erdos302

theorem log_two_lower_two_thirds : (2 / 3 : ℝ) ≤ Real.log 2 := by
  have h := Real.sum_range_le_log_div (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem regularity_moment_product_bound (X : ℕ) (hX : 2 ≤ X) :
    momentProduct (Nat.primesLE X) Parameters.z ≤
      8 * (Real.log X / Real.log 2) ^ (Parameters.z - 1) := by
  have hz1 : 1 ≤ Parameters.z := by norm_num [Parameters.z]
  have hz2 : Parameters.z < 2 := by norm_num [Parameters.z]
  have hza : 0 ≤ Parameters.z - 1 := by norm_num [Parameters.z]
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have htwo : 0 < Real.log 2 := by linarith [log_two_lower]
  have hratio : 0 < Real.log X / Real.log 2 := div_pos hL htwo
  have hlogtwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hloglogtwo : Real.log (Real.log 2) ≤ 0 := by
    have h := Real.log_le_sub_one_of_pos htwo
    linarith
  have hlog8 : (2 : ℝ) ≤ Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    linarith [log_two_lower_two_thirds]
  have hconst : 11 * (Parameters.z - 1) +
      (Parameters.z - 1) * Parameters.z / (1 - Parameters.z / 2) ≤ 2 := by
    norm_num [Parameters.z]
  have hlogbound : Real.log (momentProduct (Nat.primesLE X) Parameters.z) ≤
      Real.log 8 + Real.log (Real.log X / Real.log 2) * (Parameters.z - 1) := by
    calc
      Real.log (momentProduct (Nat.primesLE X) Parameters.z) ≤
          (Parameters.z - 1) * (∑ p ∈ Nat.primesLE X, (p : ℝ)⁻¹) +
            (Parameters.z - 1) * Parameters.z / (1 - Parameters.z / 2) :=
        log_momentProduct_bound _ hz1 hz2 _ (fun p hp => Nat.prime_of_mem_primesLE hp)
      _ ≤ (Parameters.z - 1) * (Real.log (Real.log X) + 11) +
            (Parameters.z - 1) * Parameters.z / (1 - Parameters.z / 2) := by
        exact add_le_add (mul_le_mul_of_nonneg_left (prime_reciprocal_sum_upper X hX) hza) le_rfl
      _ ≤ Real.log 8 + Real.log (Real.log X / Real.log 2) * (Parameters.z - 1) := by
        rw [Real.log_div hL.ne' htwo.ne']
        have hn := mul_nonpos_of_nonneg_of_nonpos hza hloglogtwo
        nlinarith
  calc
    momentProduct (Nat.primesLE X) Parameters.z ≤
        Real.exp (Real.log 8 + Real.log (Real.log X / Real.log 2) * (Parameters.z - 1)) :=
      Real.le_exp_of_log_le hlogbound
    _ = 8 * (Real.log X / Real.log 2) ^ (Parameters.z - 1) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8), Real.rpow_def_of_pos hratio]

theorem regularity_moment_bound (N X : ℕ) (hX : 2 ≤ X) :
    (∑ n ∈ Finset.Icc 1 N, Parameters.z ^ smallOmega n X) ≤
      8 * N * (Real.log X / Real.log 2) ^ (Parameters.z - 1) := by
  have h := smallOmega_moment_product_bound Parameters.z
    (by norm_num [Parameters.z]) (by norm_num [Parameters.z]) N X
  rw [← Nat.primesLE_eq_filter_range] at h
  calc
    (∑ n ∈ Finset.Icc 1 N, Parameters.z ^ smallOmega n X) ≤
        (N : ℝ) * momentProduct (Nat.primesLE X) Parameters.z := h
    _ ≤ (N : ℝ) * (8 * (Real.log X / Real.log 2) ^ (Parameters.z - 1)) :=
      mul_le_mul_of_nonneg_left (regularity_moment_product_bound X hX) (Nat.cast_nonneg N)
    _ = 8 * N * (Real.log X / Real.log 2) ^ (Parameters.z - 1) := by ring

theorem regularity_tail_moment_bound (N X : ℕ) (hX : 2 ≤ X) (T : ℝ) :
    ((((Finset.Icc 1 N).filter (fun n => T < (smallOmega n X : ℝ))).card : ℕ) : ℝ) *
      Parameters.z ^ T ≤ 8 * N * (Real.log X / Real.log 2) ^ (Parameters.z - 1) := by
  have h := smallOmega_tail_product_bound Parameters.z
    (by norm_num [Parameters.z]) (by norm_num [Parameters.z]) N X T
  rw [← Nat.primesLE_eq_filter_range] at h
  exact h.trans (by
    calc
      (N : ℝ) * momentProduct (Nat.primesLE X) Parameters.z ≤
          (N : ℝ) * (8 * (Real.log X / Real.log 2) ^ (Parameters.z - 1)) :=
        mul_le_mul_of_nonneg_left (regularity_moment_product_bound X hX) (Nat.cast_nonneg N)
      _ = 8 * N * (Real.log X / Real.log 2) ^ (Parameters.z - 1) := by ring)

end Erdos302
