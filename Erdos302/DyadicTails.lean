import Erdos302.PowerSums
import Erdos302.RegularityMoment

namespace Erdos302

theorem negative_rpow_scale {x y c e : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hc : 1 ≤ c) (hyx : y ≤ c * x) (he : -1 ≤ e) (he0 : e ≤ 0) :
    x ^ e ≤ c * y ^ e := by
  have hc0 : 0 < c := by linarith
  have h := Real.rpow_le_rpow_of_nonpos hy hyx he0
  rw [Real.mul_rpow hc0.le hx.le] at h
  have hcPow : c⁻¹ ≤ c ^ e := by
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hc he
  have hm := mul_le_mul_of_nonneg_right hcPow (Real.rpow_nonneg hx.le e)
  have hh : c⁻¹ * x ^ e ≤ y ^ e := hm.trans h
  have hh' := mul_le_mul_of_nonneg_left hh hc0.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul] using hh'

theorem negative_rpow_double_four {x y e : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hyx : y ≤ 2 * x) (he : -2 ≤ e) (he0 : e ≤ 0) :
    x ^ e ≤ 4 * y ^ e := by
  have h := Real.rpow_le_rpow_of_nonpos hy hyx he0
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.le] at h
  have hcPow : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ e := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
    norm_num at h
    exact h
  have hm := mul_le_mul_of_nonneg_right hcPow (Real.rpow_nonneg hx.le e)
  linarith [hm.trans h]

theorem dyadic_first_tail (S : Finset ℕ) {U h : ℝ}
    (hU : 1 ≤ U) (hh : (1 / 2 : ℝ) ≤ h) (hh1 : h ≤ 1)
    (hS : ∀ j ∈ S, 1 ≤ j ∧ U < ((j : ℝ) + 1) * h) :
    (∑ j ∈ S, (((j : ℝ) + 1) * h) ^ (Parameters.H + Parameters.gamma - 1)) ≤
      128 * U ^ (-Parameters.kappa) := by
  have hk : 0 < Parameters.kappa := by norm_num [Parameters.kappa]
  have hk1 : Parameters.kappa ≤ 1 := by norm_num [Parameters.kappa]
  have hU0 : 0 < U := by linarith
  let J := ⌊U⌋₊
  let B := S.sup id + 1
  have hJ1 : 1 ≤ J := Nat.le_floor (by simpa only [Nat.cast_one] using hU)
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hJU : (J : ℝ) ≤ U := Nat.floor_le hU0.le
  have hUJ : U ≤ 2 * (J : ℝ) := by
    have hn := Nat.lt_floor_add_one U
    have hj : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
    dsimp [J] at *
    linarith
  have hsub : S ⊆ Finset.Ico J B := by
    intro j hj
    obtain ⟨hj1, hUj⟩ := hS j hj
    have hjR : 0 ≤ (j : ℝ) + 1 := by positivity
    have hsmall : U < (j : ℝ) + 1 := hUj.trans_le (by nlinarith)
    have hJj : J ≤ j := by
      by_contra hnot
      have hjJ : j + 1 ≤ J := by omega
      have hjJR : (j : ℝ) + 1 ≤ J := by exact_mod_cast hjJ
      linarith
    exact Finset.mem_Ico.mpr ⟨hJj, Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)⟩
  have hterm (j : ℕ) (hj : j ∈ S) :
      (((j : ℝ) + 1) * h) ^ (Parameters.H + Parameters.gamma - 1) ≤
        4 * (((j + 1 : ℕ) : ℝ) ^ (-1 - Parameters.kappa)) := by
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (hS j hj).1
    have hR : 1 ≤ ((j : ℝ) + 1) * h := by nlinarith
    have he := Parameters.summation_exponents.2.2
    have hs := Real.rpow_le_rpow_of_exponent_le hR (show
      Parameters.H + Parameters.gamma - 1 ≤ -1 - Parameters.kappa by linarith)
    have hd := negative_rpow_double_four (by linarith : 0 < ((j : ℝ) + 1) * h)
      (by positivity : (0 : ℝ) < (j + 1 : ℕ))
      (show (((j + 1 : ℕ) : ℝ)) ≤ 2 * (((j : ℝ) + 1) * h) by push_cast; nlinarith)
      (show (-2 : ℝ) ≤ -1 - Parameters.kappa by linarith)
      (show -1 - Parameters.kappa ≤ 0 by linarith)
    exact hs.trans hd
  have hsum := sum_shifted_rpow_tail_le J B (by omega) hk
  have hscale := negative_rpow_scale hJ0 hU0 (by norm_num : (1 : ℝ) ≤ 2) hUJ
    (show (-1 : ℝ) ≤ -Parameters.kappa by linarith) (by linarith : -Parameters.kappa ≤ 0)
  calc
    (∑ j ∈ S, (((j : ℝ) + 1) * h) ^ (Parameters.H + Parameters.gamma - 1)) ≤
        ∑ j ∈ S, 4 * (((j + 1 : ℕ) : ℝ) ^ (-1 - Parameters.kappa)) := Finset.sum_le_sum hterm
    _ = 4 * ∑ j ∈ S, (((j + 1 : ℕ) : ℝ) ^ (-1 - Parameters.kappa)) := by rw [Finset.mul_sum]
    _ ≤ 4 * ∑ j ∈ Finset.Ico J B, (((j + 1 : ℕ) : ℝ) ^ (-1 - Parameters.kappa)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj hn => by positivity)
    _ ≤ 4 * ((J : ℝ) ^ (-Parameters.kappa) / Parameters.kappa) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ 128 * U ^ (-Parameters.kappa) := by
      have hp : 0 ≤ U ^ (-Parameters.kappa) := Real.rpow_nonneg hU0.le _
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hk).mpr
      have hc : (8 : ℝ) ≤ 128 * Parameters.kappa := by norm_num [Parameters.kappa]
      have hm := mul_le_mul_of_nonneg_right hc hp
      nlinarith

end Erdos302
