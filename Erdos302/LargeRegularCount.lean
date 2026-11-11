import Erdos302.DyadicCover
import Erdos302.DyadicSecondTail
import Erdos302.EffectiveRate

namespace Erdos302

theorem largeRegularParameters_card_bound (N V K : ℕ) (hN : 4 ≤ N) (hV : 4 ≤ V) :
    ((largeRegularParameters N V K).card : ℝ) ≤
      (N : ℝ) * (10 ^ 23 * Parameters.q ^ (3 * K) *
        (Real.rpow (Real.log V) (-(7 / 80 : ℝ)) + Real.rpow (Real.log N) (-(7 / 80 : ℝ)))) := by
  let S := dyadicParameterIndices N V
  let h := Real.log 2
  let U := Real.log N
  let W := Real.log V
  have hh : (1 / 2 : ℝ) ≤ h := by dsimp [h]; linarith [log_two_lower]
  have hh1 : h ≤ 1 := by
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    dsimp [h]
    linarith
  have hU : 1 ≤ U := (one_lt_log_of_four_le hN).le
  have hW : 1 ≤ W := (one_lt_log_of_four_le hV).le
  have hN0 : 0 < N := by omega
  have hV0 : (0 : ℝ) < V := by exact_mod_cast (show 0 < V by omega)
  have hSfirst : ∀ j ∈ S, 1 ≤ j ∧ W < ((j : ℝ) + 1) * h := by
    intro j hj
    obtain ⟨hjN, hj1, hVj, hj2⟩ := mem_dyadicParameterIndices.mp hj
    refine ⟨hj1, ?_⟩
    have hp : (V : ℝ) < 2 * ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hVj
    have hl := Real.log_lt_log hV0 hp
    rwa [log_dyadic_double] at hl
  have hSsecond : ∀ j ∈ S, 1 ≤ j ∧ 2 * (j : ℝ) * h ≤ U := by
    intro j hj
    obtain ⟨hjN, hj1, hVj, hj2⟩ := mem_dyadicParameterIndices.mp hj
    refine ⟨hj1, ?_⟩
    have hp : (((2 ^ j : ℕ) : ℝ)) ^ 2 ≤ N := by exact_mod_cast hj2
    have hl := Real.log_le_log (by positivity) hp
    rw [Real.log_pow] at hl
    push_cast at hl
    rw [Real.log_pow] at hl
    simpa only [h, U, mul_assoc] using hl
  have hfirst := dyadic_first_tail S hW hh hh1 hSfirst
  have hsecond := dyadic_second_tail S hU hh hSsecond
  let C : ℝ := 72 * 10 ^ 19 * Parameters.q ^ (3 * K) * N
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num [Parameters.q]) _))
      (Nat.cast_nonneg N)
  have hblocks : (∑ j ∈ S, ((regularParameterBox N K (2 ^ j)).card : ℝ)) ≤
      C * ((∑ j ∈ S, (((j : ℝ) + 1) * h) ^ (Parameters.H + Parameters.gamma - 1)) +
        ∑ j ∈ S, (((j : ℝ) + 1) * h) ^ Parameters.H *
          (U + (1 - 2 * (j : ℝ)) * h) ^ (Parameters.gamma - 1)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hjN, hj1, hVj, hj2⟩ := mem_dyadicParameterIndices.mp hj
    have hX : 2 ≤ 2 ^ j := by
      have h := Nat.pow_le_pow_right (by norm_num : 0 < 2) hj1
      simpa using h
    have hb := regularParameterBox_card_bound N K (2 ^ j) hX hj2
    rw [log_dyadic_double, log_dyadic_terminal hN0] at hb
    exact hb
  have hpW : 0 ≤ W ^ (-Parameters.kappa) := Real.rpow_nonneg (by linarith) _
  have hpU : 0 ≤ U ^ (-Parameters.kappa) := Real.rpow_nonneg (by linarith) _
  have hcoeff : (72 * 10 ^ 19 : ℝ) * (128 * W ^ (-Parameters.kappa) + 64 * U ^ (-Parameters.kappa)) ≤
      10 ^ 23 * (W ^ (-Parameters.kappa) + U ^ (-Parameters.kappa)) := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left hcoeff
    (show 0 ≤ Parameters.q ^ (3 * K) * (N : ℝ) by
      exact mul_nonneg (pow_nonneg (by norm_num [Parameters.q]) _) (Nat.cast_nonneg N))
  calc
    ((largeRegularParameters N V K).card : ℝ) ≤
        ∑ j ∈ S, ((regularParameterBox N K (2 ^ j)).card : ℝ) :=
      largeRegularParameters_card_le_blocks N V K hV
    _ ≤ C * ((∑ j ∈ S, (((j : ℝ) + 1) * h) ^ (Parameters.H + Parameters.gamma - 1)) +
        ∑ j ∈ S, (((j : ℝ) + 1) * h) ^ Parameters.H *
          (U + (1 - 2 * (j : ℝ)) * h) ^ (Parameters.gamma - 1)) := hblocks
    _ ≤ C * (128 * W ^ (-Parameters.kappa) + 64 * U ^ (-Parameters.kappa)) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hC
    _ ≤ (N : ℝ) * (10 ^ 23 * Parameters.q ^ (3 * K) *
        (Real.rpow (Real.log V) (-(7 / 80 : ℝ)) + Real.rpow (Real.log N) (-(7 / 80 : ℝ)))) := by
      dsimp [C, U, W, Parameters.kappa] at *
      nlinarith

end Erdos302
