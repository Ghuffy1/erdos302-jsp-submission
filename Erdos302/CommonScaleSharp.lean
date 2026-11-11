import Erdos302.CommonScaleMean

namespace Erdos302

theorem common_scale_mean_sharp {t Y : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hY : 1 ≤ Y)
    (X : ℕ) (hX : 2 ≤ X) :
    (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, t ^ smallOmega n X) ≤
      4 * (10 : ℝ) ^ 9 * Y *
        ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * Y)) ^ (t - 1)) := by
  let M := ⌈Y⌉₊
  have hYM : Y ≤ (M : ℝ) := Nat.le_ceil Y
  have hMY : (M : ℝ) ≤ 2 * Y := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ Y by linarith)
    dsimp [M]
    linarith
  have hYlog : 0 < Real.log (2 * Y) := Real.log_pos (by linarith)
  have hXlog : 0 < Real.log (2 * (X : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * X by omega))
  have hXp : 0 ≤ (Real.log (2 * (X : ℝ))) ^ (t - 1) := Real.rpow_nonneg hXlog.le _
  have hYp : 0 ≤ (Real.log (2 * Y)) ^ (t - 1) := Real.rpow_nonneg hYlog.le _
  have hp : (Real.log (2 * (M : ℝ))) ^ (t - 1) ≤ (Real.log (2 * Y)) ^ (t - 1) := by
    apply Real.rpow_le_rpow_of_nonpos hYlog
    · exact Real.log_le_log (by linarith) (by linarith)
    · linarith
  calc
    (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, t ^ smallOmega n X) ≤
        ∑ n ∈ Finset.Icc 1 M, t ^ smallOmega n X := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (Nat.floor_le_ceil Y))
      intro n hn hnot
      exact pow_nonneg ht0 _
    _ ≤ 2 * (10 : ℝ) ^ 9 * M *
        ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * (M : ℝ))) ^ (t - 1)) :=
      common_scale_mean_nat ht0 ht1 X M hX
    _ ≤ 4 * (10 : ℝ) ^ 9 * Y *
        ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * Y)) ^ (t - 1)) := by
      calc
        _ ≤ 2 * (10 : ℝ) ^ 9 * M *
            ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * Y)) ^ (t - 1)) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hp) (by positivity)
        _ ≤ 4 * (10 : ℝ) ^ 9 * Y *
            ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * Y)) ^ (t - 1)) := by
          have h := mul_le_mul_of_nonneg_right hMY (add_nonneg hXp hYp)
          nlinarith

end Erdos302
