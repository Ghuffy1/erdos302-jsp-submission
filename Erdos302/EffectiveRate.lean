import Erdos302.DensityFromRemoval

namespace Erdos302

open Filter
open scoped Topology

theorem limiting_removal_bound (hrem : RemovalEstimateStatement) (V K : ℕ) (hV : 4 ≤ V) :
    U V - claimedConstant ≤ 500000 * Parameters.z ^ (-(K : ℤ)) +
      10 ^ 23 * Parameters.q ^ (3 * K) * Real.rpow (Real.log V) (-(7 / 80 : ℝ)) := by
  have hbase := densityLimit_of_removal hrem extremal extremal_isMax
  have hdiff := (relaxed_density_tendsto V).sub hbase
  let A : ℝ := 10 ^ 23 * Parameters.q ^ (3 * K)
  let E : ℝ := 500000 * Parameters.z ^ (-(K : ℤ))
  have hupper : Tendsto (fun N : ℕ => E + A *
      (Real.rpow (Real.log V) (-(7 / 80 : ℝ)) + Real.rpow (Real.log N) (-(7 / 80 : ℝ))))
      atTop (𝓝 (E + A * Real.rpow (Real.log V) (-(7 / 80 : ℝ)))) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_const_nhds.add logarithmic_tail_tendsto).const_mul A)
  apply le_of_tendsto_of_tendsto hdiff hupper
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := (hrem N V K hN hV).2
  rw [← sub_div, div_le_iff₀ hNR]
  simpa only [A, E, mul_comm] using h

theorem one_lt_log_of_four_le {V : ℕ} (hV : 4 ≤ V) : 1 < Real.log V := by
  have h := Real.sum_range_le_log_div (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h
  have h4 : (1 : ℝ) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith
  exact h4.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hV))

noncomputable def rateCutoff (V : ℕ) : ℕ :=
  ⌊Real.log (Real.log V) / (140 * Real.log Parameters.z)⌋₊

theorem rateCutoff_bounds {V : ℕ} (hV : 4 ≤ V) :
    (rateCutoff V : ℝ) * (140 * Real.log Parameters.z) ≤ Real.log (Real.log V) ∧
    Real.log (Real.log V) < ((rateCutoff V : ℝ) + 1) * (140 * Real.log Parameters.z) := by
  have hz : 0 < Real.log Parameters.z := Real.log_pos (by norm_num [Parameters.z])
  have hden : 0 < 140 * Real.log Parameters.z := by positivity
  have hL : 0 ≤ Real.log (Real.log V) := Real.log_nonneg (one_lt_log_of_four_le hV).le
  have hfloor := Nat.floor_le (div_nonneg hL hden.le)
  have hnext := Nat.lt_floor_add_one (Real.log (Real.log V) / (140 * Real.log Parameters.z))
  exact ⟨(le_div_iff₀ hden).mp hfloor, (div_lt_iff₀ hden).mp hnext⟩

theorem optimized_geometric_error {V : ℕ} (hV : 4 ≤ V) :
    Parameters.z ^ (-(rateCutoff V : ℤ)) ≤
      Parameters.z * Real.rpow (Real.log V) (-(1 / 140 : ℝ)) := by
  have hz : 0 < Parameters.z := by norm_num [Parameters.z]
  have hlog : 0 < Real.log V := lt_trans zero_lt_one (one_lt_log_of_four_le hV)
  have hf := (rateCutoff_bounds hV).2
  apply (Real.log_le_log_iff (zpow_pos hz _) (mul_pos hz (Real.rpow_pos_of_pos hlog _))).mp
  rw [Real.log_zpow, Real.log_mul hz.ne' (Real.rpow_pos_of_pos hlog _).ne', Real.log_rpow hlog]
  push_cast
  nlinarith

theorem optimized_sieve_error {V : ℕ} (hV : 4 ≤ V) :
    Parameters.q ^ (3 * rateCutoff V) * Real.rpow (Real.log V) (-(7 / 80 : ℝ)) ≤
      Real.rpow (Real.log V) (-(1 / 140 : ℝ)) := by
  have hq : 0 < Parameters.q := by norm_num [Parameters.q]
  have hlog : 0 < Real.log V := lt_trans zero_lt_one (one_lt_log_of_four_le hV)
  have hhi := (rateCutoff_bounds hV).1
  have hK : (0 : ℝ) ≤ rateCutoff V := Nat.cast_nonneg _
  have hratio : 3 * Real.log Parameters.q ≤ (9 / 112 : ℝ) * (140 * Real.log Parameters.z) := by
    nlinarith [Parameters.log_q_vs_log_z]
  have h1 := mul_le_mul_of_nonneg_left hratio hK
  have h2 := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 9 / 112)
  apply (Real.log_le_log_iff
    (mul_pos (pow_pos hq _) (Real.rpow_pos_of_pos hlog _)) (Real.rpow_pos_of_pos hlog _)).mp
  rw [Real.log_mul (pow_pos hq _).ne' (Real.rpow_pos_of_pos hlog _).ne',
    Real.log_pow, Real.log_rpow hlog, Real.log_rpow hlog]
  push_cast
  nlinarith

theorem effectiveApproximation_of_removal (hrem : RemovalEstimateStatement) :
    EffectiveApproximationStatement := by
  intro V hV
  refine ⟨sub_nonneg.mpr (claimedConstant_le_U hV), ?_⟩
  have hmain := limiting_removal_bound hrem V (rateCutoff V) hV
  have hgeo := mul_le_mul_of_nonneg_left (optimized_geometric_error hV)
    (by norm_num : (0 : ℝ) ≤ 500000)
  have hsieve := mul_le_mul_of_nonneg_left (optimized_sieve_error hV)
    (by norm_num : (0 : ℝ) ≤ 10 ^ 23)
  rw [← mul_assoc, Parameters.irregular_coefficient] at hgeo
  nlinarith

end Erdos302
