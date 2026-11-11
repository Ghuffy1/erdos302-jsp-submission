import Erdos302.LargeRegularCount

namespace Erdos302

open Filter
open scoped Topology

/-- The uniform removal estimate, with no additional analytic hypotheses. -/
theorem removalEstimate : RemovalEstimateStatement :=
  removalEstimate_of_largeRegular_bound largeRegularParameters_card_bound

/-- Every choice of exact finite extremal cardinalities has the stated density. -/
theorem densityLimit : DensityLimitStatement :=
  densityLimit_of_removal removalEstimate

/-- The effective approximation to the density through finite-prime relaxations. -/
theorem effectiveApproximation : EffectiveApproximationStatement :=
  effectiveApproximation_of_removal removalEstimate

theorem extremal_density_tendsto :
    Tendsto (fun N : ℕ => (extremal N : ℝ) / N) atTop (𝓝 claimedConstant) :=
  densityLimit extremal extremal_isMax

theorem uniform_finite_removal_rate (N V : ℕ) (hN : 4 ≤ N) (hV : 4 ≤ V) :
    0 ≤ ((relaxedExtremal V N : ℝ) - extremal N) / N ∧
    ((relaxedExtremal V N : ℝ) - extremal N) / N ≤
      (2 * (10 : ℝ) ^ 23 + 561000) *
        (Real.log (min V N)) ^ (-(1 / 140 : ℝ)) := by
  let W := min V N
  have hW : 4 ≤ W := le_min hV hN
  let K := rateCutoff W
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogW : 0 < Real.log W := by linarith [one_lt_log_of_four_le hW]
  have hlogV : Real.log W ≤ Real.log V :=
    Real.log_le_log (by exact_mod_cast (show 0 < W by omega)) (by exact_mod_cast min_le_left V N)
  have hlogN : Real.log W ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (show 0 < W by omega)) (by exact_mod_cast min_le_right V N)
  have hv := Real.rpow_le_rpow_of_nonpos hlogW hlogV (by norm_num : -(7 / 80 : ℝ) ≤ 0)
  have hn := Real.rpow_le_rpow_of_nonpos hlogW hlogN (by norm_num : -(7 / 80 : ℝ) ≤ 0)
  obtain ⟨hlo, hhi⟩ := removalEstimate N V K hN hV
  refine ⟨div_nonneg hlo hN0.le, ?_⟩
  apply (div_le_iff₀ hN0).mpr
  have hq : 0 ≤ (10 : ℝ) ^ 23 * Parameters.q ^ (3 * K) :=
    mul_nonneg (by norm_num) (pow_nonneg (by norm_num [Parameters.q]) _)
  have htail := mul_le_mul_of_nonneg_left (add_le_add hv hn) hq
  have hgeo := mul_le_mul_of_nonneg_left (optimized_geometric_error hW)
    (by norm_num : (0 : ℝ) ≤ 500000)
  have hsieve := mul_le_mul_of_nonneg_left (optimized_sieve_error hW)
    (by norm_num : (0 : ℝ) ≤ 2 * 10 ^ 23)
  rw [← mul_assoc, Parameters.irregular_coefficient] at hgeo
  have herr : 500000 * Parameters.z ^ (-(K : ℤ)) +
      10 ^ 23 * Parameters.q ^ (3 * K) *
        ((Real.log V) ^ (-(7 / 80 : ℝ)) + (Real.log N) ^ (-(7 / 80 : ℝ))) ≤
      (2 * (10 : ℝ) ^ 23 + 561000) * (Real.log W) ^ (-(1 / 140 : ℝ)) := by
    dsimp [K] at *
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left herr hN0.le
  simpa only [W, Nat.cast_min, mul_comm] using hhi.trans hscaled

end Erdos302
