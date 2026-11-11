import Erdos302.RemovalReduction
import Erdos302.WeightedSquare
import Erdos302.CommonScaleSharp

namespace Erdos302

theorem regular_triple_weight {g u v K : ℕ}
    (hg : 0 < g) (hu : 0 < u) (hv : 0 < v) (hw : 2 ≤ u + v)
    (ha : KRegular K (g * u * v))
    (hb : KRegular K (g * u * (u + v)))
    (hc : KRegular K (g * v * (u + v))) :
    1 ≤ Parameters.q ^ (3 * K) *
      (Real.log (u + v) / Real.log 2) ^ Parameters.M *
      Parameters.gamma ^ smallOmega g (u + v) *
      Parameters.theta ^ (totalOmega u + totalOmega v + totalOmega (u + v)) := by
  have hq : 0 < Parameters.q := by norm_num [Parameters.q]
  have hgamma : 0 < Parameters.gamma := by norm_num [Parameters.gamma]
  have htheta : 0 < Parameters.theta := by norm_num [Parameters.theta]
  have hlogq : 0 ≤ Real.log Parameters.q := Real.log_nonneg (by norm_num [Parameters.q])
  have htwo : 0 < Real.log 2 := by linarith [log_two_lower]
  have hlogw : 0 < Real.log (u + v) :=
    Real.log_pos (by exact_mod_cast (show 1 < u + v by omega))
  have hratio : 0 < Real.log (u + v) / Real.log 2 := div_pos hlogw htwo
  have hsum := triple_smallOmega hg hu hv (u + v)
  rw [smallOmega_eq_totalOmega (Nat.le_add_right u v),
    smallOmega_eq_totalOmega (Nat.le_add_left v u), smallOmega_eq_totalOmega le_rfl] at hsum
  have hsumR :
      (smallOmega (g * u * v) (u + v) : ℝ) +
      smallOmega (g * u * (u + v)) (u + v) + smallOmega (g * v * (u + v)) (u + v) =
      3 * smallOmega g (u + v) +
        2 * (totalOmega u + totalOmega v + totalOmega (u + v) : ℕ) := by
    exact_mod_cast hsum
  have hs := add_le_add (add_le_add (ha (u + v) hw) (hb (u + v) hw)) (hc (u + v) hw)
  rw [hsumR] at hs
  have h := mul_le_mul_of_nonneg_right hs hlogq
  have hlg : Real.log Parameters.gamma = -3 * Real.log Parameters.q := by
    rw [Parameters.gamma_eq, Real.log_inv, Real.log_pow]
    norm_num
  have hlt : Real.log Parameters.theta = -2 * Real.log Parameters.q := by
    rw [Parameters.theta_eq, Real.log_inv, Real.log_pow]
    norm_num
  apply (Real.log_le_log_iff zero_lt_one
    (mul_pos (mul_pos (mul_pos (pow_pos hq _) (Real.rpow_pos_of_pos hratio _))
      (pow_pos hgamma _)) (pow_pos htheta _))).mp
  rw [Real.log_one, Real.log_mul (mul_pos (mul_pos (pow_pos hq _)
    (Real.rpow_pos_of_pos hratio _)) (pow_pos hgamma _)).ne' (pow_pos htheta _).ne',
    Real.log_mul (mul_pos (pow_pos hq _) (Real.rpow_pos_of_pos hratio _)).ne'
      (pow_pos hgamma _).ne',
    Real.log_mul (pow_pos hq _).ne' (Real.rpow_pos_of_pos hratio _).ne',
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_rpow hratio, hlg, hlt]
  push_cast
  dsimp [Parameters.M]
  push_cast at h
  nlinarith

theorem regular_triple_block_weight {g u v K X : ℕ}
    (hX : 2 ≤ X) (hg : 0 < g) (hu : 0 < u) (hv : X ≤ v)
    (huX : u ≤ 2 * X) (hvX : v ≤ 2 * X)
    (ha : KRegular K (g * u * v))
    (hb : KRegular K (g * u * (u + v)))
    (hc : KRegular K (g * v * (u + v))) :
    1 ≤ 9 * Parameters.q ^ (3 * K) * (Real.log (2 * (X : ℝ))) ^ Parameters.M *
      Parameters.gamma ^ smallOmega g X *
      Parameters.theta ^ (totalOmega u + totalOmega v + totalOmega (u + v)) := by
  have hbase := regular_triple_weight hg hu (by omega) (by omega) ha hb hc
  have htwo : 0 < Real.log 2 := by linarith [log_two_lower]
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hR : 0 < Real.log (2 * (X : ℝ)) := Real.log_pos (by
    exact_mod_cast (show 1 < 2 * X by omega))
  have hratio0 : 0 ≤ Real.log (u + v) / Real.log 2 := by
    apply div_nonneg _ htwo.le
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ u + v by omega))
  have hratio : Real.log (u + v) / Real.log 2 ≤ 3 * Real.log (2 * (X : ℝ)) := by
    apply (div_le_iff₀ htwo).mpr
    have hw4 : (u + v : ℝ) ≤ 4 * X := by exact_mod_cast (show u + v ≤ 4 * X by omega)
    have hl := Real.log_le_log (by exact_mod_cast (show 0 < u + v by omega)) hw4
    have hx : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
    rw [show 4 * (X : ℝ) = 2 * (2 * X) by ring,
      Real.log_mul (by norm_num) (by positivity)] at hl
    have hr := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'
    nlinarith [log_two_lower_two_thirds, mul_nonneg hx (show 0 ≤ 3 * Real.log 2 - 2 by
      linarith [log_two_lower_two_thirds])]
  have hM0 : 0 ≤ Parameters.M := by
    dsimp [Parameters.M, Parameters.A]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num [Parameters.q]))
  have hM2 : Parameters.M ≤ 2 := by
    have h := Parameters.log_q_upper
    dsimp [Parameters.M, Parameters.A]
    linarith
  have hp := Real.rpow_le_rpow hratio0 hratio hM0
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hR.le] at hp
  have h3 : (3 : ℝ) ^ Parameters.M ≤ 9 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hM2
    norm_num at h ⊢
    exact h
  have hp' : (Real.log (u + v) / Real.log 2) ^ Parameters.M ≤
      9 * (Real.log (2 * (X : ℝ))) ^ Parameters.M := by
    exact hp.trans (mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hR.le _))
  have hg' : Parameters.gamma ^ smallOmega g (u + v) ≤ Parameters.gamma ^ smallOmega g X :=
    pow_le_pow_of_le_one (by norm_num [Parameters.gamma]) (by norm_num [Parameters.gamma])
      (smallOmega_mono g (by omega))
  have hmul := mul_le_mul hp' hg'
    (pow_nonneg (by norm_num [Parameters.gamma]) _) (by positivity)
  have h := mul_le_mul_of_nonneg_left hmul
    (show 0 ≤ Parameters.q ^ (3 * K) *
      Parameters.theta ^ (totalOmega u + totalOmega v + totalOmega (u + v)) by
        apply mul_nonneg <;> apply pow_nonneg <;> norm_num [Parameters.q, Parameters.theta])
  exact hbase.trans (by nlinarith)

end Erdos302
