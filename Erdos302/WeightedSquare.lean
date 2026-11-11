import Erdos302.WeightedPairSieve
import Erdos302.OddPrimeProduct
import Erdos302.CommonScaleMean

namespace Erdos302

theorem log_square_le_sixteen_sqrt {X : ℝ} (hX : 1 ≤ X) :
    (Real.log X) ^ 2 ≤ 16 * Real.sqrt X := by
  have hX0 : 0 < X := by linarith
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX
  have h := Real.add_one_le_exp (Real.log X / 4)
  have hlin : Real.log X ≤ 4 * Real.exp (Real.log X / 4) := by linarith
  have hs := pow_le_pow_left₀ hL hlin 2
  have he : (Real.exp (Real.log X / 4)) ^ 2 = Real.sqrt X := by
    rw [pow_two, ← Real.exp_add]
    have harg : Real.log X / 4 + Real.log X / 4 = Real.log X / 2 := by ring
    rw [harg, Real.exp_half, Real.exp_log hX0]
  nlinarith

theorem square_sieve_error_bound {X : ℝ} (hX : 1 < X) (hL : 1 ≤ Real.log X) :
    9 * X ^ (3 / 2 : ℝ) ≤ 144 * X ^ 2 * (Real.log X) ^ (-Parameters.beta) := by
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < Real.log X := by linarith
  have hb : Parameters.beta ≤ 2 := by norm_num [Parameters.beta]
  have hpow : (Real.log X) ^ Parameters.beta ≤ (Real.log X) ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hL hb
  have hupper := hpow.trans (log_square_le_sixteen_sqrt hX.le)
  have hXsqrt : X ^ (3 / 2 : ℝ) * Real.sqrt X = X ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX0]
    norm_num
  have hcancel : (Real.log X) ^ (-Parameters.beta) * (Real.log X) ^ Parameters.beta = 1 := by
    rw [← Real.rpow_add hL0]
    simp
  apply (mul_le_mul_iff_of_pos_right (Real.rpow_pos_of_pos hL0 Parameters.beta)).mp
  calc
    (9 * X ^ (3 / 2 : ℝ)) * (Real.log X) ^ Parameters.beta ≤
        9 * X ^ (3 / 2 : ℝ) * (16 * Real.sqrt X) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = 144 * X ^ 2 := by nlinarith [hXsqrt]
    _ = (144 * X ^ 2 * (Real.log X) ^ (-Parameters.beta)) * (Real.log X) ^ Parameters.beta := by
      rw [mul_assoc, hcancel, mul_one]

theorem root_log_decay_bound {X : ℝ} (hX : 1 < X) :
    (Real.log (X ^ (1 / 768 : ℝ))) ^ (-Parameters.beta) ≤
      (768 : ℝ) ^ 2 * (Real.log X) ^ (-Parameters.beta) := by
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX
  have hcoeff : (768 : ℝ) ^ Parameters.beta ≤ (768 : ℝ) ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 768) (show Parameters.beta ≤ 2 by norm_num [Parameters.beta])
  have hroot : (Real.log (X ^ (1 / 768 : ℝ))) ^ (-Parameters.beta) =
      (768 : ℝ) ^ Parameters.beta * (Real.log X) ^ (-Parameters.beta) := by
    rw [Real.log_rpow hX0, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 768) hL.le,
      one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 768),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 768), inv_inv]
  rw [hroot]
  exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hL.le _)

theorem theta_weighted_square_large {X : ℝ} (hX : 1 < X) (hZ : 16 ≤ X ^ (1 / 768 : ℝ)) :
    (∑ t ∈ integerBox ⌊4 * X⌋₊,
      Parameters.theta ^ (totalOmega t.1 + totalOmega t.2 + totalOmega (t.1 + t.2))) ≤
      (5 : ℝ) * 10 ^ 9 * X ^ 2 * (Real.log X) ^ (-Parameters.beta) := by
  let Z := X ^ (1 / 768 : ℝ)
  have hP : ∀ p ∈ oddSievePrimes Z, p.Prime ∧ 3 ≤ p ∧ (p : ℝ) < X ^ (1 / 768 : ℝ) :=
    fun p hp => mem_oddSievePrimes hZ hp
  have hbase := weighted_pair_sieve (oddSievePrimes Z)
    (by norm_num [Parameters.theta] : 0 ≤ Parameters.theta)
    (by norm_num [Parameters.theta] : Parameters.theta ≤ 1) hX (by linarith) hP
  rw [← Parameters.beta_eq] at hbase
  have hprod := odd_pair_density_product hZ
  have hroot := root_log_decay_bound hX
  have hlogZ : Real.log Z = (1 / 768 : ℝ) * Real.log X := Real.log_rpow (by linarith) _
  have hL : 1 ≤ Real.log X := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ Z by linarith)
    rw [hlogZ] at hlog
    linarith [log_two_lower]
  have herr := square_sieve_error_bound hX hL
  have hnonneg : 0 ≤ X ^ 2 * (Real.log X) ^ (-Parameters.beta) := by positivity
  calc
    (∑ t ∈ integerBox ⌊4 * X⌋₊,
        Parameters.theta ^ (totalOmega t.1 + totalOmega t.2 + totalOmega (t.1 + t.2))) ≤
      32 * X ^ 2 * (256 * (Real.log Z) ^ (-Parameters.beta)) + 9 * X ^ (3 / 2 : ℝ) :=
        hbase.trans (add_le_add (mul_le_mul_of_nonneg_left hprod (by positivity)) le_rfl)
    _ ≤ (32 * 256 * 768 ^ 2 + 144) * (X ^ 2 * (Real.log X) ^ (-Parameters.beta)) := by
      have h := mul_le_mul_of_nonneg_left hroot (show (0 : ℝ) ≤ 32 * X ^ 2 * 256 by positivity)
      dsimp [Z] at *
      nlinarith
    _ ≤ (5 : ℝ) * 10 ^ 9 * X ^ 2 * (Real.log X) ^ (-Parameters.beta) := by
      have hc : (32 * 256 * 768 ^ 2 + 144 : ℝ) ≤ 5 * 10 ^ 9 := by norm_num
      have h := mul_le_mul_of_nonneg_right hc hnonneg
      nlinarith

theorem integerBox_mono {M N : ℕ} (hMN : M ≤ N) : integerBox M ⊆ integerBox N := by
  intro t ht
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp ht
  exact Finset.mem_product.mpr ⟨Finset.Icc_subset_Icc_right hMN ha, Finset.Icc_subset_Icc_right hMN hb⟩

theorem log_double_negative_beta {X : ℝ} (hX : 2 ≤ X) :
    (Real.log X) ^ (-Parameters.beta) ≤ 4 * (Real.log (2 * X)) ^ (-Parameters.beta) := by
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hM : 0 < Real.log (2 * X) := Real.log_pos (by nlinarith)
  have hLM : Real.log (2 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    have h := Real.log_le_log (by norm_num) hX
    linarith
  have he0 : -Parameters.beta ≤ 0 := by norm_num [Parameters.beta]
  have he2 : (-2 : ℝ) ≤ -Parameters.beta := by norm_num [Parameters.beta]
  have hp := Real.rpow_le_rpow_of_nonpos hM hLM he0
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hL.le] at hp
  have htwo : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (-Parameters.beta) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he2
    norm_num at h
    exact h
  have hn := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hL.le (-Parameters.beta))
  nlinarith

theorem theta_weighted_square (X : ℕ) (hX : 2 ≤ X) :
    (∑ t ∈ integerBox (2 * X),
      Parameters.theta ^ (totalOmega t.1 + totalOmega t.2 + totalOmega (t.1 + t.2))) ≤
      (20 : ℝ) * 10 ^ 9 * X ^ 2 * (Real.log (2 * (X : ℝ))) ^ (-Parameters.beta) := by
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  have htheta0 : 0 ≤ Parameters.theta := by norm_num [Parameters.theta]
  have htheta1 : Parameters.theta ≤ 1 := by norm_num [Parameters.theta]
  by_cases hZ : 16 ≤ (X : ℝ) ^ (1 / 768 : ℝ)
  · have hlarge := theta_weighted_square_large (by linarith : (1 : ℝ) < X) hZ
    have hsub : integerBox (2 * X) ⊆ integerBox ⌊4 * (X : ℝ)⌋₊ := by
      apply integerBox_mono
      apply Nat.le_floor
      push_cast
      nlinarith
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun t ht hnot => pow_nonneg htheta0 (totalOmega t.1 + totalOmega t.2 + totalOmega (t.1 + t.2)))
    have hshift := log_double_negative_beta hXR
    have h := mul_le_mul_of_nonneg_left hshift (show (0 : ℝ) ≤ 5 * 10 ^ 9 * (X : ℝ) ^ 2 by positivity)
    exact hsum.trans (hlarge.trans (by nlinarith))
  · have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    have hlog : Real.log ((X : ℝ) ^ (1 / 768 : ℝ)) < Real.log 16 :=
      Real.log_lt_log (Real.rpow_pos_of_pos hX0 _) (lt_of_not_ge hZ)
    rw [Real.log_rpow hX0, show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at hlog
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hL : Real.log (2 * (X : ℝ)) ≤ 3073 := by
      rw [Real.log_mul (by norm_num) hX0.ne']
      norm_num at hlog
      linarith
    have hL1 : 1 ≤ Real.log (2 * (X : ℝ)) := by
      rw [Real.log_mul (by norm_num) hX0.ne']
      have h := Real.log_le_log (by norm_num) hXR
      linarith [log_two_lower]
    have hL0 : 0 < Real.log (2 * (X : ℝ)) := by linarith
    have hp : (Real.log (2 * (X : ℝ))) ^ Parameters.beta ≤ (3073 : ℝ) ^ 2 := by
      have hb := Real.rpow_le_rpow_of_exponent_le hL1 (show Parameters.beta ≤ 2 by norm_num [Parameters.beta])
      rw [Real.rpow_two] at hb
      exact hb.trans (pow_le_pow_left₀ hL0.le hL 2)
    have hcoeff : (4 : ℝ) ≤ 20 * 10 ^ 9 * (Real.log (2 * (X : ℝ))) ^ (-Parameters.beta) := by
      rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv]
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hL0 Parameters.beta)).mpr
      nlinarith
    have hsum : (∑ t ∈ integerBox (2 * X),
        Parameters.theta ^ (totalOmega t.1 + totalOmega t.2 + totalOmega (t.1 + t.2))) ≤ 4 * (X : ℝ) ^ 2 := by
      calc
        (∑ t ∈ integerBox (2 * X),
            Parameters.theta ^ (totalOmega t.1 + totalOmega t.2 + totalOmega (t.1 + t.2))) ≤
          ∑ _ ∈ integerBox (2 * X), (1 : ℝ) := Finset.sum_le_sum (fun t ht => pow_le_one₀ htheta0 htheta1)
        _ = 4 * (X : ℝ) ^ 2 := by simp [integerBox, pow_two]; ring
    have h := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (X : ℝ))
    exact hsum.trans (by nlinarith)

end Erdos302
