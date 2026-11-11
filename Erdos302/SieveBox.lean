import Erdos302.ResidueSieveBound

namespace Erdos302

theorem sieve_level_error_bound {X : ℝ} (hX : 1 ≤ X) {M : ℕ} (hM : (M : ℝ) ≤ 4 * X) :
    (2 * M * (X ^ (1 / 16 : ℝ)) ^ 2 + (X ^ (1 / 16 : ℝ)) ^ 4) *
      (X ^ (1 / 16 : ℝ)) ^ 6 ≤ 9 * X ^ (3 / 2 : ℝ) := by
  have hX0 : 0 < X := by linarith
  have h8 : (X ^ (1 / 16 : ℝ)) ^ 8 = X ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hX0.le]
    norm_num
  have h10 : (X ^ (1 / 16 : ℝ)) ^ 10 ≤ X ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hX0.le]
    apply Real.rpow_le_rpow_of_exponent_le hX
    norm_num
  have hmul : X * X ^ (1 / 2 : ℝ) = X ^ (3 / 2 : ℝ) := by
    calc
      X * X ^ (1 / 2 : ℝ) = X ^ (1 : ℝ) * X ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = X ^ (1 + 1 / 2 : ℝ) := (Real.rpow_add hX0 _ _).symm
      _ = X ^ (3 / 2 : ℝ) := by norm_num
  calc
    (2 * M * (X ^ (1 / 16 : ℝ)) ^ 2 + (X ^ (1 / 16 : ℝ)) ^ 4) *
        (X ^ (1 / 16 : ℝ)) ^ 6 =
      2 * M * (X ^ (1 / 16 : ℝ)) ^ 8 + (X ^ (1 / 16 : ℝ)) ^ 10 := by ring
    _ ≤ 8 * X * (X ^ (1 / 16 : ℝ)) ^ 8 + X ^ (3 / 2 : ℝ) := by
      exact add_le_add (mul_le_mul_of_nonneg_right (by linarith : 2 * (M : ℝ) ≤ 8 * X)
        (by positivity)) h10
    _ = 9 * X ^ (3 / 2 : ℝ) := by rw [h8]; nlinarith [hmul]

theorem residue_sieve_box_bound (q : ℕ) (hq : Squarefree q)
    (U : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    (hloc : ∀ p : ℕ, p.Prime → p ∣ q → 0 < (U p).card ∧ (U p).card < p ^ 2)
    {X : ℝ} (hX : 1 < X) (hz : 2 ≤ X ^ (1 / 768 : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ q →
      (p : ℝ) < X ^ (1 / 768 : ℝ) ∧ (U p).card ≤ 3 * p) :
    ((avoidingResiduePairs q ⌊4 * X⌋₊ U).card : ℝ) ≤
      32 * X ^ 2 * (∏ p ∈ q.primeFactors, (1 - (U p).card / (p : ℝ) ^ 2)) +
        9 * X ^ (3 / 2 : ℝ) := by
  have hX0 : 0 < X := by linarith
  have hD : 1 < X ^ (1 / 16 : ℝ) := Real.one_lt_rpow hX (by norm_num)
  have hlog : 48 * Real.log (X ^ (1 / 768 : ℝ)) ≤ Real.log (X ^ (1 / 16 : ℝ)) := by
    rw [Real.log_rpow hX0, Real.log_rpow hX0]
    linarith
  have hbase := residue_sieve_product_bound q hq U hloc ⌊4 * X⌋₊ hz hD hlog hsmall
  have hM : (⌊4 * X⌋₊ : ℝ) ≤ 4 * X := Nat.floor_le (by positivity)
  have hM2 : (⌊4 * X⌋₊ : ℝ) ^ 2 ≤ 16 * X ^ 2 := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg ⌊4 * X⌋₊) hM 2
    nlinarith
  have hprod : 0 ≤ ∏ p ∈ q.primeFactors, (1 - (U p).card / (p : ℝ) ^ 2) := by
    apply Finset.prod_nonneg
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hcard : ((U p).card : ℝ) < (p : ℝ) ^ 2 := by
      exact_mod_cast (hloc p hprime (Nat.dvd_of_mem_primeFactors hp)).2
    have hfrac := (div_lt_one (sq_pos_of_pos hp0)).mpr hcard
    linarith
  calc
    ((avoidingResiduePairs q ⌊4 * X⌋₊ U).card : ℝ) ≤
        2 * (⌊4 * X⌋₊ : ℝ) ^ 2 *
          (∏ p ∈ q.primeFactors, (1 - (U p).card / (p : ℝ) ^ 2)) +
          (2 * ⌊4 * X⌋₊ * (X ^ (1 / 16 : ℝ)) ^ 2 + (X ^ (1 / 16 : ℝ)) ^ 4) *
            (X ^ (1 / 16 : ℝ)) ^ 6 := hbase
    _ ≤ 32 * X ^ 2 * (∏ p ∈ q.primeFactors, (1 - (U p).card / (p : ℝ) ^ 2)) +
        9 * X ^ (3 / 2 : ℝ) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by nlinarith : 2 * (⌊4 * X⌋₊ : ℝ) ^ 2 ≤ 32 * X ^ 2) hprod
      · exact sieve_level_error_bound hX.le hM

end Erdos302
