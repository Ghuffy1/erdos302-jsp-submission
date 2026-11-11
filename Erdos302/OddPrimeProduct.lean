import Erdos302.LineDensity
import Erdos302.ReciprocalPrimeSums
import Erdos302.PrimeReciprocalBounds
import Erdos302.RegularityMoment

namespace Erdos302

noncomputable def oddSievePrimes (Z : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊Z / 2⌋₊).filter (fun p => 3 ≤ p)

theorem mem_oddSievePrimes {Z : ℝ} (hZ : 16 ≤ Z) {p : ℕ} (hp : p ∈ oddSievePrimes Z) :
    p.Prime ∧ 3 ≤ p ∧ (p : ℝ) < Z := by
  obtain ⟨hpN, hp3⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpN, hprime⟩ := Nat.mem_primesLE.mp hpN
  have hf := Nat.floor_le (show (0 : ℝ) ≤ Z / 2 by linarith)
  have hpR : (p : ℝ) ≤ ⌊Z / 2⌋₊ := by exact_mod_cast hpN
  exact ⟨hprime, hp3, by linarith⟩

theorem odd_primes_reciprocal_lower {Z : ℝ} (hZ : 16 ≤ Z) :
    Real.log (Real.log Z) - 5 / 2 ≤ ∑ p ∈ oddSievePrimes Z, (p : ℝ)⁻¹ := by
  let N := ⌊Z / 2⌋₊
  have hN2 : 2 ≤ N := Nat.le_floor (by linarith)
  have hZ0 : 0 < Z := by linarith
  have hlogZ : 0 < Real.log Z := Real.log_pos (by linarith)
  have hNlower : Z / 4 ≤ (N : ℝ) := by
    have h := Nat.lt_floor_add_one (Z / 2)
    dsimp [N]
    linarith
  have hlog4 : 2 * Real.log 4 ≤ Real.log Z := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hZ
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow] at h
    norm_num at h
    exact h
  have hlogN : Real.log Z / 2 ≤ Real.log N := by
    calc
      Real.log Z / 2 ≤ Real.log Z - Real.log 4 := by linarith
      _ = Real.log (Z / 4) := by rw [Real.log_div hZ0.ne' (by norm_num)]
      _ ≤ Real.log N := Real.log_le_log (by positivity) hNlower
  have hloglog : Real.log (Real.log Z) - Real.log 2 ≤ Real.log (Real.log N) := by
    rw [← Real.log_div hlogZ.ne' (by norm_num)]
    exact Real.log_le_log (by positivity) hlogN
  have hset : Nat.primesLE N = insert 2 (oddSievePrimes Z) := by
    ext p
    simp only [oddSievePrimes, Finset.mem_filter, Nat.mem_primesLE, Finset.mem_insert]
    constructor
    · rintro ⟨hpN, hp⟩
      by_cases hp2 : p = 2
      · exact Or.inl hp2
      · exact Or.inr ⟨⟨hpN, hp⟩, by have := hp.two_le; omega⟩
    · rintro (rfl | ⟨⟨hpN, hp⟩, hp3⟩)
      · exact ⟨hN2, Nat.prime_two⟩
      · exact ⟨hpN, hp⟩
  have hnot : 2 ∉ oddSievePrimes Z := by simp [oddSievePrimes]
  have hsum := prime_reciprocal_sum_lower N hN2
  rw [hset, Finset.sum_insert hnot] at hsum
  norm_num at hsum
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  linarith

theorem odd_pair_density_product {Z : ℝ} (hZ : 16 ≤ Z) :
    (∏ p ∈ oddSievePrimes Z,
      (1 - Parameters.beta / p +
        (2 - 3 * Parameters.theta + Parameters.theta ^ 3) / (p : ℝ) ^ 2)) ≤
      256 * (Real.log Z) ^ (-Parameters.beta) := by
  let C := 2 - 3 * Parameters.theta + Parameters.theta ^ 3
  have hbeta0 : 0 < Parameters.beta := by norm_num [Parameters.beta]
  have hbeta2 : Parameters.beta < 2 := by norm_num [Parameters.beta]
  have hC0 : 0 ≤ C := by norm_num [C, Parameters.theta]
  have hconst : (5 / 2 : ℝ) * Parameters.beta + C ≤ 16 / 3 := by
    norm_num [C, Parameters.beta, Parameters.theta]
  have hlog256 : (16 / 3 : ℝ) ≤ Real.log 256 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
    linarith [log_two_lower_two_thirds]
  have hlogZ : 0 < Real.log Z := Real.log_pos (by linarith)
  have hm (p : ℕ) (hp : p ∈ oddSievePrimes Z) :
      0 < 1 - Parameters.beta / p + C / (p : ℝ) ^ 2 := by
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (mem_oddSievePrimes hZ hp).2.1
    have hp0 : (0 : ℝ) < p := by linarith
    have hb := (div_lt_one hp0).mpr (show Parameters.beta < p by linarith)
    have hc : 0 ≤ C / (p : ℝ) ^ 2 := div_nonneg hC0 (sq_nonneg _)
    linarith
  have hlog : Real.log (∏ p ∈ oddSievePrimes Z,
      (1 - Parameters.beta / p + C / (p : ℝ) ^ 2)) ≤
      Real.log 256 + Real.log (Real.log Z) * (-Parameters.beta) := by
    rw [Real.log_prod (fun p hp => (hm p hp).ne')]
    calc
      (∑ p ∈ oddSievePrimes Z, Real.log (1 - Parameters.beta / p + C / (p : ℝ) ^ 2)) ≤
          ∑ p ∈ oddSievePrimes Z, (-Parameters.beta * (p : ℝ)⁻¹ + C * (p : ℝ)⁻¹ ^ 2) := by
        apply Finset.sum_le_sum
        intro p hp
        have h := Real.log_le_sub_one_of_pos (hm p hp)
        simp only [div_eq_mul_inv, inv_pow] at h ⊢
        linarith
      _ = -Parameters.beta * (∑ p ∈ oddSievePrimes Z, (p : ℝ)⁻¹) +
          C * (∑ p ∈ oddSievePrimes Z, (p : ℝ)⁻¹ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ -Parameters.beta * (Real.log (Real.log Z) - 5 / 2) + C := by
        have hs := mul_le_mul_of_nonpos_left (odd_primes_reciprocal_lower hZ) (by linarith : -Parameters.beta ≤ 0)
        have hsq := mul_le_mul_of_nonneg_left
          (prime_reciprocal_square_sum_le_one (oddSievePrimes Z)
            (fun p hp => (mem_oddSievePrimes hZ hp).1)) hC0
        nlinarith
      _ ≤ Real.log 256 + Real.log (Real.log Z) * (-Parameters.beta) := by linarith
  calc
    (∏ p ∈ oddSievePrimes Z,
        (1 - Parameters.beta / p + C / (p : ℝ) ^ 2)) ≤
      Real.exp (Real.log 256 + Real.log (Real.log Z) * (-Parameters.beta)) :=
        Real.le_exp_of_log_le hlog
    _ = 256 * (Real.log Z) ^ (-Parameters.beta) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 256), Real.rpow_def_of_pos hlogZ]

end Erdos302
