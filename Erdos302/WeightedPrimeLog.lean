import Erdos302.ElementaryPrimeBounds
import Mathlib.Data.Nat.Choose.Factorization

namespace Erdos302

theorem factorial_prime_valuation_lower {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ (Nat.factorial N).factorization p := by
  rw [Nat.factorization_factorial hp (show Nat.log p N < Nat.log p N + 2 by omega)]
  have h := Finset.single_le_sum (f := fun a : ℕ => N / p ^ a)
    (fun a ha => Nat.zero_le _) (show 1 ∈ Finset.Ico 1 (Nat.log p N + 2) by simp)
  simpa only [pow_one] using h

theorem prime_floor_log_sum_le_factorial (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, ((N / p : ℕ) : ℝ) * Real.log p) ≤ Real.log (Nat.factorial N) := by
  have hsub : Nat.primesLE N ⊆ (Nat.factorial N).primeFactors := by
    intro p hp
    obtain ⟨hpN, hpprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hpprime, Nat.dvd_factorial hpprime.pos hpN, Nat.factorial_ne_zero N⟩
  have hlog : Real.log (Nat.factorial N) =
      ∑ p ∈ (Nat.factorial N).primeFactors, ((Nat.factorial N).factorization p : ℝ) * Real.log p := by
    simpa only [Finsupp.sum, Nat.support_factorization] using
      Real.log_nat_eq_sum_factorization (Nat.factorial N)
  rw [hlog]
  calc
    (∑ p ∈ Nat.primesLE N, ((N / p : ℕ) : ℝ) * Real.log p) ≤
        ∑ p ∈ Nat.primesLE N, ((Nat.factorial N).factorization p : ℝ) * Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      have hpprime := Nat.prime_of_mem_primesLE hp
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast factorial_prime_valuation_lower hpprime N)
      exact Real.log_nonneg (by exact_mod_cast hpprime.one_le)
    _ ≤ ∑ p ∈ (Nat.factorial N).primeFactors,
        ((Nat.factorial N).factorization p : ℝ) * Real.log p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp hnot
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))

theorem log_factorial_le_mul_log (N : ℕ) :
    Real.log (Nat.factorial N) ≤ (N : ℝ) * Real.log N := by
  calc
    Real.log (Nat.factorial N) ≤ Real.log ((N ^ N : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast Nat.factorial_pos N) (by exact_mod_cast Nat.factorial_le_pow N)
    _ = (N : ℝ) * Real.log N := by rw [Nat.cast_pow, Real.log_pow]

theorem weighted_prime_log_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ p ∈ Nat.primesLE N, Real.log p / p) ≤ Real.log N + 4 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hterm (p : ℕ) (hp : p ∈ Nat.primesLE N) :
      (N : ℝ) * (Real.log p / p) ≤ ((N / p : ℕ) : ℝ) * Real.log p + Real.log p := by
    have hpprime := Nat.prime_of_mem_primesLE hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hf : (N : ℝ) / p ≤ ((N / p : ℕ) : ℝ) + 1 := by
      apply (div_le_iff₀ hpR).mpr
      have hnat : N ≤ (N / p + 1) * p := by
        have hdiv := Nat.mod_add_div N p
        have hmod := Nat.mod_lt N hpprime.pos
        nlinarith
      exact_mod_cast hnat
    calc
      (N : ℝ) * (Real.log p / p) = ((N : ℝ) / p) * Real.log p := by ring
      _ ≤ (((N / p : ℕ) : ℝ) + 1) * Real.log p :=
        mul_le_mul_of_nonneg_right hf (Real.log_nonneg (by exact_mod_cast hpprime.one_le))
      _ = ((N / p : ℕ) : ℝ) * Real.log p + Real.log p := by ring
  apply (mul_le_mul_iff_of_pos_left hNR).mp
  calc
    (N : ℝ) * (∑ p ∈ Nat.primesLE N, Real.log p / p) ≤
        (∑ p ∈ Nat.primesLE N, ((N / p : ℕ) : ℝ) * Real.log p) +
          (∑ p ∈ Nat.primesLE N, Real.log p) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hterm
    _ ≤ Real.log (Nat.factorial N) + Chebyshev.theta N := by
      rw [Chebyshev.theta_eq_sum_primesLE_log]
      exact add_le_add (prime_floor_log_sum_le_factorial N) le_rfl
    _ ≤ (N : ℝ) * Real.log N + 4 * N :=
      add_le_add (log_factorial_le_mul_log N)
        ((Chebyshev.theta_le_psi N).trans (psi_le_four_mul (Nat.cast_nonneg N)))
    _ = (N : ℝ) * (Real.log N + 4) := by ring

end Erdos302
