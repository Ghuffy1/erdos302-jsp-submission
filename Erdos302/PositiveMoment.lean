import Erdos302.PrimeFactorCounts
import Mathlib.Data.Nat.Cast.Order.Field

namespace Erdos302

def omegaOn (P : Finset ℕ) (n : ℕ) : ℕ := ∑ p ∈ P, n.factorization p

noncomputable def primeMoment (P : Finset ℕ) (z : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, z ^ omegaOn P n

theorem omegaOn_insert {P : Finset ℕ} {p n : ℕ} (hp : p ∉ P) :
    omegaOn (insert p P) n = n.factorization p + omegaOn P n := by
  simp [omegaOn, hp]

theorem omegaOn_mul (P : Finset ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    omegaOn P (a * b) = omegaOn P a + omegaOn P b := by
  simp [omegaOn, Nat.factorization_mul ha hb, Finset.sum_add_distrib]

theorem omegaOn_prime_pow {P : Finset ℕ} {p : ℕ} (hp : p.Prime) (hpP : p ∉ P) (k : ℕ) :
    omegaOn P (p ^ k) = 0 := by
  unfold omegaOn
  apply Finset.sum_eq_zero
  intro q hq
  have hpq : p ≠ q := by rintro rfl; exact hpP hq
  simp [hp.factorization_pow, hpq]

theorem multiples_Icc_image {d : ℕ} (hd : 0 < d) (N : ℕ) :
    (Finset.Icc 1 N).filter (fun n => d ∣ n) =
      (Finset.Icc 1 (N / d)).image (fun n => d * n) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hnI, hdvd⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnpos, hnN⟩ := Finset.mem_Icc.mp hnI
    have hn0 : 0 < n := by omega
    have hmpos := Nat.div_pos (Nat.le_of_dvd hn0 hdvd) hd
    have hmN : n / d ≤ N / d := by
      apply (Nat.le_div_iff_mul_le hd).mpr
      simpa only [Nat.div_mul_cancel hdvd] using hnN
    exact Finset.mem_image.mpr ⟨n / d, Finset.mem_Icc.mpr ⟨hmpos, hmN⟩,
      Nat.mul_div_cancel' hdvd⟩
  · intro hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hmpos, hmN⟩ := Finset.mem_Icc.mp hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd (by omega), ?_⟩, ⟨m, rfl⟩⟩
    simpa only [mul_comm] using (Nat.le_div_iff_mul_le hd).mp hmN

theorem primePower_weighted_multiples {P : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hpP : p ∉ P) (z : ℝ) (N k : ℕ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ^ k ∣ n), z ^ omegaOn P n) =
      primeMoment P z (N / p ^ k) := by
  rw [multiples_Icc_image (pow_pos hp.pos k), Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    rw [omegaOn_mul P (pow_ne_zero k hp.ne_zero) hn0, omegaOn_prime_pow hp hpP, zero_add]
  · intro a ha b hb h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos k) h

theorem pow_eq_one_add_geometric (z : ℝ) (k : ℕ) :
    z ^ k = 1 + (z - 1) * ∑ a ∈ Finset.range k, z ^ a := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ, Finset.sum_range_succ]
    rw [ih]
    ring

theorem geometric_sum_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (L : ℕ) :
    (∑ a ∈ Finset.range L, r ^ a) ≤ (1 - r)⁻¹ := by
  rw [← one_div, le_div_iff₀ (by linarith : 0 < 1 - r)]
  have h := pow_eq_one_add_geometric r L
  have hp := pow_nonneg hr0 L
  nlinarith

theorem primePower_indicator_sum {p n L : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hL : n.factorization p ≤ L) (z : ℝ) :
    (∑ a ∈ Finset.range L, if p ^ (a + 1) ∣ n then z ^ a else 0) =
      ∑ a ∈ Finset.range (n.factorization p), z ^ a := by
  have heq : (Finset.range L).filter (fun a => p ^ (a + 1) ∣ n) =
      Finset.range (n.factorization p) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, hp.pow_dvd_iff_le_factorization hn]
    omega
  rw [← Finset.sum_filter, heq]

def exponentBound (p N : ℕ) : ℕ := (Finset.Icc 1 N).sup (fun n => n.factorization p)

theorem primeMoment_insert {P : Finset ℕ} {p : ℕ} (hp : p.Prime) (hpP : p ∉ P)
    (z : ℝ) (N : ℕ) :
    primeMoment (insert p P) z N = primeMoment P z N + (z - 1) *
      ∑ a ∈ Finset.range (exponentBound p N),
        z ^ a * primeMoment P z (N / p ^ (a + 1)) := by
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      z ^ omegaOn (insert p P) n = z ^ omegaOn P n + (z - 1) *
        ∑ a ∈ Finset.range (exponentBound p N),
          if p ^ (a + 1) ∣ n then z ^ omegaOn P n * z ^ a else 0 := by
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    have hL : n.factorization p ≤ exponentBound p N :=
      Finset.le_sup (f := fun m => m.factorization p) hn
    have hi := primePower_indicator_sum hp hn0 hL z
    have hpow := pow_eq_one_add_geometric z (n.factorization p)
    have hscale : (∑ a ∈ Finset.range (exponentBound p N),
        if p ^ (a + 1) ∣ n then z ^ omegaOn P n * z ^ a else 0) =
        z ^ omegaOn P n * (∑ a ∈ Finset.range (exponentBound p N),
          if p ^ (a + 1) ∣ n then z ^ a else 0) := by
      simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [hscale, hi, omegaOn_insert hpP, pow_add, hpow]
    ring
  change (∑ n ∈ Finset.Icc 1 N, z ^ omegaOn (insert p P) n) = _
  rw [Finset.sum_congr rfl hpoint]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have hm := primePower_weighted_multiples hp hpP z N (a + 1)
  rw [← hm, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> ring

noncomputable def momentProduct (P : Finset ℕ) (z : ℝ) : ℝ :=
  ∏ p ∈ P, (1 + (z - 1) / ((p : ℝ) - z))

theorem momentProduct_nonneg (z : ℝ) (hz1 : 1 ≤ z) (hz2 : z < 2)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : 0 ≤ momentProduct P z := by
  apply Finset.prod_nonneg
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
  exact add_nonneg zero_le_one (div_nonneg (by linarith) (by linarith))

theorem primeMoment_product_bound (z : ℝ) (hz1 : 1 ≤ z) (hz2 : z < 2) (P : Finset ℕ) :
    (∀ p ∈ P, p.Prime) → ∀ N : ℕ, primeMoment P z N ≤ (N : ℝ) * momentProduct P z := by
  induction P using Finset.induction_on with
  | empty =>
    intro hP N
    simp [primeMoment, omegaOn, momentProduct]
  | @insert p P hpP ih =>
    intro hP N
    have hp : p.Prime := hP p (Finset.mem_insert_self p P)
    have hPrimes : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    let C := momentProduct P z
    have hC : 0 ≤ C := momentProduct_nonneg z hz1 hz2 P hPrimes
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hpz : 0 < (p : ℝ) - z := by linarith
    have hz0 : 0 ≤ z := by linarith
    have hr0 : (0 : ℝ) ≤ z / p := div_nonneg hz0 hp0.le
    have hr1 : z / (p : ℝ) < 1 := (div_lt_one hp0).mpr (by linarith)
    have hS : (∑ a ∈ Finset.range (exponentBound p N),
        z ^ a * primeMoment P z (N / p ^ (a + 1))) ≤ (N : ℝ) * C / ((p : ℝ) - z) := by
      calc
        (∑ a ∈ Finset.range (exponentBound p N),
            z ^ a * primeMoment P z (N / p ^ (a + 1))) ≤
          ∑ a ∈ Finset.range (exponentBound p N),
            z ^ a * ((N : ℝ) / (p : ℝ) ^ (a + 1) * C) := by
          apply Finset.sum_le_sum
          intro a ha
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hz0 a)
          have hM := ih hPrimes (N / p ^ (a + 1))
          have hdiv : ((N / p ^ (a + 1) : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ (a + 1) := by
            simpa only [Nat.cast_pow] using (Nat.cast_div_le (m := N) (n := p ^ (a + 1)) :
              ((N / p ^ (a + 1) : ℕ) : ℝ) ≤ (N : ℝ) / (p ^ (a + 1) : ℕ))
          exact hM.trans (mul_le_mul_of_nonneg_right hdiv hC)
        _ = ((N : ℝ) * C / p) *
            ∑ a ∈ Finset.range (exponentBound p N), (z / (p : ℝ)) ^ a := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          simp only [div_pow, pow_succ]
          field_simp
        _ ≤ ((N : ℝ) * C / p) * (1 - z / (p : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left (geometric_sum_le hr0 hr1 _) (by positivity)
        _ = (N : ℝ) * C / ((p : ℝ) - z) := by
          have hden : 1 - z / (p : ℝ) ≠ 0 := by linarith
          field_simp
    calc
      primeMoment (insert p P) z N = primeMoment P z N + (z - 1) *
          ∑ a ∈ Finset.range (exponentBound p N),
            z ^ a * primeMoment P z (N / p ^ (a + 1)) := primeMoment_insert hp hpP z N
      _ ≤ (N : ℝ) * C + (z - 1) * ((N : ℝ) * C / ((p : ℝ) - z)) :=
        add_le_add (ih hPrimes N) (mul_le_mul_of_nonneg_left hS (by linarith))
      _ = (N : ℝ) * momentProduct (insert p P) z := by
        simp only [momentProduct, Finset.prod_insert hpP]
        change (N : ℝ) * C + (z - 1) * ((N : ℝ) * C / ((p : ℝ) - z)) =
          (N : ℝ) * ((1 + (z - 1) / ((p : ℝ) - z)) * C)
        ring

theorem smallOmega_eq_omegaOn_primes (n X : ℕ) :
    smallOmega n X = omegaOn ((Finset.range (X + 1)).filter Nat.Prime) n := by
  unfold smallOmega omegaOn
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime
  · simp [hprime]
  · simp [hprime, Nat.factorization_eq_zero_of_not_prime n hprime]

theorem smallOmega_moment_product_bound (z : ℝ) (hz1 : 1 ≤ z) (hz2 : z < 2) (N X : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, z ^ smallOmega n X) ≤ (N : ℝ) *
      momentProduct ((Finset.range (X + 1)).filter Nat.Prime) z := by
  have h := primeMoment_product_bound z hz1 hz2 ((Finset.range (X + 1)).filter Nat.Prime)
    (fun p hp => (Finset.mem_filter.mp hp).2) N
  simpa only [primeMoment, ← smallOmega_eq_omegaOn_primes] using h

theorem smallOmega_tail_product_bound (z : ℝ) (hz1 : 1 < z) (hz2 : z < 2)
    (N X : ℕ) (T : ℝ) :
    ((((Finset.Icc 1 N).filter (fun n => T < (smallOmega n X : ℝ))).card : ℕ) : ℝ) *
      Real.rpow z T ≤ (N : ℝ) * momentProduct ((Finset.range (X + 1)).filter Nat.Prime) z := by
  classical
  let B := (Finset.Icc 1 N).filter (fun n => T < (smallOmega n X : ℝ))
  have hB : (B.card : ℝ) * Real.rpow z T ≤ ∑ n ∈ B, z ^ smallOmega n X := by
    calc
      (B.card : ℝ) * Real.rpow z T = ∑ _ ∈ B, Real.rpow z T := by simp
      _ ≤ ∑ n ∈ B, z ^ smallOmega n X := by
        apply Finset.sum_le_sum
        intro n hn
        have hT : T ≤ (smallOmega n X : ℝ) := (Finset.mem_filter.mp hn).2.le
        calc
          Real.rpow z T ≤ Real.rpow z (smallOmega n X : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hz1.le hT
          _ = z ^ smallOmega n X := Real.rpow_natCast z _
  have hsum : (∑ n ∈ B, z ^ smallOmega n X) ≤ ∑ n ∈ Finset.Icc 1 N, z ^ smallOmega n X := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro n hn hnot
    exact pow_nonneg (by linarith) _
  exact hB.trans (hsum.trans (smallOmega_moment_product_bound z hz1.le hz2 N X))

end Erdos302
