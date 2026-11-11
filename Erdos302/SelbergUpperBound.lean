import Erdos302.SieveMass

namespace Erdos302

theorem sieveLambda_sum_abs_bound (s : BoundingSieve) {D : ℝ} (hD : 1 ≤ D)
    (hnu : ∀ d, d ∣ s.prodPrimes → 1 / (d : ℝ) ^ 2 ≤ s.nu d) :
    (∑ d ∈ s.prodPrimes.divisors, |sieveLambda s D d|) ≤ D ^ 3 := by
  let J : Finset ℕ := s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ D)
  have hsub : J ⊆ Finset.Icc 1 ⌊D⌋₊ := by
    intro d hd
    obtain ⟨hdP, hdD⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, Nat.le_floor hdD⟩
  have hcard : (J.card : ℝ) ≤ D := by
    have hnat : J.card ≤ ⌊D⌋₊ := by simpa using Finset.card_le_card hsub
    exact (show (J.card : ℝ) ≤ ⌊D⌋₊ by exact_mod_cast hnat).trans (Nat.floor_le (by linarith))
  have hsum : (∑ d ∈ s.prodPrimes.divisors, |sieveLambda s D d|) =
      ∑ d ∈ J, |sieveLambda s D d| := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hdP hdJ
    have hdD : D < (d : ℝ) := by simpa [J, hdP] using hdJ
    rw [sieveLambda_eq_zero_of_lt s (Nat.dvd_of_mem_divisors hdP) hdD, abs_zero]
  rw [hsum]
  calc
    (∑ d ∈ J, |sieveLambda s D d|) ≤ ∑ _ ∈ J, D ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdP, hdD⟩ := Finset.mem_filter.mp hd
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      exact (sieveLambda_abs_le_square s hD (Nat.dvd_of_mem_divisors hdP)
        (hnu d (Nat.dvd_of_mem_divisors hdP))).trans (pow_le_pow_left₀ hd0 hdD 2)
    _ = (J.card : ℝ) * D ^ 2 := by simp
    _ ≤ D * D ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg D)
    _ = D ^ 3 := by ring

theorem sieve_quadratic_form (s : BoundingSieve) (w : ℕ → ℝ) :
    (∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
      w d * w e * s.nu (d.lcm e)) = s.mainSum (BoundingSieve.lambdaSquared w) := by
  rw [s.mainSum_lambdaSquared_eq_sum_sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hne : s.nu (d.gcd e) ≠ 0 := s.nu_ne_zero
    ((Nat.gcd_dvd_left d e).trans (Nat.dvd_of_mem_divisors hd))
  rw [s.nu_mult.map_lcm hne]
  ring

theorem finite_sieve_square_bound {α : Type*} (s : BoundingSieve) {D T R : ℝ}
    (hD : 1 ≤ D) (hR : 0 ≤ R)
    (hnu : ∀ d, d ∣ s.prodPrimes → 1 / (d : ℝ) ^ 2 ≤ s.nu d)
    (A G : Finset α) (hGA : G ⊆ A) (I : ℕ → α → ℝ)
    (hIone : ∀ a ∈ G, I 1 a = 1)
    (hIgood : ∀ a ∈ G, ∀ d ∈ s.prodPrimes.divisors, d ≠ 1 → I d a = 0)
    (hIprod : ∀ a ∈ A, ∀ d ∈ s.prodPrimes.divisors, ∀ e ∈ s.prodPrimes.divisors,
      I d a * I e a = I (d.lcm e) a)
    (herr : ∀ d ∈ s.prodPrimes.divisors, ∀ e ∈ s.prodPrimes.divisors,
      (d : ℝ) ≤ D → (e : ℝ) ≤ D →
      |(∑ a ∈ A, I (d.lcm e) a) - T * s.nu (d.lcm e)| ≤ R) :
    (G.card : ℝ) ≤ T / sieveMass s D + R * D ^ 6 := by
  classical
  let w := sieveLambda s D
  let P := s.prodPrimes.divisors
  have hgood (a : α) (ha : a ∈ G) : (∑ d ∈ P, w d * I d a) = 1 := by
    rw [Finset.sum_eq_single 1]
    · change sieveLambda s D 1 * I 1 a = 1
      rw [sieveLambda_one s hD, hIone a ha, mul_one]
    · intro d hd hd1
      rw [hIgood a ha d hd hd1, mul_zero]
    · intro hnot
      exact (hnot (Nat.one_mem_divisors.mpr s.prodPrimes_ne_zero)).elim
  have hcard : (G.card : ℝ) ≤ ∑ a ∈ A, (∑ d ∈ P, w d * I d a) ^ 2 := by
    calc
      (G.card : ℝ) = ∑ _ ∈ G, (1 : ℝ) := by simp
      _ = ∑ a ∈ G, (∑ d ∈ P, w d * I d a) ^ 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hgood a ha, one_pow]
      _ ≤ ∑ a ∈ A, (∑ d ∈ P, w d * I d a) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hGA (fun a ha hnot => sq_nonneg _)
  have hpoint (a : α) (ha : a ∈ A) :
      (∑ d ∈ P, w d * I d a) ^ 2 =
        ∑ d ∈ P, ∑ e ∈ P, w d * w e * I (d.lcm e) a := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [← hIprod a ha d hd e he]
    ring
  have hexpand : (∑ a ∈ A, (∑ d ∈ P, w d * I d a) ^ 2) =
      ∑ d ∈ P, ∑ e ∈ P, w d * w e * (∑ a ∈ A, I (d.lcm e) a) := by
    rw [Finset.sum_congr rfl hpoint, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mul_sum]
  have herror (d : ℕ) (hd : d ∈ P) (e : ℕ) (he : e ∈ P) :
      w d * w e * ((∑ a ∈ A, I (d.lcm e) a) - T * s.nu (d.lcm e)) ≤
        R * |w d| * |w e| := by
    by_cases hdD : (d : ℝ) ≤ D
    · by_cases heD : (e : ℝ) ≤ D
      · calc
          w d * w e * ((∑ a ∈ A, I (d.lcm e) a) - T * s.nu (d.lcm e)) ≤
              |w d * w e * ((∑ a ∈ A, I (d.lcm e) a) - T * s.nu (d.lcm e))| := le_abs_self _
          _ = |w d| * |w e| * |(∑ a ∈ A, I (d.lcm e) a) - T * s.nu (d.lcm e)| := by rw [abs_mul, abs_mul]
          _ ≤ |w d| * |w e| * R := mul_le_mul_of_nonneg_left (herr d hd e he hdD heD) (by positivity)
          _ = R * |w d| * |w e| := by ring
      · have hz : w e = 0 := sieveLambda_eq_zero_of_lt s (Nat.dvd_of_mem_divisors he) (lt_of_not_ge heD)
        simp only [hz, mul_zero, abs_zero, zero_mul, le_refl]
    · have hz : w d = 0 := sieveLambda_eq_zero_of_lt s (Nat.dvd_of_mem_divisors hd) (lt_of_not_ge hdD)
      simp only [hz, mul_zero, abs_zero, zero_mul, le_refl]
  have hmain : (∑ d ∈ P, ∑ e ∈ P, w d * w e * s.nu (d.lcm e)) = (sieveMass s D)⁻¹ := by
    rw [sieve_quadratic_form, sieveLambda_mainSum s hD]
  have hsum : (∑ d ∈ P, |w d|) ≤ D ^ 3 := sieveLambda_sum_abs_bound s hD hnu
  have hsum0 : 0 ≤ ∑ d ∈ P, |w d| := Finset.sum_nonneg (fun d hd => abs_nonneg _)
  have hsum2 : (∑ d ∈ P, |w d|) ^ 2 ≤ D ^ 6 := by
    have h := pow_le_pow_left₀ hsum0 hsum 2
    simpa only [← pow_mul] using h
  have hde (d : ℕ) (hd : d ∈ P) (e : ℕ) (he : e ∈ P) :
      w d * w e * (∑ a ∈ A, I (d.lcm e) a) ≤
        T * (w d * w e * s.nu (d.lcm e)) + R * |w d| * |w e| := by
    have h := herror d hd e he
    nlinarith
  calc
    (G.card : ℝ) ≤ ∑ a ∈ A, (∑ d ∈ P, w d * I d a) ^ 2 := hcard
    _ = ∑ d ∈ P, ∑ e ∈ P, w d * w e * (∑ a ∈ A, I (d.lcm e) a) := hexpand
    _ ≤ ∑ d ∈ P, ∑ e ∈ P,
        (T * (w d * w e * s.nu (d.lcm e)) + R * |w d| * |w e|) :=
      Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hde d hd e he))
    _ = T * (∑ d ∈ P, ∑ e ∈ P, w d * w e * s.nu (d.lcm e)) +
        R * (∑ d ∈ P, |w d|) ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, pow_two]
      apply congrArg₂ (· + ·)
      · rfl
      · apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro e he
        ring
    _ = T / sieveMass s D + R * (∑ d ∈ P, |w d|) ^ 2 := by rw [hmain, div_eq_mul_inv]
    _ ≤ T / sieveMass s D + R * D ^ 6 := add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum2 hR)

end Erdos302
