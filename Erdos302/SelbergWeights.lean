import Erdos302.DualDivisors

namespace Erdos302

open scoped ArithmeticFunction.Moebius

noncomputable def sieveMass (s : BoundingSieve) (D : ℝ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, if (d : ℝ) ≤ D then s.selbergTerms d else 0

noncomputable def sieveDiagonal (s : BoundingSieve) (D : ℝ) (l : ℕ) : ℝ :=
  if (l : ℝ) ≤ D then (μ l : ℝ) * s.selbergTerms l / sieveMass s D else 0

noncomputable def sieveLambda (s : BoundingSieve) (D : ℝ) (d : ℕ) : ℝ :=
  (s.nu d)⁻¹ * upperMoebiusTransform s.prodPrimes (sieveDiagonal s D) d

theorem sieveMass_pos (s : BoundingSieve) {D : ℝ} (hD : 1 ≤ D) : 0 < sieveMass s D := by
  unfold sieveMass
  have hone : 1 ∈ s.prodPrimes.divisors := Nat.one_mem_divisors.mpr s.prodPrimes_ne_zero
  apply Finset.sum_pos'
  · intro d hd
    split_ifs
    · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)).le
    · exact le_rfl
  · refine ⟨1, hone, ?_⟩
    simpa only [Nat.cast_one, ite_eq_left hD] using s.selbergTerms_pos (one_dvd s.prodPrimes)

theorem sieveDiagonal_abs_sum (s : BoundingSieve) {D : ℝ} (hD : 1 ≤ D) :
    (∑ l ∈ s.prodPrimes.divisors, |sieveDiagonal s D l|) = 1 := by
  have hG := sieveMass_pos s hD
  have hterm (l : ℕ) (hl : l ∈ s.prodPrimes.divisors) :
      |sieveDiagonal s D l| =
        (if (l : ℝ) ≤ D then s.selbergTerms l else 0) / sieveMass s D := by
    have hH := s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)
    have hmu : |(μ l : ℝ)| = 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
        (s.squarefree_of_mem_divisors_prodPrimes hl)
    unfold sieveDiagonal
    split_ifs
    · rw [abs_div, abs_mul, hmu, abs_of_pos hH, abs_of_pos hG, one_mul]
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  change sieveMass s D / sieveMass s D = 1
  exact div_self hG.ne'

theorem sieveLambda_transform (s : BoundingSieve) (D : ℝ) {l : ℕ} (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * sieveLambda s D d else 0) =
      sieveDiagonal s D l := by
  have hterm (d : ℕ) (hd : d ∈ s.prodPrimes.divisors) :
      (if l ∣ d then s.nu d * sieveLambda s D d else 0) =
        (if l ∣ d then upperMoebiusTransform s.prodPrimes (sieveDiagonal s D) d else 0) := by
    have hnu : s.nu d ≠ 0 := s.nu_ne_zero (Nat.dvd_of_mem_divisors hd)
    simp only [sieveLambda, ← mul_assoc, mul_inv_cancel₀ hnu, one_mul]
  rw [Finset.sum_congr rfl hterm]
  exact upperMoebiusTransform_inverse s.prodPrimes_ne_zero hl (sieveDiagonal s D)

theorem sieveLambda_one (s : BoundingSieve) {D : ℝ} (hD : 1 ≤ D) : sieveLambda s D 1 = 1 := by
  have hG := sieveMass_pos s hD
  have hnu1 := s.nu_mult.map_one
  unfold sieveLambda upperMoebiusTransform
  rw [hnu1, inv_one, one_mul, Nat.div_one,
    Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℝ) * sieveDiagonal s D (s.prodPrimes / b)),
    Nat.sum_div_divisors s.prodPrimes (fun d => (μ d : ℝ) * sieveDiagonal s D d)]
  have hterm (l : ℕ) (hl : l ∈ s.prodPrimes.divisors) :
      (μ l : ℝ) * sieveDiagonal s D l =
        (if (l : ℝ) ≤ D then s.selbergTerms l else 0) / sieveMass s D := by
    have hmu : (μ l : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (s.squarefree_of_mem_divisors_prodPrimes hl)
    unfold sieveDiagonal
    split_ifs
    · calc
        (μ l : ℝ) * ((μ l : ℝ) * s.selbergTerms l / sieveMass s D) =
            (μ l : ℝ) ^ 2 * s.selbergTerms l / sieveMass s D := by ring
        _ = s.selbergTerms l / sieveMass s D := by rw [hmu, one_mul]
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  exact div_self hG.ne'

theorem sieveLambda_abs_le_inv (s : BoundingSieve) {D : ℝ} (hD : 1 ≤ D)
    {d : ℕ} (hd : d ∣ s.prodPrimes) : |sieveLambda s D d| ≤ (s.nu d)⁻¹ := by
  have hnu := s.nu_pos_of_dvd_prodPrimes hd
  unfold sieveLambda
  rw [abs_mul, abs_of_pos (inv_pos.mpr hnu)]
  have h := upperMoebiusTransform_abs_bound s.prodPrimes_ne_zero hd (sieveDiagonal s D)
  rw [sieveDiagonal_abs_sum s hD] at h
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h (inv_pos.mpr hnu).le

theorem sieveLambda_abs_le_square (s : BoundingSieve) {D : ℝ} (hD : 1 ≤ D)
    {d : ℕ} (hd : d ∣ s.prodPrimes) (hnu : 1 / (d : ℝ) ^ 2 ≤ s.nu d) :
    |sieveLambda s D d| ≤ (d : ℝ) ^ 2 := by
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero s.prodPrimes_ne_zero)
  have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 / (d : ℝ) ^ 2) hnu
  have hinv : (s.nu d)⁻¹ ≤ (d : ℝ) ^ 2 := by simpa only [one_div, inv_inv] using h
  exact (sieveLambda_abs_le_inv s hD hd).trans hinv

theorem sieveLambda_mainSum (s : BoundingSieve) {D : ℝ} (hD : 1 ≤ D) :
    s.mainSum (BoundingSieve.lambdaSquared (sieveLambda s D)) = (sieveMass s D)⁻¹ := by
  have hG := sieveMass_pos s hD
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hterm (l : ℕ) (hl : l ∈ s.prodPrimes.divisors) :
      (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * sieveLambda s D d else 0) ^ 2 =
      (if (l : ℝ) ≤ D then s.selbergTerms l else 0) / (sieveMass s D) ^ 2 := by
    rw [sieveLambda_transform s D (Nat.dvd_of_mem_divisors hl)]
    have hH := s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)
    have hmu : (μ l : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (s.squarefree_of_mem_divisors_prodPrimes hl)
    unfold sieveDiagonal
    split_ifs
    · calc
        (s.selbergTerms l)⁻¹ * ((μ l : ℝ) * s.selbergTerms l / sieveMass s D) ^ 2 =
            (μ l : ℝ) ^ 2 * s.selbergTerms l / (sieveMass s D) ^ 2 := by
              field_simp
              <;> ring
        _ = s.selbergTerms l / (sieveMass s D) ^ 2 := by rw [hmu, one_mul]
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  change sieveMass s D / (sieveMass s D) ^ 2 = (sieveMass s D)⁻¹
  field_simp

theorem sieveLambda_eq_zero_of_lt (s : BoundingSieve) {D : ℝ} {d : ℕ}
    (hd : d ∣ s.prodPrimes) (hDd : D < (d : ℝ)) : sieveLambda s D d = 0 := by
  unfold sieveLambda upperMoebiusTransform
  rw [Nat.sum_divisorsAntidiagonal' (fun a b =>
    (μ a : ℝ) * sieveDiagonal s D (s.prodPrimes / b))]
  have hsum : (∑ e ∈ (s.prodPrimes / d).divisors,
      (μ ((s.prodPrimes / d) / e) : ℝ) * sieveDiagonal s D (s.prodPrimes / e)) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have heN := Nat.dvd_of_mem_divisors he
    have heP : e ∣ s.prodPrimes := heN.trans (Nat.div_dvd_of_dvd hd)
    have hdPe : d ∣ s.prodPrimes / e := by
      apply (Nat.dvd_div_iff_mul_dvd heP).mpr
      simpa only [mul_comm] using (Nat.dvd_div_iff_mul_dvd hd).mp heN
    have hPe : 0 < s.prodPrimes / e := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero s.prodPrimes_ne_zero) heP)
      (Nat.pos_of_dvd_of_pos heP (Nat.pos_of_ne_zero s.prodPrimes_ne_zero))
    have hdle : (d : ℝ) ≤ (s.prodPrimes / e : ℕ) := by
      exact_mod_cast Nat.le_of_dvd hPe hdPe
    have hnot : ¬ ((s.prodPrimes / e : ℕ) : ℝ) ≤ D := by linarith
    simp only [sieveDiagonal, ite_eq_right hnot, mul_zero]
  rw [hsum, mul_zero]

theorem sieve_nu_lower_square (s : BoundingSieve)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ s.prodPrimes → 1 / (p : ℝ) ^ 2 ≤ s.nu p)
    {d : ℕ} (hd : d ∣ s.prodPrimes) : 1 / (d : ℝ) ^ 2 ≤ s.nu d := by
  have hsq := s.squarefree_of_dvd_prodPrimes hd
  have hprod : (∏ p ∈ d.primeFactors, 1 / (p : ℝ) ^ 2) = 1 / (d : ℝ) ^ 2 := by
    simp only [one_div, Finset.prod_inv_distrib, Finset.prod_pow]
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  rw [← hprod, ← s.prod_primeFactors_nu hd]
  apply Finset.prod_le_prod₀
  · intro p hp
    positivity
  · intro p hp
    exact hprime p (Nat.prime_of_mem_primeFactors hp) ((Nat.dvd_of_mem_primeFactors hp).trans hd)

end Erdos302
