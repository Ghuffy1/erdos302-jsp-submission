import Erdos302.SelbergWeights
import Erdos302.RegularityMoment

namespace Erdos302

noncomputable def fullSieveMass (s : BoundingSieve) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d

theorem fullSieveMass_pos (s : BoundingSieve) : 0 < fullSieveMass s := by
  apply Finset.sum_pos'
  · intro d hd
    exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)).le
  · exact ⟨1, Nat.one_mem_divisors.mpr s.prodPrimes_ne_zero,
      s.selbergTerms_pos (one_dvd s.prodPrimes)⟩

theorem sieve_prime_mass (s : BoundingSieve) {p : ℕ} (hp : p.Prime) (hpP : p ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors, if p ∣ d then s.selbergTerms d else 0) =
      s.nu p * fullSieveMass s := by
  let H := s.selbergTerms
  have hcop : p.Coprime (s.prodPrimes / p) := Nat.coprime_of_squarefree_mul
    (by simpa only [Nat.mul_div_cancel' hpP] using s.prodPrimes_squarefree)
  have hpart : (∑ d ∈ s.prodPrimes.divisors, if p ∣ d then H d else 0) =
      H p * ∑ e ∈ (s.prodPrimes / p).divisors, H e := by
    rw [sum_upper_divisors s.prodPrimes_ne_zero hpP, Finset.mul_sum]
    calc
      (∑ e ∈ (s.prodPrimes / p).divisors, H (s.prodPrimes / e)) =
          ∑ e ∈ (s.prodPrimes / p).divisors, H p * H ((s.prodPrimes / p) / e) := by
        apply Finset.sum_congr rfl
        intro e he
        have heN := Nat.dvd_of_mem_divisors he
        have hquot : s.prodPrimes / e = p * ((s.prodPrimes / p) / e) := by
          calc
            s.prodPrimes / e = (p * (s.prodPrimes / p)) / e := by rw [Nat.mul_div_cancel' hpP]
            _ = p * ((s.prodPrimes / p) / e) := Nat.mul_div_assoc p heN
        rw [hquot]
        exact s.selbergTerms_isMultiplicative.map_mul_of_coprime
          (hcop.of_dvd_right (Nat.div_dvd_of_dvd heN))
      _ = ∑ e ∈ (s.prodPrimes / p).divisors, H p * H e := by
        rw [← Finset.mul_sum, Nat.sum_div_divisors, Finset.mul_sum]
  let T : ArithmeticFunction ℝ := (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * H
  have hTmult : T.IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul s.selbergTerms_isMultiplicative
  have hprime : (∑ d ∈ p.divisors, H d) = 1 + H p := by
    rw [← s.selbergTerms_isMultiplicative.prodPrimeFactors_one_add_of_squarefree hp.squarefree]
    simp only [hp.primeFactors, Finset.prod_singleton]
    rfl
  have htotal : fullSieveMass s = (1 + H p) * ∑ e ∈ (s.prodPrimes / p).divisors, H e := by
    have h := hTmult.map_mul_of_coprime hcop
    rw [Nat.mul_div_cancel' hpP] at h
    simp only [T, ArithmeticFunction.coe_zeta_mul_apply] at h
    rw [hprime] at h
    exact h
  have hnu : 0 < 1 - s.nu p := by linarith [s.nu_lt_one_of_prime p hp hpP]
  have hH : H p = s.nu p * (1 - s.nu p)⁻¹ := by
    simp only [H, BoundingSieve.selbergTerms_apply, hp.primeFactors, Finset.prod_singleton]
  have hr : H p = s.nu p * (1 + H p) := by rw [hH]; field_simp; ring
  rw [hpart, htotal]
  calc
    H p * (∑ e ∈ (s.prodPrimes / p).divisors, H e) =
        (s.nu p * (1 + H p)) * (∑ e ∈ (s.prodPrimes / p).divisors, H e) := by rw [← hr]
    _ = s.nu p * ((1 + H p) * ∑ e ∈ (s.prodPrimes / p).divisors, H e) := by ring

theorem sieve_divisor_log (s : BoundingSieve) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    Real.log d = ∑ p ∈ s.prodPrimes.primeFactors, if p ∣ d then Real.log p else 0 := by
  have hsq := s.squarefree_of_dvd_prodPrimes hd
  have hprod : (∏ p ∈ d.primeFactors, (p : ℝ)) = (d : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  rw [← Finset.sum_filter, Nat.primeFactors_filter_dvd_of_dvd s.prodPrimes_ne_zero hd, ← hprod]
  rw [Real.log_prod]
  intro p hp
  exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero

theorem fullSieve_log_moment (s : BoundingSieve) :
    (∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d * Real.log d) =
      fullSieveMass s * ∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p := by
  calc
    (∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d * Real.log d) =
        ∑ d ∈ s.prodPrimes.divisors, ∑ p ∈ s.prodPrimes.primeFactors,
          if p ∣ d then s.selbergTerms d * Real.log p else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [sieve_divisor_log s (Nat.dvd_of_mem_divisors hd), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp
    _ = ∑ p ∈ s.prodPrimes.primeFactors, ∑ d ∈ s.prodPrimes.divisors,
        if p ∣ d then s.selbergTerms d * Real.log p else 0 := Finset.sum_comm
    _ = ∑ p ∈ s.prodPrimes.primeFactors,
        (s.nu p * fullSieveMass s) * Real.log p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← sieve_prime_mass s (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp),
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> simp
    _ = fullSieveMass s * ∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

theorem sieveMass_ge_half_of_log_moment (s : BoundingSieve) {D : ℝ} (hD : 1 < D)
    (hlog : (∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d * Real.log d) ≤
      fullSieveMass s * Real.log D / 2) :
    fullSieveMass s / 2 ≤ sieveMass s D := by
  have hlogD := Real.log_pos hD
  have hpoint (d : ℕ) (hd : d ∈ s.prodPrimes.divisors) :
      s.selbergTerms d * Real.log D ≤ s.selbergTerms d * Real.log d +
        (if (d : ℝ) ≤ D then s.selbergTerms d else 0) * Real.log D := by
    have hH := (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)).le
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    by_cases hdD : (d : ℝ) ≤ D
    · rw [ite_eq_left hdD]
      have hnonneg := mul_nonneg hH (Real.log_nonneg hd1)
      linarith
    · rw [ite_eq_right hdD, zero_mul, add_zero]
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (by linarith : 0 < D) (le_of_lt (lt_of_not_ge hdD))) hH
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  change fullSieveMass s * Real.log D ≤
    (∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d * Real.log d) +
      sieveMass s D * Real.log D at hsum
  nlinarith

theorem prime_log_sum_le_eight_log (P : Finset ℕ) {z : ℝ} (hz : 2 ≤ z)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) < z) :
    (∑ p ∈ P, Real.log p / p) ≤ 8 * Real.log z := by
  have hfloor : 2 ≤ ⌊z⌋₊ := Nat.le_floor hz
  have hsub : P ⊆ Nat.primesLE ⌊z⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hP p hp).2.le, (hP p hp).1⟩
  have hsum : (∑ p ∈ P, Real.log p / p) ≤
      ∑ p ∈ Nat.primesLE ⌊z⌋₊, Real.log p / p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp hnot
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le))
      (Nat.cast_nonneg p)
  have hlogfloor : Real.log (⌊z⌋₊ : ℝ) ≤ Real.log z :=
    Real.log_le_log (by exact_mod_cast (show 0 < ⌊z⌋₊ by omega)) (Nat.floor_le (by linarith))
  have hlogz : (2 / 3 : ℝ) ≤ Real.log z :=
    log_two_lower_two_thirds.trans (Real.log_le_log (by norm_num) hz)
  have hbound := weighted_prime_log_le ⌊z⌋₊ (by omega)
  linarith

theorem sieveMass_ge_half (s : BoundingSieve) {z D : ℝ} (hz : 2 ≤ z) (hD : 1 < D)
    (hDz : 48 * Real.log z ≤ Real.log D)
    (hloc : ∀ p : ℕ, p.Prime → p ∣ s.prodPrimes →
      (p : ℝ) < z ∧ s.nu p ≤ 3 / (p : ℝ)) :
    fullSieveMass s / 2 ≤ sieveMass s D := by
  have hsum : (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) ≤ 24 * Real.log z := by
    calc
      (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) ≤
          ∑ p ∈ s.prodPrimes.primeFactors, (3 / (p : ℝ)) * Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        exact mul_le_mul_of_nonneg_right (hloc p hprime (Nat.dvd_of_mem_primeFactors hp)).2
          (Real.log_nonneg (by exact_mod_cast hprime.one_le))
      _ = 3 * ∑ p ∈ s.prodPrimes.primeFactors, Real.log p / p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ ≤ 3 * (8 * Real.log z) := mul_le_mul_of_nonneg_left
        (prime_log_sum_le_eight_log _ hz (fun p hp =>
          ⟨Nat.prime_of_mem_primeFactors hp,
            (hloc p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)).1⟩))
        (by norm_num)
      _ = 24 * Real.log z := by ring
  apply sieveMass_ge_half_of_log_moment s hD
  rw [fullSieve_log_moment]
  have h := mul_le_mul_of_nonneg_left hsum (fullSieveMass_pos s).le
  have h' := mul_le_mul_of_nonneg_left hDz (fullSieveMass_pos s).le
  nlinarith

theorem fullSieveMass_product (s : BoundingSieve) :
    fullSieveMass s = ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)⁻¹ := by
  unfold fullSieveMass
  rw [← s.selbergTerms_isMultiplicative.prodPrimeFactors_one_add_of_squarefree
    s.prodPrimes_squarefree]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < 1 - s.nu p := by
    linarith [s.nu_lt_one_of_prime p hprime (Nat.dvd_of_mem_primeFactors hp)]
  simp only [BoundingSieve.selbergTerms_apply, hprime.primeFactors, Finset.prod_singleton]
  field_simp
  <;> ring

theorem sieveMass_inverse_bound (s : BoundingSieve) {z D : ℝ} (hz : 2 ≤ z) (hD : 1 < D)
    (hDz : 48 * Real.log z ≤ Real.log D)
    (hloc : ∀ p : ℕ, p.Prime → p ∣ s.prodPrimes →
      (p : ℝ) < z ∧ s.nu p ≤ 3 / (p : ℝ)) :
    (sieveMass s D)⁻¹ ≤ 2 * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  have hhalf := sieveMass_ge_half s hz hD hDz hloc
  have hpos : 0 < fullSieveMass s / 2 := by linarith [fullSieveMass_pos s]
  have hinv := one_div_le_one_div_of_le hpos hhalf
  have hprod : (fullSieveMass s)⁻¹ = ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
    rw [fullSieveMass_product, Finset.prod_inv_distrib, inv_inv]
  calc
    (sieveMass s D)⁻¹ ≤ (fullSieveMass s / 2)⁻¹ := by simpa only [one_div] using hinv
    _ = 2 * (fullSieveMass s)⁻¹ := by rw [inv_div]; ring
    _ = 2 * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by rw [hprod]

end Erdos302
