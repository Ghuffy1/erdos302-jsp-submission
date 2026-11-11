import Erdos302.ResidueSieve

namespace Erdos302

noncomputable def residueSieveData (q : ℕ) (hq : Squarefree q)
    (U : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    (hloc : ∀ p : ℕ, p.Prime → p ∣ q → 0 < (U p).card ∧ (U p).card < p ^ 2) : BoundingSieve where
  -- The finite-index sieve theorem uses the modulus and density fields.
  support := ∅
  weights := fun _ => 0
  weights_nonneg := fun _ => le_rfl
  totalMass := 0
  prodPrimes := q
  prodPrimes_squarefree := hq
  nu := residueDensity U
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := by
    intro p hp hpq
    rw [residueDensity_prime U hp]
    exact div_pos (by exact_mod_cast (hloc p hp hpq).1) (sq_pos_of_pos (by exact_mod_cast hp.pos))
  nu_lt_one_of_prime := by
    intro p hp hpq
    rw [residueDensity_prime U hp]
    apply (div_lt_one (sq_pos_of_pos (by exact_mod_cast hp.pos))).mpr
    exact_mod_cast (hloc p hp hpq).2

theorem residue_sieve_square_bound (q : ℕ) (hq : Squarefree q)
    (U : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    (hloc : ∀ p : ℕ, p.Prime → p ∣ q → 0 < (U p).card ∧ (U p).card < p ^ 2)
    (M : ℕ) {D : ℝ} (hD : 1 ≤ D) :
    ((avoidingResiduePairs q M U).card : ℝ) ≤
      (M : ℝ) ^ 2 / sieveMass (residueSieveData q hq U hloc) D +
        (2 * M * D ^ 2 + D ^ 4) * D ^ 6 := by
  let s := residueSieveData q hq U hloc
  have hnu : ∀ d, d ∣ s.prodPrimes → 1 / (d : ℝ) ^ 2 ≤ s.nu d := by
    intro d hd
    apply sieve_nu_lower_square s _ hd
    intro p hp hpq
    change 1 / (p : ℝ) ^ 2 ≤ residueDensity U p
    rw [residueDensity_prime U hp]
    apply div_le_div_of_nonneg_right _ (sq_nonneg (p : ℝ))
    exact_mod_cast (hloc p hp hpq).1
  have hGA : avoidingResiduePairs q M U ⊆ integerBox M := Finset.filter_subset _ _
  apply finite_sieve_square_bound s hD (by positivity) hnu (integerBox M)
    (avoidingResiduePairs q M U) hGA (residueIndicator U)
  · intro t ht
    exact residueIndicator_one U t
  · intro t ht d hd hd1
    exact residueIndicator_zero_of_avoiding U hq.ne_zero (Nat.dvd_of_mem_divisors hd) hd1 ht
  · intro t ht d hd e he
    exact residueIndicator_lcm U d e t
  · intro d hd e he hdD heD
    have hde : d.lcm e ∣ q := Nat.lcm_dvd_iff.mpr
      ⟨Nat.dvd_of_mem_divisors hd, Nat.dvd_of_mem_divisors he⟩
    have hsq := hq.squarefree_of_dvd hde
    have herror := residueIndicator_error U (d.lcm e) hsq M
    change |(∑ t ∈ integerBox M, residueIndicator U (d.lcm e) t) -
      (M : ℝ) ^ 2 * residueDensity U (d.lcm e)| ≤ _
    have hlcm : ((d.lcm e : ℕ) : ℝ) ≤ D ^ 2 := by
      calc
        ((d.lcm e : ℕ) : ℝ) ≤ (d : ℝ) * e := by
          exact_mod_cast Nat.lcm_le_mul (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)
        _ ≤ D * D := mul_le_mul hdD heD (Nat.cast_nonneg e) (by linarith)
        _ = D ^ 2 := by ring
    have hsqle : (((d.lcm e : ℕ) : ℝ)) ^ 2 ≤ D ^ 4 := by
      have h := pow_le_pow_left₀ (Nat.cast_nonneg (d.lcm e)) hlcm 2
      simpa only [← pow_mul] using h
    have hmul := mul_le_mul_of_nonneg_left hlcm (show (0 : ℝ) ≤ 2 * M by positivity)
    exact herror.trans (by nlinarith)

theorem residue_sieve_product_bound (q : ℕ) (hq : Squarefree q)
    (U : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    (hloc : ∀ p : ℕ, p.Prime → p ∣ q → 0 < (U p).card ∧ (U p).card < p ^ 2)
    (M : ℕ) {z D : ℝ} (hz : 2 ≤ z) (hD : 1 < D)
    (hDz : 48 * Real.log z ≤ Real.log D)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) < z ∧ (U p).card ≤ 3 * p) :
    ((avoidingResiduePairs q M U).card : ℝ) ≤
      2 * (M : ℝ) ^ 2 * (∏ p ∈ q.primeFactors, (1 - (U p).card / (p : ℝ) ^ 2)) +
        (2 * M * D ^ 2 + D ^ 4) * D ^ 6 := by
  let s := residueSieveData q hq U hloc
  have hprime : ∀ p : ℕ, p.Prime → p ∣ s.prodPrimes →
      (p : ℝ) < z ∧ s.nu p ≤ 3 / (p : ℝ) := by
    intro p hp hpq
    refine ⟨(hsmall p hp hpq).1, ?_⟩
    change residueDensity U p ≤ 3 / (p : ℝ)
    rw [residueDensity_prime U hp]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hcard : ((U p).card : ℝ) ≤ 3 * p := by exact_mod_cast (hsmall p hp hpq).2
    calc
      ((U p).card : ℝ) / (p : ℝ) ^ 2 ≤ (3 * p) / (p : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hcard (sq_nonneg (p : ℝ))
      _ = 3 / (p : ℝ) := by field_simp
  have hmass := sieveMass_inverse_bound s hz hD hDz hprime
  have hprod : (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) =
      ∏ p ∈ q.primeFactors, (1 - (U p).card / (p : ℝ) ^ 2) := by
    apply Finset.prod_congr rfl
    intro p hp
    change 1 - residueDensity U p = 1 - (U p).card / (p : ℝ) ^ 2
    rw [residueDensity_prime U (Nat.prime_of_mem_primeFactors hp)]
  rw [hprod] at hmass
  have hbase := residue_sieve_square_bound q hq U hloc M hD.le
  calc
    ((avoidingResiduePairs q M U).card : ℝ) ≤
        (M : ℝ) ^ 2 / sieveMass s D + (2 * M * D ^ 2 + D ^ 4) * D ^ 6 := hbase
    _ ≤ 2 * (M : ℝ) ^ 2 * (∏ p ∈ q.primeFactors, (1 - (U p).card / (p : ℝ) ^ 2)) +
        (2 * M * D ^ 2 + D ^ 4) * D ^ 6 := by
      have h := mul_le_mul_of_nonneg_left hmass (sq_nonneg (M : ℝ))
      calc
        _ = (M : ℝ) ^ 2 * (sieveMass s D)⁻¹ + (2 * M * D ^ 2 + D ^ 4) * D ^ 6 := by
          rw [div_eq_mul_inv]
        _ ≤ (M : ℝ) ^ 2 * (2 * (∏ p ∈ q.primeFactors, (1 - (U p).card / (p : ℝ) ^ 2))) +
            (2 * M * D ^ 2 + D ^ 4) * D ^ 6 := add_le_add h le_rfl
        _ = _ := by ring

end Erdos302
