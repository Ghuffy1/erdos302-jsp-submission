import Erdos302.SieveBox
import Erdos302.RoughCountDensity

namespace Erdos302

theorem primeModulus_squarefree (P : Finset ℕ) : Squarefree (primeModulus P) := by
  unfold primeModulus
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (Finset.mem_filter.mp hp).2.squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hpq

noncomputable def avoidingPrimes (P : Finset ℕ) (M : ℕ)
    (U : ∀ p : ℕ, Finset (ZMod p × ZMod p)) : Finset (ℕ × ℕ) := by
  classical
  exact (integerBox M).filter (fun t => ∀ p ∈ P, ((t.1 : ZMod p), (t.2 : ZMod p)) ∉ U p)

theorem prime_box_sieve_bound (P : Finset ℕ)
    (U : ∀ p : ℕ, Finset (ZMod p × ZMod p)) {X : ℝ}
    (hX : 1 < X) (hz : 2 ≤ X ^ (1 / 768 : ℝ))
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) < X ^ (1 / 768 : ℝ) ∧
      (U p).card < p ^ 2 ∧ (U p).card ≤ 3 * p) :
    ((avoidingPrimes P ⌊4 * X⌋₊ U).card : ℝ) ≤
      32 * X ^ 2 * (∏ p ∈ P, (1 - (U p).card / (p : ℝ) ^ 2)) + 9 * X ^ (3 / 2 : ℝ) := by
  classical
  let A := P.filter (fun p => 0 < (U p).card)
  let q := primeModulus A
  have hA : ∀ p ∈ A, p.Prime := fun p hp => (hP p (Finset.mem_filter.mp hp).1).1
  have hqA : q.primeFactors = A := by
    rw [primeModulus_primeFactors]
    exact Finset.filter_eq_self.mpr hA
  have hq0 : q ≠ 0 := (primeModulus_pos A).ne'
  have hq : Squarefree q := primeModulus_squarefree A
  have hloc : ∀ p : ℕ, p.Prime → p ∣ q → 0 < (U p).card ∧ (U p).card < p ^ 2 := by
    intro p hp hpq
    have hpA : p ∈ A := hqA ▸ Nat.mem_primeFactors.mpr ⟨hp, hpq, hq0⟩
    obtain ⟨hpP, hcard⟩ := Finset.mem_filter.mp hpA
    exact ⟨hcard, (hP p hpP).2.2.1⟩
  have hsmall : ∀ p : ℕ, p.Prime → p ∣ q →
      (p : ℝ) < X ^ (1 / 768 : ℝ) ∧ (U p).card ≤ 3 * p := by
    intro p hp hpq
    have hpA : p ∈ A := hqA ▸ Nat.mem_primeFactors.mpr ⟨hp, hpq, hq0⟩
    have hpP := (Finset.mem_filter.mp hpA).1
    exact ⟨(hP p hpP).2.1, (hP p hpP).2.2.2⟩
  have hempty (p : ℕ) (hpP : p ∈ P) (hpA : p ∉ A) : U p = ∅ := by
    have hn : ¬ 0 < (U p).card := by simpa [A, hpP] using hpA
    exact Finset.card_eq_zero.mp (by omega)
  have hsets : avoidingResiduePairs q ⌊4 * X⌋₊ U = avoidingPrimes P ⌊4 * X⌋₊ U := by
    ext t
    simp only [avoidingResiduePairs, avoidingPrimes, Finset.mem_filter, hqA]
    constructor
    · rintro ⟨ht, ha⟩
      refine ⟨ht, ?_⟩
      intro p hpP
      by_cases hpA : p ∈ A
      · exact ha p hpA
      · simp [hempty p hpP hpA]
    · rintro ⟨ht, hp⟩
      exact ⟨ht, fun p hpA => hp p (Finset.mem_filter.mp hpA).1⟩
  have hprod : (∏ p ∈ A, (1 - (U p).card / (p : ℝ) ^ 2)) =
      ∏ p ∈ P, (1 - (U p).card / (p : ℝ) ^ 2) := by
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro p hpP hpA
    simp [hempty p hpP hpA]
  have h := residue_sieve_box_bound q hq U hloc hX hz hsmall
  rw [hsets, hqA, hprod] at h
  exact h

end Erdos302
