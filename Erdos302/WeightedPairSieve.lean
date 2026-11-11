import Erdos302.GlobalLineWeights

namespace Erdos302

theorem lineFactor_product_natCast (w : ℝ) (p a b : ℕ) :
    (∏ l, lineFactor w l ((a : ZMod p), (b : ZMod p))) =
      (if p ∣ a then w else 1) * (if p ∣ b then w else 1) * (if p ∣ a + b then w else 1) := by
  classical
  rw [prod_residueLine]
  simp only [lineFactor, lineCondition, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]

theorem power_weight_le_global (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    w ^ (totalOmega a + totalOmega b + totalOmega (a + b)) ≤
      ∏ p : P, ∏ l, lineFactor w l ((a : ZMod (p : ℕ)), (b : ZMod (p : ℕ))) := by
  classical
  have hA := prime_support_weight_bound P hP ha.ne' hw0 hw1
  have hB := prime_support_weight_bound P hP hb.ne' hw0 hw1
  have hAB := prime_support_weight_bound P hP (show a + b ≠ 0 by omega) hw0 hw1
  have hprod (n : ℕ) : 0 ≤ ∏ p ∈ P, if p ∣ n then w else 1 := by
    apply Finset.prod_nonneg
    intro p hp
    split_ifs <;> positivity
  have htwo := mul_le_mul hA hB (pow_nonneg hw0 _) (hprod a)
  have hthree := mul_le_mul htwo hAB (pow_nonneg hw0 _) (mul_nonneg (hprod a) (hprod b))
  calc
    w ^ (totalOmega a + totalOmega b + totalOmega (a + b)) =
        (w ^ totalOmega a * w ^ totalOmega b) * w ^ totalOmega (a + b) := by rw [pow_add, pow_add]
    _ ≤ ((∏ p ∈ P, if p ∣ a then w else 1) * (∏ p ∈ P, if p ∣ b then w else 1)) *
        (∏ p ∈ P, if p ∣ a + b then w else 1) := hthree
    _ = ∏ p ∈ P, ∏ l, lineFactor w l ((a : ZMod p), (b : ZMod p)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      exact (lineFactor_product_natCast w p a b).symm
    _ = ∏ p : P, ∏ l, lineFactor w l ((a : ZMod (p : ℕ)), (b : ZMod (p : ℕ))) :=
      (P.prod_coe_sort (fun p : ℕ => ∏ l, lineFactor w l ((a : ZMod p), (b : ZMod p)))).symm

theorem averaged_box_sieve (P : Finset ℕ) {w X : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hX : 1 < X) (hz : 2 ≤ X ^ (1 / 768 : ℝ))
    (hP : ∀ p ∈ P, p.Prime ∧ 3 ≤ p ∧ (p : ℝ) < X ^ (1 / 768 : ℝ)) :
    (∑ s : PrimeSelection P, globalSelectionWeight P w s *
      (avoidingPrimes P ⌊4 * X⌋₊ (selectedPrimeResidues P s)).card) ≤
      32 * X ^ 2 * (∏ p ∈ P, (1 - (3 * (1 - w)) / p + (2 - 3 * w + w ^ 3) / (p : ℝ) ^ 2)) +
        9 * X ^ (3 / 2 : ℝ) := by
  classical
  have hbound (s : PrimeSelection P) :
      ((avoidingPrimes P ⌊4 * X⌋₊ (selectedPrimeResidues P s)).card : ℝ) ≤
        32 * X ^ 2 * (∏ p ∈ P, (1 - (selectedPrimeResidues P s p).card / (p : ℝ) ^ 2)) +
          9 * X ^ (3 / 2 : ℝ) := by
    apply prime_box_sieve_bound P (selectedPrimeResidues P s) hX hz
    intro p hp
    rw [selectedPrimeResidues_of_mem P s hp]
    exact ⟨(hP p hp).1, (hP p hp).2.2, card_selectedResidues_lt (hP p hp).2.1 _,
      card_selectedResidues_le p _⟩
  calc
    (∑ s : PrimeSelection P, globalSelectionWeight P w s *
        (avoidingPrimes P ⌊4 * X⌋₊ (selectedPrimeResidues P s)).card) ≤
      ∑ s : PrimeSelection P, globalSelectionWeight P w s *
        (32 * X ^ 2 * (∏ p ∈ P, (1 - (selectedPrimeResidues P s p).card / (p : ℝ) ^ 2)) +
          9 * X ^ (3 / 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro s hs
        exact mul_le_mul_of_nonneg_left (hbound s) (globalSelectionWeight_nonneg P hw0 hw1 s)
    _ = ∑ s : PrimeSelection P,
        (32 * X ^ 2 * (globalSelectionWeight P w s *
          ∏ p ∈ P, (1 - (selectedPrimeResidues P s p).card / (p : ℝ) ^ 2)) +
          9 * X ^ (3 / 2 : ℝ) * globalSelectionWeight P w s) := by
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = 32 * X ^ 2 * (∑ s : PrimeSelection P, globalSelectionWeight P w s *
        ∏ p ∈ P, (1 - (selectedPrimeResidues P s p).card / (p : ℝ) ^ 2)) +
        9 * X ^ (3 / 2 : ℝ) * (∑ s : PrimeSelection P, globalSelectionWeight P w s) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 32 * X ^ 2 * (∏ p ∈ P, (1 - (3 * (1 - w)) / p + (2 - 3 * w + w ^ 3) / (p : ℝ) ^ 2)) +
        9 * X ^ (3 / 2 : ℝ) := by
      rw [globalDensity_average P (fun p hp => (hP p hp).1), globalSelectionWeight_sum, mul_one]

theorem weighted_pair_sieve (P : Finset ℕ) {w X : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hX : 1 < X) (hz : 2 ≤ X ^ (1 / 768 : ℝ))
    (hP : ∀ p ∈ P, p.Prime ∧ 3 ≤ p ∧ (p : ℝ) < X ^ (1 / 768 : ℝ)) :
    (∑ t ∈ integerBox ⌊4 * X⌋₊, w ^ (totalOmega t.1 + totalOmega t.2 + totalOmega (t.1 + t.2))) ≤
      32 * X ^ 2 * (∏ p ∈ P, (1 - (3 * (1 - w)) / p + (2 - 3 * w + w ^ 3) / (p : ℝ) ^ 2)) +
        9 * X ^ (3 / 2 : ℝ) := by
  have hprimes : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  calc
    (∑ t ∈ integerBox ⌊4 * X⌋₊, w ^ (totalOmega t.1 + totalOmega t.2 + totalOmega (t.1 + t.2))) ≤
      ∑ t ∈ integerBox ⌊4 * X⌋₊, ∏ p : P, ∏ l,
        lineFactor w l ((t.1 : ZMod (p : ℕ)), (t.2 : ZMod (p : ℕ))) := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp ht
      exact power_weight_le_global P hprimes hw0 hw1
        (by have := (Finset.mem_Icc.mp ha).1; omega) (by have := (Finset.mem_Icc.mp hb).1; omega)
    _ = ∑ s : PrimeSelection P, globalSelectionWeight P w s *
        (avoidingPrimes P ⌊4 * X⌋₊ (selectedPrimeResidues P s)).card :=
      (globalCard_average P hprimes ⌊4 * X⌋₊ w).symm
    _ ≤ _ := averaged_box_sieve P hw0 hw1 hX hz hP

end Erdos302
