import Erdos302.LineDensity

namespace Erdos302

theorem omegaOn_le_totalOmega (P : Finset ℕ) (n : ℕ) : omegaOn P n ≤ totalOmega n := by
  let R := Finset.range (n + 1)
  have hsub : P ⊆ R ∪ P := Finset.subset_union_right
  have hle : (∑ p ∈ P, n.factorization p) ≤ ∑ p ∈ R ∪ P, n.factorization p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp hnot => Nat.zero_le _)
  have heq : (∑ p ∈ R ∪ P, n.factorization p) = ∑ p ∈ R, n.factorization p := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro p hp hpR
    have hnp : n < p := by
      have h := hpR
      simp only [R, Finset.mem_range] at h
      omega
    exact Nat.factorization_eq_zero_of_lt hnp
  exact hle.trans_eq heq

theorem prime_divisor_count_le_totalOmega (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (hn : n ≠ 0) :
    (∑ p ∈ P, if p ∣ n then 1 else 0) ≤ totalOmega n := by
  apply le_trans _ (omegaOn_le_totalOmega P n)
  apply Finset.sum_le_sum
  intro p hp
  by_cases hd : p ∣ n
  · rw [ite_eq_left hd]
    exact ((hP p hp).pow_dvd_iff_le_factorization hn).mp (by simpa using hd)
  · simp only [ite_eq_right hd]
    exact Nat.zero_le _

theorem prime_support_weight_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (hn : n ≠ 0) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    w ^ totalOmega n ≤ ∏ p ∈ P, if p ∣ n then w else 1 := by
  have hcount := prime_divisor_count_le_totalOmega P hP hn
  calc
    w ^ totalOmega n ≤ w ^ (∑ p ∈ P, if p ∣ n then 1 else 0) :=
      pow_le_pow_of_le_one hw0 hw1 hcount
    _ = ∏ p ∈ P, if p ∣ n then w else 1 := by
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro p hp
      split_ifs <;> simp

end Erdos302
