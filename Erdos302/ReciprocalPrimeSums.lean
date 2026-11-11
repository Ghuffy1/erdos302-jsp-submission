import Erdos302.ElementaryPrimeBounds
import Mathlib.Data.Nat.Prime.Basic

namespace Erdos302

theorem reciprocal_interval_telescope (N : ℕ) :
    (∑ p ∈ Finset.Icc 2 (N + 1), (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹)) =
      1 - ((N + 1 : ℕ) : ℝ)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hc : ((N + 1 + 1 : ℕ) : ℝ) - 1 = ((N + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    change 1 - ((N + 1 : ℕ) : ℝ)⁻¹ +
      ((((N + 1 + 1 : ℕ) : ℝ) - 1)⁻¹ - ((N + 1 + 1 : ℕ) : ℝ)⁻¹) =
      1 - ((N + 1 + 1 : ℕ) : ℝ)⁻¹
    rw [hc]
    ring

theorem reciprocal_square_le_difference {p : ℕ} (hp : 2 ≤ p) :
    (p : ℝ)⁻¹ ^ 2 ≤ ((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹ := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have hd : (p : ℝ) * ((p : ℝ) - 1) ≤ (p : ℝ) ^ 2 := by nlinarith
  calc
    (p : ℝ)⁻¹ ^ 2 = 1 / (p : ℝ) ^ 2 := by simp only [inv_pow, one_div]
    _ ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) :=
      one_div_le_one_div_of_le (mul_pos hp0 hp1) hd
    _ = ((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹ := by field_simp <;> ring

theorem prime_inverse_difference_sum_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹)) ≤ 1 := by
  let M := max 2 (P.sup id)
  have hM2 : 2 ≤ M := le_max_left _ _
  have hPM : P ⊆ Finset.Icc 2 M := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(hP p hp).two_le,
      (Finset.le_sup (f := id) hp).trans (le_max_right _ _)⟩
  have hsum : (∑ p ∈ P, (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹)) ≤
      ∑ p ∈ Finset.Icc 2 M, (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hPM
    intro p hp hnot
    exact (sq_nonneg _).trans (reciprocal_square_le_difference (Finset.mem_Icc.mp hp).1)
  have ht := reciprocal_interval_telescope (M - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ M)] at ht
  rw [ht] at hsum
  exact hsum.trans (sub_le_self 1 (inv_nonneg.mpr (Nat.cast_nonneg M)))

theorem prime_reciprocal_square_sum_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, (p : ℝ)⁻¹ ^ 2) ≤ 1 := by
  apply le_trans (Finset.sum_le_sum (fun p hp => reciprocal_square_le_difference (hP p hp).two_le))
  exact prime_inverse_difference_sum_le_one P hP

end Erdos302
