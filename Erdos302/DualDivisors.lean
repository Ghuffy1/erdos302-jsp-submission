import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic

namespace Erdos302

open scoped ArithmeticFunction.Moebius

theorem sum_upper_divisors {P l : ℕ} (hP : P ≠ 0) (hl : l ∣ P) (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then f d else 0) =
      ∑ e ∈ (P / l).divisors, f (P / e) := by
  calc
    (∑ d ∈ P.divisors, if l ∣ d then f d else 0) =
        ∑ e ∈ P.divisors, if l ∣ P / e then f (P / e) else 0 :=
      (Nat.sum_div_divisors P (fun d => if l ∣ d then f d else 0)).symm
    _ = ∑ e ∈ P.divisors, if e ∣ P / l then f (P / e) else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      have heP := Nat.dvd_of_mem_divisors he
      have hiff : l ∣ P / e ↔ e ∣ P / l := by
        rw [Nat.dvd_div_iff_mul_dvd heP, Nat.dvd_div_iff_mul_dvd hl]
        rw [mul_comm e l]
      simp only [hiff]
    _ = ∑ e ∈ (P / l).divisors, f (P / e) := by
      rw [← Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP (Nat.div_dvd_of_dvd hl)]

noncomputable def upperMoebiusTransform (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ x ∈ (P / d).divisorsAntidiagonal, (μ x.1 : ℝ) * y (P / x.2)

theorem upperMoebiusTransform_inverse {P l : ℕ} (hP : P ≠ 0) (hl : l ∣ P)
    (y : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then upperMoebiusTransform P y d else 0) = y l := by
  let f := fun n : ℕ => ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ) * y (P / x.2)
  have hinv : ∀ n > 0, (∑ e ∈ n.divisors, f e) = y (P / n) :=
    ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr (fun n hn => rfl)
  rw [sum_upper_divisors hP hl]
  have hsum : (∑ e ∈ (P / l).divisors, upperMoebiusTransform P y (P / e)) =
      ∑ e ∈ (P / l).divisors, f e := by
    apply Finset.sum_congr rfl
    intro e he
    have heP : e ∣ P := (Nat.dvd_of_mem_divisors he).trans (Nat.div_dvd_of_dvd hl)
    simp only [upperMoebiusTransform, Nat.div_div_self heP hP, f]
  rw [hsum, hinv]
  · rw [Nat.div_div_self hl hP]
  · exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl)
      (Nat.pos_of_dvd_of_pos hl (Nat.pos_of_ne_zero hP))

theorem upperMoebiusTransform_abs_bound {P d : ℕ} (hP : P ≠ 0) (hd : d ∣ P)
    (y : ℕ → ℝ) :
    |upperMoebiusTransform P y d| ≤ ∑ m ∈ P.divisors, |y m| := by
  unfold upperMoebiusTransform
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℝ) * y (P / b))]
  calc
    |∑ e ∈ (P / d).divisors, (μ ((P / d) / e) : ℝ) * y (P / e)| ≤
        ∑ e ∈ (P / d).divisors, |(μ ((P / d) / e) : ℝ) * y (P / e)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ (P / d).divisors, |y (P / e)| := by
      apply Finset.sum_le_sum
      intro e he
      rw [abs_mul]
      have hmu : |(μ ((P / d) / e) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := (P / d) / e))
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmu (abs_nonneg (y (P / e)))
    _ ≤ ∑ e ∈ P.divisors, |y (P / e)| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hP (Nat.div_dvd_of_dvd hd))
        (fun e he hnot => abs_nonneg _)
    _ = ∑ m ∈ P.divisors, |y m| := Nat.sum_div_divisors P (fun m => |y m|)

end Erdos302
