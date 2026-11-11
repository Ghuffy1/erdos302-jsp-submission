import Erdos302.ElementaryPrimeBounds
import Erdos302.Parameters
import Mathlib.Data.Nat.Factorization.Basic

namespace Erdos302

def smallOmega (n X : ℕ) : ℕ := ∑ p ∈ Finset.range (X + 1), n.factorization p

def totalOmega (n : ℕ) : ℕ := smallOmega n n

theorem smallOmega_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (X : ℕ) :
    smallOmega (a * b) X = smallOmega a X + smallOmega b X := by
  simp [smallOmega, Nat.factorization_mul ha hb, Finset.sum_add_distrib]

theorem smallOmega_eq_totalOmega {n X : ℕ} (hnX : n ≤ X) :
    smallOmega n X = totalOmega n := by
  unfold totalOmega smallOmega
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hnX 1))
  intro p hp hpnot
  have hnp : n < p := by simp only [Finset.mem_range] at hpnot; omega
  exact Nat.factorization_eq_zero_of_lt hnp

theorem totalOmega_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    totalOmega (a * b) = totalOmega a + totalOmega b := by
  have ha' : a ≤ a * b := by nlinarith
  have hb' : b ≤ a * b := by nlinarith
  change smallOmega (a * b) (a * b) = totalOmega a + totalOmega b
  rw [smallOmega_mul ha.ne' hb.ne', smallOmega_eq_totalOmega ha', smallOmega_eq_totalOmega hb']

theorem smallOmega_mono (n : ℕ) : Monotone (smallOmega n) := by
  intro X Y hXY
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hXY 1))
    (fun _ _ _ => Nat.zero_le _)

def KRegular (K n : ℕ) : Prop :=
  ∀ X : ℕ, 2 ≤ X → (smallOmega n X : ℝ) ≤
    Parameters.A * Real.log (Real.log X / Real.log 2) + K

theorem triple_smallOmega {g u v : ℕ} (hg : 0 < g) (hu : 0 < u) (hv : 0 < v) (X : ℕ) :
    smallOmega (g * u * v) X + smallOmega (g * u * (u + v)) X +
      smallOmega (g * v * (u + v)) X =
      3 * smallOmega g X + 2 * (smallOmega u X + smallOmega v X + smallOmega (u + v) X) := by
  have hw : u + v ≠ 0 := by omega
  simp only [smallOmega_mul (Nat.mul_pos hg hu).ne' hv.ne',
    smallOmega_mul (Nat.mul_pos hg hu).ne' hw,
    smallOmega_mul (Nat.mul_pos hg hv).ne' hw,
    smallOmega_mul hg.ne' hu.ne', smallOmega_mul hg.ne' hv.ne']
  omega

end Erdos302
