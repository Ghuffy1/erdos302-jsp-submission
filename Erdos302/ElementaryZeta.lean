import Erdos302.PositiveMoment
import Erdos302.SmoothSeries
import Mathlib.Analysis.PSeries

namespace Erdos302

open scoped BigOperators
open Filter Topology

theorem log_two_lower : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.sum_range_le_log_div (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem real_zeta_condensation_bound {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, (n : ℝ) ^ (-s)) ≤ (1 - (2 : ℝ) ^ (1 - s))⁻¹ := by
  have hs0 : 0 < s := by linarith
  have hf : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hr0 : 0 ≤ (2 : ℝ) ^ (1 - s) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ) ^ (1 - s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hmono : ∀ {m n : ℕ}, 0 < m → m ≤ n →
      (n : ℝ) ^ (-s) ≤ (m : ℝ) ^ (-s) := by
    intro m n hm hmn
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hm)
      (by exact_mod_cast hmn) (by linarith)
  have hterm (k : ℕ) : (2 ^ k : ℕ) • (((2 ^ k : ℕ) : ℝ) ^ (-s)) =
      ((2 : ℝ) ^ (1 - s)) ^ k := by
    simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2), ← mul_pow]
    congr 1
    calc
      2 * (2 : ℝ) ^ (-s) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-s) := by simp
      _ = (2 : ℝ) ^ (1 + -s) := (Real.rpow_add (by norm_num) _ _).symm
      _ = (2 : ℝ) ^ (1 - s) := by congr 1
  have hpartial (N : ℕ) : (∑ n ∈ Finset.range N, (n : ℝ) ^ (-s)) ≤
      (1 - (2 : ℝ) ^ (1 - s))⁻¹ := by
    calc
      (∑ n ∈ Finset.range N, (n : ℝ) ^ (-s)) ≤
          ∑ n ∈ Finset.range (2 ^ N), (n : ℝ) ^ (-s) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.lt_two_pow_self.le))
        intro n hn hnot
        exact Real.rpow_nonneg (Nat.cast_nonneg n) _
      _ ≤ (0 : ℝ) ^ (-s) +
          ∑ k ∈ Finset.range N, (2 ^ k : ℕ) • (((2 ^ k : ℕ) : ℝ) ^ (-s)) :=
        by simpa only [Nat.cast_zero] using
          Finset.le_sum_condensed (f := fun n : ℕ => (n : ℝ) ^ (-s)) (@hmono) N
      _ = ∑ k ∈ Finset.range N, ((2 : ℝ) ^ (1 - s)) ^ k := by
        simp only [Real.zero_rpow (neg_ne_zero.mpr hs0.ne'), zero_add, hterm]
      _ ≤ (1 - (2 : ℝ) ^ (1 - s))⁻¹ := geometric_sum_le hr0 hr1 N
  exact le_of_tendsto hf.hasSum.tendsto_sum_nat (Filter.Eventually.of_forall hpartial)

theorem real_zeta_bound {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, (n : ℝ) ^ (-s)) ≤ 1 + 2 / (s - 1) := by
  let t : ℝ := (s - 1) * Real.log 2
  have ht : 0 < t := mul_pos (by linarith) (by linarith [log_two_lower])
  have hpow : (2 : ℝ) ^ (1 - s) = (Real.exp t)⁻¹ := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_neg]
    congr 1
    dsimp [t]
    ring
  have he : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hden : 0 < 1 - (Real.exp t)⁻¹ := by
    have h1 : 1 < Real.exp t := (Real.one_lt_exp_iff).mpr ht
    have hi := inv_lt_one_of_one_lt₀ h1
    linarith
  have hcomp : (1 - (Real.exp t)⁻¹)⁻¹ ≤ 1 + t⁻¹ := by
    have hepos := Real.exp_pos t
    have he1 : 0 < Real.exp t - 1 := by linarith
    calc
      (1 - (Real.exp t)⁻¹)⁻¹ = Real.exp t / (Real.exp t - 1) := by field_simp
      _ ≤ (t + 1) / t := by
        apply (div_le_div_iff₀ he1 ht).mpr
        nlinarith
      _ = 1 + t⁻¹ := by field_simp
  have htcomp : t⁻¹ ≤ 2 / (s - 1) := by
    rw [← one_div]
    apply (div_le_div_iff₀ ht (by linarith)).mpr
    dsimp [t]
    nlinarith [log_two_lower]
  calc
    (∑' n : ℕ, (n : ℝ) ^ (-s)) ≤ (1 - (2 : ℝ) ^ (1 - s))⁻¹ :=
      real_zeta_condensation_bound hs
    _ = (1 - (Real.exp t)⁻¹)⁻¹ := by rw [hpow]
    _ ≤ 1 + t⁻¹ := hcomp
    _ ≤ 1 + 2 / (s - 1) := add_le_add le_rfl htcomp

noncomputable def powerHom (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    simpa only [Nat.cast_mul] using (Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n) :
      ((m : ℝ) * n) ^ (-s) = (m : ℝ) ^ (-s) * (n : ℝ) ^ (-s))

theorem powerHom_prime_norm_lt_one {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : p.Prime) :
    ‖powerHom s p‖ < 1 := by
  change ‖(p : ℝ) ^ (-s)‖ < 1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

theorem smooth_power_hasSum {s : ℝ} (hs : 0 < s) (P : Finset ℕ) :
    HasSum (fun n : Nat.factoredNumbers P => ((n : ℕ) : ℝ) ^ (-s))
      (∏ p ∈ P with p.Prime, (1 - (p : ℝ) ^ (-s))⁻¹) := by
  exact (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := powerHom s) (fun hp => powerHom_prime_norm_lt_one hs hp) P).2

theorem finite_euler_power_bound {s : ℝ} (hs : 1 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, (1 - (p : ℝ) ^ (-s))⁻¹) ≤ 1 + 2 / (s - 1) := by
  have hfilter : P.filter Nat.Prime = P := Finset.filter_eq_self.mpr hP
  have he := smooth_power_hasSum (by linarith : 0 < s) P
  rw [hfilter] at he
  rw [← he.tsum_eq]
  exact (Summable.tsum_subtype_le (fun n : ℕ => (n : ℝ) ^ (-s))
    (Nat.factoredNumbers P) (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (Real.summable_nat_rpow.mpr (by linarith))).trans (real_zeta_bound hs)

end Erdos302
