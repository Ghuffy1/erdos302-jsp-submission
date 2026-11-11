import Erdos302.RoughCountDensity
import Mathlib.Analysis.Normed.Group.Tannery

namespace Erdos302

open Filter
open scoped Topology

theorem roughCount_le (P : Finset ℕ) (N : ℕ) : roughCount P N ≤ N := by
  classical
  have h := Finset.card_le_card (Finset.filter_subset (IsRough P) (Finset.Icc 1 N))
  simpa [roughCount, roughIndices] using h

theorem natQuotient_tendsto_atTop {n : ℕ} (hn : 0 < n) :
    Tendsto (fun N : ℕ => N / n) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro k
  apply Filter.eventually_atTop.mpr
  refine ⟨k * n, ?_⟩
  intro N hN
  exact (Nat.le_div_iff_mul_le hn).mpr hN

theorem roughCount_quotient_ratio_tendsto (P : Finset ℕ) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun N : ℕ => (roughCount P (N / n) : ℝ) / N)
      atTop (𝓝 (primeDensity P / n)) := by
  have hC := (roughCount_ratio_tendsto P).comp (natQuotient_tendsto_atTop hn)
  have hQ := natQuotient_ratio_tendsto hn
  have h := hC.mul hQ
  dsimp only [Function.comp_def] at h
  have heq : (fun N : ℕ => ((roughCount P (N / n) : ℝ) / (N / n : ℕ)) *
      (((N / n : ℕ) : ℝ) / N)) = (fun N : ℕ => (roughCount P (N / n) : ℝ) / N) := by
    funext N
    by_cases hm : N / n = 0
    · simp [hm, roughCount_zero]
    · have hm' : ((N / n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm
      field_simp
  rw [heq] at h
  simpa only [div_eq_mul_inv] using h

noncomputable def densityTerm (P : Finset ℕ) (N n : ℕ) : ℝ :=
  (smoothIncrement P n : ℝ) * (roughCount P (N / n) : ℝ) / N

theorem densityTerm_eq_zero_of_outside {P : Finset ℕ} {N n : ℕ}
    (hn : n ∉ Finset.Icc 1 N) : densityTerm P N n = 0 := by
  by_cases hn0 : n = 0
  · simp [densityTerm, hn0, roughCount_zero]
  · have hNn : N < n := by simp only [Finset.mem_Icc] at hn; omega
    simp [densityTerm, Nat.div_eq_of_lt hNn, roughCount_zero]

theorem densityTerm_support_smooth (P : Finset ℕ) (N : ℕ) :
    Function.support (densityTerm P N) ⊆ Nat.factoredNumbers P := by
  intro n hn
  by_contra hns
  have hz : densityTerm P N n = 0 := by
    simp [densityTerm, smoothIncrement_eq_zero_of_not_smooth hns]
  exact hn hz

theorem relaxed_density_series (V N : ℕ) :
    (relaxedExtremal V N : ℝ) / N =
      ∑' n : Nat.factoredNumbers (primeSet V), densityTerm (primeSet V) N n := by
  rw [tsum_subtype_eq_of_support_subset (densityTerm_support_smooth (primeSet V) N),
    tsum_eq_sum (s := Finset.Icc 1 N) (fun n hn => densityTerm_eq_zero_of_outside hn)]
  simp only [relaxedExtremal_increment_sum, Nat.cast_sum, Nat.cast_mul,
    Finset.sum_div, densityTerm]

theorem densityTerm_bound (P : Finset ℕ) (N : ℕ) (n : Nat.factoredNumbers P) :
    ‖densityTerm P N n‖ ≤ ((n : ℕ) : ℝ)⁻¹ := by
  have hn : 0 < (n : ℕ) := Nat.pos_of_ne_zero n.2.1
  have hnR : (0 : ℝ) < (n : ℕ) := by exact_mod_cast hn
  have hΔ : (smoothIncrement P n : ℝ) ≤ 1 := by exact_mod_cast smoothIncrement_le_one P n
  have hpos : 0 ≤ densityTerm P N n := by unfold densityTerm; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hpos]
  unfold densityTerm
  by_cases hN : N = 0
  · simp [hN]
  · have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hC : (roughCount P (N / n) : ℝ) * (n : ℕ) ≤ N := by
      have hb := Nat.mul_le_mul_right (n : ℕ) (roughCount_le P (N / n))
      have hd := Nat.div_mul_le_self N (n : ℕ)
      exact_mod_cast hb.trans hd
    have hratio : (roughCount P (N / n) : ℝ) / N ≤ ((n : ℕ) : ℝ)⁻¹ := by
      rw [← one_div, div_le_div_iff₀ hNR hnR]
      simpa only [one_mul] using hC
    have hmul := mul_le_mul_of_nonneg_right hΔ
      (div_nonneg (Nat.cast_nonneg (roughCount P (N / n))) (Nat.cast_nonneg N))
    simpa only [one_mul, mul_div_assoc] using hmul.trans (by simpa only [one_mul] using hratio)

theorem relaxed_density_tendsto (V : ℕ) :
    Tendsto (fun N : ℕ => (relaxedExtremal V N : ℝ) / N) atTop (𝓝 (U V)) := by
  let P := primeSet V
  have hpoint (n : Nat.factoredNumbers P) :
      Tendsto (fun N => densityTerm P N n) atTop
        (𝓝 ((smoothIncrement P n : ℝ) * (primeDensity P / (n : ℕ)))) := by
    have h := (roughCount_quotient_ratio_tendsto P (Nat.pos_of_ne_zero n.2.1)).const_mul
      (smoothIncrement P n : ℝ)
    simpa only [densityTerm, mul_div_assoc] using h
  have hsum := tendsto_tsum_of_dominated_convergence (smooth_reciprocal_summable P)
    hpoint (Filter.Eventually.of_forall (fun N n => densityTerm_bound P N n))
  have htarget : (∑' n : Nat.factoredNumbers P,
      (smoothIncrement P n : ℝ) * (primeDensity P / (n : ℕ))) = U V := by
    unfold U smoothUpperValue
    rw [← tsum_mul_left]
    congr 1
    funext n
    dsimp [P]
    ring
  have heq : (fun N => ∑' n : Nat.factoredNumbers P, densityTerm P N n) =
      (fun N : ℕ => (relaxedExtremal V N : ℝ) / N) :=
    funext (fun N => (relaxed_density_series V N).symm)
  rw [heq, htarget] at hsum
  exact hsum

theorem fixedPrimeLimit : FixedPrimeLimitStatement := by
  intro V hV
  exact relaxed_density_tendsto V

end Erdos302
