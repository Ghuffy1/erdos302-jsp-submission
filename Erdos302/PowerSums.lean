import Erdos302.Parameters
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Erdos302

open MeasureTheory Set

theorem sum_shifted_rpow_le (B : ℕ) {e : ℝ} (he : -1 < e) (he0 : e ≤ 0) :
    (∑ j ∈ Finset.range B, ((j + 1 : ℕ) : ℝ) ^ e) ≤ (B : ℝ) ^ (e + 1) / (e + 1) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ e) (Ioc 0 (0 + B)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos hx.1 hxy he0
  have hint : IntegrableOn (fun x : ℝ => x ^ e) (Icc 0 (0 + B)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp
      (intervalIntegral.intervalIntegrable_rpow' he)
  have h := hanti.sum_le_integral_of_integrableOn hint
  rw [integral_rpow (Or.inl he)] at h
  simpa only [zero_add, Real.zero_rpow (show e + 1 ≠ 0 by linarith), sub_zero] using h

theorem sum_shifted_rpow_tail_le (J B : ℕ) (hJ : 0 < J) {k : ℝ} (hk : 0 < k) :
    (∑ j ∈ Finset.Ico J B, ((j + 1 : ℕ) : ℝ) ^ (-1 - k)) ≤
      (J : ℝ) ^ (-k) / k := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-1 - k)) (Icc (J : ℝ) B) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hJR.trans_le hx.1) hxy (by linarith)
  have hint := integrableOn_Ioi_rpow_of_lt (by linarith : -1 - k < -1) hJR
  have h := hanti.sum_Ico_le_integral hint
    (fun x hx => Real.rpow_nonneg (hJR.le.trans hx.le) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -1 - k < -1) hJR] at h
  have hexp : -1 - k + 1 = -k := by ring
  rw [hexp] at h
  simpa only [neg_div_neg_eq] using h

theorem sum_Icc_rpow_le (B : ℕ) {e : ℝ} (he : -1 < e) (he0 : e ≤ 0) :
    (∑ j ∈ Finset.Icc 1 B, (j : ℝ) ^ e) ≤ (B : ℝ) ^ (e + 1) / (e + 1) := by
  have h := sum_shifted_rpow_le B he he0
  have heq : (∑ j ∈ Finset.range B, ((j + 1 : ℕ) : ℝ) ^ e) =
      ∑ j ∈ Finset.Icc 1 B, (j : ℝ) ^ e := by
    apply Finset.sum_bij (fun j _ => j + 1)
    · intro j hj
      simp only [Finset.mem_range] at hj
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a ha b hb hab
      omega
    · intro b hb
      obtain ⟨hb1, hbB⟩ := Finset.mem_Icc.mp hb
      exact ⟨b - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j hj
      rfl
  rwa [heq] at h

end Erdos302
