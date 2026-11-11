import Erdos302.RegularityMoment

namespace Erdos302

noncomputable def regularityCutoff (j : ℕ) : ℕ :=
  ⌊Real.exp (Real.log 2 * Real.exp ((j : ℝ) + 1))⌋₊

noncomputable def regularityGap : ℝ :=
  Parameters.A * Real.log Parameters.z - Parameters.z + 1

noncomputable def regularityBlock (N K j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun n =>
    Parameters.A * (j : ℝ) + K < (smallOmega n (regularityCutoff j) : ℝ))

theorem regularityGap_pos : 0 < regularityGap := by
  have h := Parameters.chernoff_gap
  dsimp [regularityGap]
  linarith

theorem regularityCutoff_two_le (j : ℕ) : 2 ≤ regularityCutoff j := by
  apply Nat.le_floor
  have hj : 1 ≤ Real.exp ((j : ℝ) + 1) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hlog : Real.log 2 ≤ Real.log 2 * Real.exp ((j : ℝ) + 1) := by
    nlinarith [log_two_lower]
  calc
    (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp (Real.log 2 * Real.exp ((j : ℝ) + 1)) := Real.exp_le_exp.mpr hlog

theorem regularityCutoff_log_le (j : ℕ) :
    Real.log (regularityCutoff j) / Real.log 2 ≤ Real.exp ((j : ℝ) + 1) := by
  have htwo : 0 < Real.log 2 := by linarith [log_two_lower]
  have hc : (0 : ℝ) < regularityCutoff j := by
    exact_mod_cast (show 0 < regularityCutoff j by have := regularityCutoff_two_le j; omega)
  apply (div_le_iff₀ htwo).mpr
  have hf := Nat.floor_le (Real.exp_pos (Real.log 2 * Real.exp ((j : ℝ) + 1))).le
  have hl := Real.log_le_log hc hf
  rw [Real.log_exp] at hl
  simpa only [mul_comm] using hl

theorem irregular_has_block (K n : ℕ) (hn : ¬ KRegular K n) :
    ∃ j : ℕ, Parameters.A * (j : ℝ) + K < (smallOmega n (regularityCutoff j) : ℝ) := by
  unfold KRegular at hn
  push Not at hn
  obtain ⟨X, hX, hbad⟩ := hn
  let L := Real.log (Real.log X / Real.log 2)
  let j := ⌊L⌋₊
  have htwo : 0 < Real.log 2 := by linarith [log_two_lower]
  have hlogX : Real.log 2 ≤ Real.log X :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hX)
  have hratio : 1 ≤ Real.log X / Real.log 2 :=
    (le_div_iff₀ htwo).mpr (by simpa using hlogX)
  have hL : 0 ≤ L := Real.log_nonneg hratio
  have hj : (j : ℝ) ≤ L := Nat.floor_le hL
  have hjnext : L < (j : ℝ) + 1 := Nat.lt_floor_add_one L
  have hratioExp : Real.log X / Real.log 2 < Real.exp ((j : ℝ) + 1) := by
    have h := Real.exp_lt_exp.mpr hjnext
    dsimp [L] at h
    rwa [Real.exp_log (lt_of_lt_of_le zero_lt_one hratio)] at h
  have hXcap : X ≤ regularityCutoff j := by
    apply Nat.le_floor
    apply (Real.log_le_iff_le_exp (by exact_mod_cast (show 0 < X by omega))).mp
    have h := (div_lt_iff₀ htwo).mp hratioExp
    linarith
  have hmono : (smallOmega n X : ℝ) ≤ smallOmega n (regularityCutoff j) := by
    exact_mod_cast smallOmega_mono n hXcap
  refine ⟨j, ?_⟩
  have hA : 0 ≤ Parameters.A := by norm_num [Parameters.A]
  have hAj := mul_le_mul_of_nonneg_left hj hA
  dsimp [L] at hAj
  linarith

theorem regularityBlock_card_bound (N K j : ℕ) :
    ((regularityBlock N K j).card : ℝ) ≤
      8 * Real.exp (Parameters.z - 1) * Parameters.z ^ (-(K : ℝ)) * N *
        (Real.exp (-regularityGap)) ^ j := by
  have hz : 0 < Parameters.z := by norm_num [Parameters.z]
  have hza : 0 ≤ Parameters.z - 1 := by norm_num [Parameters.z]
  have hc : (0 : ℝ) < regularityCutoff j := by
    exact_mod_cast (show 0 < regularityCutoff j by have := regularityCutoff_two_le j; omega)
  have hlogc : 0 ≤ Real.log (regularityCutoff j) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ regularityCutoff j by
      have := regularityCutoff_two_le j; omega))
  have htwo : 0 < Real.log 2 := by linarith [log_two_lower]
  have hpower : (Real.log (regularityCutoff j) / Real.log 2) ^ (Parameters.z - 1) ≤
      Real.exp (((j : ℝ) + 1) * (Parameters.z - 1)) := by
    calc
      (Real.log (regularityCutoff j) / Real.log 2) ^ (Parameters.z - 1) ≤
          (Real.exp ((j : ℝ) + 1)) ^ (Parameters.z - 1) :=
        Real.rpow_le_rpow (div_nonneg hlogc htwo.le) (regularityCutoff_log_le j) hza
      _ = Real.exp (((j : ℝ) + 1) * (Parameters.z - 1)) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have htail := regularity_tail_moment_bound N (regularityCutoff j)
    (regularityCutoff_two_le j) (Parameters.A * (j : ℝ) + K)
  change ((regularityBlock N K j).card : ℝ) *
    Parameters.z ^ (Parameters.A * (j : ℝ) + K) ≤ _ at htail
  have hden : 0 < Parameters.z ^ (Parameters.A * (j : ℝ) + K) := Real.rpow_pos_of_pos hz _
  have hexp : Real.exp (((j : ℝ) + 1) * (Parameters.z - 1)) /
      Parameters.z ^ (Parameters.A * (j : ℝ) + K) =
      Real.exp (Parameters.z - 1) * Parameters.z ^ (-(K : ℝ)) *
        (Real.exp (-regularityGap)) ^ j := by
    rw [Real.rpow_def_of_pos hz, Real.rpow_def_of_pos hz, div_eq_mul_inv,
      ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [regularityGap]
    ring
  calc
    ((regularityBlock N K j).card : ℝ) ≤
        (8 * N * (Real.log (regularityCutoff j) / Real.log 2) ^ (Parameters.z - 1)) /
          Parameters.z ^ (Parameters.A * (j : ℝ) + K) := (le_div_iff₀ hden).mpr htail
    _ ≤ (8 * N * Real.exp (((j : ℝ) + 1) * (Parameters.z - 1))) /
          Parameters.z ^ (Parameters.A * (j : ℝ) + K) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = 8 * Real.exp (Parameters.z - 1) * Parameters.z ^ (-(K : ℝ)) * N *
        (Real.exp (-regularityGap)) ^ j := by
      rw [mul_div_assoc, hexp]
      ring

end Erdos302
