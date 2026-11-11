import Erdos302.DensitySeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Erdos302

open Filter
open scoped Topology

theorem U_antitone : Antitone U := by
  intro V W hVW
  apply le_of_tendsto_of_tendsto (relaxed_density_tendsto W) (relaxed_density_tendsto V)
  exact Filter.Eventually.of_forall (fun N => div_le_div_of_nonneg_right
    (by exact_mod_cast relaxedExtremal_antitone N hVW) (Nat.cast_nonneg N))

theorem U_tail_bddBelow : BddBelow (Set.range (fun V : ℕ => U (V + 4))) := by
  refine ⟨0, ?_⟩
  rintro x ⟨V, rfl⟩
  exact smoothUpperValue_nonneg (primeSet (V + 4))

theorem U_tail_tendsto :
    Tendsto (fun V : ℕ => U (V + 4)) atTop (𝓝 claimedConstant) := by
  have hanti : Antitone (fun V : ℕ => U (V + 4)) := by
    intro V W hVW
    exact U_antitone (Nat.add_le_add_right hVW 4)
  exact tendsto_atTop_ciInf hanti U_tail_bddBelow

theorem claimedConstant_le_U {V : ℕ} (hV : 4 ≤ V) : claimedConstant ≤ U V := by
  apply csInf_le U_tail_bddBelow
  exact ⟨V - 4, congrArg U (Nat.sub_add_cancel hV)⟩

theorem claimedConstant_nonneg : 0 ≤ claimedConstant := by
  apply le_csInf (Set.range_nonempty _) 
  rintro x ⟨V, rfl⟩
  exact smoothUpperValue_nonneg (primeSet (V + 4))

theorem logarithmic_tail_tendsto :
    Tendsto (fun N : ℕ => Real.rpow (Real.log N) (-(7 / 80 : ℝ))) atTop (𝓝 0) := by
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 80)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem regularity_error_tendsto :
    Tendsto (fun K : ℕ => (500000 : ℝ) * Parameters.z ^ (-(K : ℤ))) atTop (𝓝 0) := by
  have hz0 : 0 ≤ Parameters.z⁻¹ := by norm_num [Parameters.z]
  have hz1 : Parameters.z⁻¹ < 1 := by norm_num [Parameters.z]
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hz0 hz1).const_mul (500000 : ℝ)
  simpa only [zpow_neg, zpow_natCast, inv_pow, mul_zero] using h

theorem uniform_approximation_of_removal (hrem : RemovalEstimateStatement) :
    ∀ ε : ℝ, 0 < ε → ∃ V₀ : ℕ, ∀ V ≥ V₀, ∀ᶠ N : ℕ in atTop,
      |(extremal N : ℝ) / N - (relaxedExtremal V N : ℝ) / N| < ε := by
  intro ε hε
  have he : 0 < ε / 3 := by positivity
  obtain ⟨K, hK⟩ := ((tendsto_order.mp regularity_error_tendsto).2 (ε / 3) he).exists
  let A : ℝ := 10 ^ 23 * Parameters.q ^ (3 * K)
  have htail : Tendsto (fun N : ℕ => A * Real.rpow (Real.log N) (-(7 / 80 : ℝ)))
      atTop (𝓝 0) := by simpa only [mul_zero] using logarithmic_tail_tendsto.const_mul A
  obtain ⟨V₁, hV₁⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp htail).2 (ε / 3) he)
  refine ⟨max 4 V₁, ?_⟩
  intro V hV
  have hV4 : 4 ≤ V := le_trans (le_max_left _ _) hV
  have hVT := hV₁ V (le_trans (le_max_right _ _) hV)
  filter_upwards [eventually_ge_atTop (4 : ℕ),
    (tendsto_order.mp htail).2 (ε / 3) he] with N hN hNT
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hlo, hhi⟩ := hrem N V K hN hV4
  have hd : (relaxedExtremal V N : ℝ) / N - (extremal N : ℝ) / N ≤
      500000 * Parameters.z ^ (-(K : ℤ)) + A *
        (Real.rpow (Real.log V) (-(7 / 80 : ℝ)) +
          Real.rpow (Real.log N) (-(7 / 80 : ℝ))) := by
    rw [← sub_div, div_le_iff₀ hNR]
    simpa only [A, mul_comm] using hhi
  have hnonneg : (extremal N : ℝ) / N ≤ (relaxedExtremal V N : ℝ) / N :=
    div_le_div_of_nonneg_right (by linarith) hNR.le
  rw [abs_of_nonpos (sub_nonpos.mpr hnonneg), neg_sub]
  nlinarith

theorem densityLimit_of_removal (hrem : RemovalEstimateStatement) : DensityLimitStatement := by
  have hconv : Tendsto (fun N : ℕ => (extremal N : ℝ) / N) atTop (𝓝 claimedConstant) := by
    apply tendsto_of_uniform_approximations
      (fun N : ℕ => (extremal N : ℝ) / N)
      (fun V N : ℕ => (relaxedExtremal (V + 4) N : ℝ) / N)
      (fun V : ℕ => U (V + 4)) claimedConstant
      (fun V => relaxed_density_tendsto (V + 4)) U_tail_tendsto
    intro ε hε
    obtain ⟨V₀, hV₀⟩ := uniform_approximation_of_removal hrem ε hε
    exact ⟨V₀, fun V hV => hV₀ (V + 4) (by omega)⟩
  intro f hf
  have heq : f = extremal := funext (fun N => isMax_iff_eq_extremal.mp (hf N))
  simpa only [heq] using hconv

end Erdos302
