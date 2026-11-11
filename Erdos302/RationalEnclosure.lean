import Erdos302.Solution

namespace Erdos302

open Filter
open scoped Topology

def rationalPrimeDensity (P : Finset ℕ) : ℚ :=
  ∏ p ∈ P with p.Prime, (1 - (p : ℚ)⁻¹)

noncomputable def rationalPartialValue (P : Finset ℕ) (S : Finset (Nat.factoredNumbers P)) : ℚ :=
  rationalPrimeDensity P * ∑ n ∈ S, (smoothIncrement P n : ℚ) / (n : ℕ)

def rationalTail (P : Finset ℕ) (S : Finset (Nat.factoredNumbers P)) : ℚ :=
  1 - rationalPrimeDensity P * ∑ n ∈ S, ((n : ℕ) : ℚ)⁻¹

theorem rationalPrimeDensity_cast (P : Finset ℕ) :
    (rationalPrimeDensity P : ℝ) = primeDensity P := by
  simp [rationalPrimeDensity, primeDensity]

theorem rationalPartialValue_cast (P : Finset ℕ) (S : Finset (Nat.factoredNumbers P)) :
    (rationalPartialValue P S : ℝ) =
      primeDensity P * ∑ n ∈ S, (smoothIncrement P n : ℝ) / (n : ℕ) := by
  simp [rationalPartialValue, rationalPrimeDensity_cast]

theorem rationalTail_cast (P : Finset ℕ) (S : Finset (Nat.factoredNumbers P)) :
    (rationalTail P S : ℝ) =
      1 - primeDensity P * ∑ n ∈ S, ((n : ℕ) : ℝ)⁻¹ := by
  simp [rationalTail, rationalPrimeDensity_cast]

theorem primeDensity_mul_reciprocal_sum (P : Finset ℕ) :
    primeDensity P * ∑' n : Nat.factoredNumbers P, ((n : ℕ) : ℝ)⁻¹ = 1 := by
  rw [(smooth_reciprocal_hasSum P).tsum_eq]
  rw [Finset.prod_inv_distrib]
  change primeDensity P * (primeDensity P)⁻¹ = 1
  exact mul_inv_cancel₀ (primeDensity_pos P).ne'

theorem rational_enclosure_fixed_primes (P : Finset ℕ) (S : Finset (Nat.factoredNumbers P)) :
    (rationalPartialValue P S : ℝ) ≤ smoothUpperValue P ∧
    smoothUpperValue P ≤ (rationalPartialValue P S + rationalTail P S : ℚ) := by
  let w : Nat.factoredNumbers P → ℝ := fun n => (smoothIncrement P n : ℝ) / (n : ℕ)
  let r : Nat.factoredNumbers P → ℝ := fun n => ((n : ℕ) : ℝ)⁻¹
  have hw := smoothUpperValue_series_summable P
  have hr := smooth_reciprocal_summable P
  have hwr (n : Nat.factoredNumbers P) : w n ≤ r n := by
    have h := div_le_div_of_nonneg_right
      (show (smoothIncrement P n : ℝ) ≤ 1 by exact_mod_cast smoothIncrement_le_one P n)
      (Nat.cast_nonneg (n : ℕ))
    simpa only [w, r, one_div] using h
  have hwl := hw.sum_le_tsum S (fun n hn => by positivity)
  have hdiff := (hr.sub hw).sum_le_tsum S (fun n hn => sub_nonneg.mpr (hwr n))
  rw [Summable.tsum_sub hr hw, Finset.sum_sub_distrib] at hdiff
  have hd := primeDensity_pos P
  have htotal := primeDensity_mul_reciprocal_sum P
  constructor
  · rw [rationalPartialValue_cast]
    exact mul_le_mul_of_nonneg_left hwl hd.le
  · push_cast
    rw [rationalPartialValue_cast, rationalTail_cast]
    have hscaled := mul_le_mul_of_nonneg_left hdiff hd.le
    change primeDensity P * ∑' n, w n ≤ _
    change primeDensity P * ∑' n, r n = 1 at htotal
    change primeDensity P * ((∑ n ∈ S, r n) - ∑ n ∈ S, w n) ≤
      primeDensity P * ((∑' n, r n) - ∑' n, w n) at hscaled
    change primeDensity P * ∑' n, w n ≤
      primeDensity P * ∑ n ∈ S, w n + (1 - primeDensity P * ∑ n ∈ S, r n)
    nlinarith

theorem rationalTail_tendsto (P : Finset ℕ) :
    Tendsto (fun S : Finset (Nat.factoredNumbers P) => (rationalTail P S : ℝ)) atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : Finset (Nat.factoredNumbers P) => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have h := hc.sub ((smooth_reciprocal_summable P).hasSum.const_mul (primeDensity P))
  have htotal := primeDensity_mul_reciprocal_sum P
  simpa only [rationalTail_cast, htotal, sub_self] using h

/-- Finite rational enclosures of the density exist at every positive rational width. -/
theorem rational_enclosures (ε : ℚ) (hε : 0 < ε) :
    ∃ (V : ℕ) (S : Finset (Nat.factoredNumbers (primeSet V))), 4 ≤ V ∧
      (rationalPartialValue (primeSet V) S - ε / 2 : ℚ) ≤ claimedConstant ∧
      claimedConstant ≤ (rationalPartialValue (primeSet V) S + rationalTail (primeSet V) S : ℚ) ∧
      (rationalPartialValue (primeSet V) S + rationalTail (primeSet V) S) -
        (rationalPartialValue (primeSet V) S - ε / 2) < ε := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hδ : (0 : ℝ) < 1 / 140 := by norm_num
  have hlim : Tendsto (fun V : ℕ => ((10 : ℝ) ^ 23 + 561000) *
      (Real.log V) ^ (-(1 / 140 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using ((tendsto_rpow_neg_atTop hδ).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul ((10 : ℝ) ^ 23 + 561000)
  obtain ⟨V, hV, hVE⟩ := (eventually_ge_atTop (4 : ℕ) |>.and
    ((tendsto_order.mp hlim).2 ((ε : ℝ) / 2) (by linarith))).exists
  obtain ⟨S, hS⟩ := ((tendsto_order.mp (rationalTail_tendsto (primeSet V))).2
    ((ε : ℝ) / 2) (by linarith)).exists
  change ((10 : ℝ) ^ 23 + 561000) * Real.rpow (Real.log V) (-(1 / 140 : ℝ)) < (ε : ℝ) / 2 at hVE
  have he := effectiveApproximation V hV
  have hp := rational_enclosure_fixed_primes (primeSet V) S
  refine ⟨V, S, hV, ?_, ?_, ?_⟩
  · push_cast
    change (rationalPartialValue (primeSet V) S : ℝ) - (ε : ℝ) / 2 ≤ claimedConstant
    have hp1 : (rationalPartialValue (primeSet V) S : ℝ) ≤ U V := hp.1
    linarith [hp1, he.2]
  · exact (claimedConstant_le_U hV).trans hp.2
  · have hSr : rationalTail (primeSet V) S < ε / 2 := by exact_mod_cast hS
    linarith

end Erdos302
