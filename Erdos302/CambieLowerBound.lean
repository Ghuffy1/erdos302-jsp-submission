import Erdos302.Solution

namespace Erdos302

open Filter
open scoped Topology

/-- Cambie's construction of small odd integers and the upper half interval. -/
def cambieSet (N : ℕ) : Finset ℕ :=
  (Finset.range ((N / 4 + 1) / 2)).image (fun k => 2 * k + 1) ∪ Finset.Ioc (N / 2) N

theorem cambieSet_mem_bounds {N n : ℕ} (hn : n ∈ cambieSet N) :
    1 ≤ n ∧ n ≤ N ∧ ((n % 2 = 1 ∧ 4 * n ≤ N) ∨ N < 2 * n) := by
  rcases Finset.mem_union.mp hn with hs | hl
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hs
    have hk' := Finset.mem_range.mp hk
    omega
  · obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hl
    omega

theorem cambieSet_free (N : ℕ) : NoUnitFractionTriple (cambieSet N) := by
  intro a ha b hb c hc hab hac hbc heq
  obtain ⟨ha1, haN, haCase⟩ := cambieSet_mem_bounds ha
  obtain ⟨hb1, hbN, hbCase⟩ := cambieSet_mem_bounds hb
  obtain ⟨hc1, hcN, hcCase⟩ := cambieSet_mem_bounds hc
  have he := (reciprocalEquation_iff (by omega) (by omega) (by omega)).mp heq
  have haSmall : a % 2 = 1 ∧ 4 * a ≤ N := by
    rcases haCase with hs | hl
    · exact hs
    · have hm1 := Nat.mul_le_mul_right c hbN
      have hm2 := Nat.mul_le_mul_right b hcN
      have hm3 := Nat.mul_lt_mul_of_pos_right hl (show 0 < b + c by omega)
      exfalso
      nlinarith
  rcases hbCase with hs | hl
  · have hm := congrArg (fun n : ℕ => n % 2) he
    rw [Nat.mul_mod b c 2, Nat.mul_mod a (b + c) 2, Nat.add_mod b c 2,
      haSmall.1, hs.1] at hm
    norm_num at hm
    omega
  rcases hcCase with hs | hl'
  · have hm := congrArg (fun n : ℕ => n % 2) he
    rw [Nat.mul_mod b c 2, Nat.mul_mod a (b + c) 2, Nat.add_mod b c 2,
      haSmall.1, hs.1] at hm
    norm_num at hm
    omega
  · have hab' : 2 * a < b := by omega
    have hac' : 2 * a < c := by omega
    have hm1 := Nat.mul_lt_mul_of_pos_right hab' (show 0 < c by omega)
    have hm2 := Nat.mul_lt_mul_of_pos_right hac' (show 0 < b by omega)
    nlinarith

theorem cambieSet_card (N : ℕ) :
    (cambieSet N).card = (N / 4 + 1) / 2 + (N - N / 2) := by
  have hd : Disjoint ((Finset.range ((N / 4 + 1) / 2)).image (fun k => 2 * k + 1))
      (Finset.Ioc (N / 2) N) := by
    apply Finset.disjoint_left.mpr
    intro n hs hl
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hs
    have hk' := Finset.mem_range.mp hk
    have hl' := Finset.mem_Ioc.mp hl
    omega
  rw [cambieSet, Finset.card_union_of_disjoint hd, Finset.card_image_of_injective,
    Finset.card_range, Nat.card_Ioc]
  intro a b hab
  change 2 * a + 1 = 2 * b + 1 at hab
  omega

theorem cambie_lower_finite (N : ℕ) : 5 * N ≤ 8 * extremal N + 8 := by
  have hsub : cambieSet N ⊆ Finset.Icc 1 N := by
    intro n hn
    have h := cambieSet_mem_bounds hn
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩
  have h := card_le_extremal hsub (cambieSet_free N)
  rw [cambieSet_card] at h
  omega

theorem claimedConstant_ge_five_eighths : (5 / 8 : ℝ) ≤ claimedConstant := by
  have hlow : Tendsto (fun N : ℕ => (5 / 8 : ℝ) - 1 / N) atTop (𝓝 (5 / 8 : ℝ)) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (5 / 8 : ℝ)) atTop (𝓝 (5 / 8 : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  apply le_of_tendsto_of_tendsto hlow extremal_density_tendsto
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h := cambie_lower_finite N
  have hr : 5 * (N : ℝ) ≤ 8 * extremal N + 8 := by exact_mod_cast h
  apply (le_div_iff₀ hN0).mpr
  have hc : (1 / (N : ℝ)) * N = 1 := one_div_mul_cancel hN0.ne'
  nlinarith

theorem density_not_one_half (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N)) :
    ¬ Tendsto (fun N : ℕ => (f N : ℝ) / N) atTop (𝓝 (1 / 2 : ℝ)) := by
  intro hhalf
  have heq := tendsto_nhds_unique (densityLimit f hf) hhalf
  have h := claimedConstant_ge_five_eighths
  linarith

end Erdos302
