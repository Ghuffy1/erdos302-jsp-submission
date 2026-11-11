import Erdos302.IncrementIdentity
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecificLimits.Basic

namespace Erdos302

open Filter
open scoped Topology

def primeModulus (P : Finset ℕ) : ℕ := ∏ p ∈ P with p.Prime, p

theorem primeModulus_pos (P : Finset ℕ) : 0 < primeModulus P := by
  exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)

theorem isRough_iff_coprime (P : Finset ℕ) (q : ℕ) :
    IsRough P q ↔ q ≠ 0 ∧ Nat.Coprime (primeModulus P) q := by
  simp only [IsRough, primeModulus, Nat.coprime_prod_left_iff, Finset.mem_filter]
  constructor
  · rintro ⟨hq, hp⟩
    exact ⟨hq, fun p h => h.2.coprime_iff_not_dvd.mpr (hp p h.1 h.2)⟩
  · rintro ⟨hq, hp⟩
    exact ⟨hq, fun p hpP hprime => hprime.coprime_iff_not_dvd.mp (hp p ⟨hpP, hprime⟩)⟩

theorem primeModulus_primeFactors (P : Finset ℕ) :
    (primeModulus P).primeFactors = P.filter Nat.Prime :=
  Nat.primeFactors_prod (fun _ hp => (Finset.mem_filter.mp hp).2)

theorem totient_primeModulus_ratio (P : Finset ℕ) :
    ((primeModulus P).totient : ℝ) / primeModulus P = primeDensity P := by
  have h := Nat.totient_eq_mul_prod_factors (primeModulus P)
  have hc := congrArg (fun x : ℚ => (x : ℝ)) h
  push_cast at hc
  have hreal : ((primeModulus P).totient : ℝ) = (primeModulus P : ℝ) *
      ∏ p ∈ (primeModulus P).primeFactors, (1 - (p : ℝ)⁻¹) := hc
  rw [primeModulus_primeFactors] at hreal
  have hM : (primeModulus P : ℝ) ≠ 0 := by exact_mod_cast (primeModulus_pos P).ne'
  apply (div_eq_iff hM).mpr
  simpa only [primeDensity, mul_comm] using hreal

theorem roughCount_eq_coprime_card (P : Finset ℕ) (N : ℕ) :
    roughCount P N = ((Finset.Ico 1 (N + 1)).filter (Nat.Coprime (primeModulus P))).card := by
  classical
  unfold roughCount
  congr 1
  ext q
  simp only [roughIndices, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico,
    isRough_iff_coprime]
  omega

theorem coprime_card_blocks (M k t : ℕ) :
    ((Finset.Ico t (t + M * k)).filter (Nat.Coprime M)).card = M.totient * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : Finset.Ico t (t + M * (k + 1)) =
        Finset.Ico t (t + M * k) ∪ Finset.Ico (t + M * k) (t + M * k + M) := by
      rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
      congr 1
      ring
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint]
    · rw [ih, Nat.filter_coprime_Ico_eq_totient]
      ring
    · exact (Finset.Ico_disjoint_Ico_consecutive t (t + M * k) (t + M * k + M)).mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem roughCount_bounds (P : Finset ℕ) (N : ℕ) :
    (primeModulus P).totient * (N / primeModulus P) ≤ roughCount P N ∧
      roughCount P N ≤ (primeModulus P).totient * (N / primeModulus P + 1) := by
  rw [roughCount_eq_coprime_card]
  constructor
  · rw [← coprime_card_blocks (primeModulus P) (N / primeModulus P) 1]
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    apply Finset.Ico_subset_Ico le_rfl
    have h := Nat.div_mul_le_self N (primeModulus P)
    nlinarith
  · simpa only [Nat.add_comm] using
      Nat.Ico_filter_coprime_le (a := primeModulus P) 1 N (primeModulus_pos P).ne'

theorem natQuotient_ratio_tendsto {M : ℕ} (hM : 0 < M) :
    Tendsto (fun N : ℕ => ((N / M : ℕ) : ℝ) / N) atTop (𝓝 ((M : ℝ)⁻¹)) := by
  have h : Tendsto (fun N : ℕ => (1 - ((N % M : ℕ) : ℝ) / N) / (M : ℝ))
      atTop (𝓝 ((M : ℝ)⁻¹)) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      (tendsto_mod_div_atTop_nhds_zero_nat hM)).div_const (M : ℝ)
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : ((N % M : ℕ) : ℝ) + (M : ℝ) * (N / M : ℕ) = N := by
    exact_mod_cast Nat.mod_add_div N M
  field_simp
  nlinarith

theorem roughCount_ratio_tendsto (P : Finset ℕ) :
    Tendsto (fun N : ℕ => (roughCount P N : ℝ) / N) atTop (𝓝 (primeDensity P)) := by
  let M := primeModulus P
  have hM : 0 < M := primeModulus_pos P
  have hL := (natQuotient_ratio_tendsto hM).const_mul (M.totient : ℝ)
  have hZ : Tendsto (fun N : ℕ => (M.totient : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hU := hL.add hZ
  have htarget : (M.totient : ℝ) * (M : ℝ)⁻¹ = primeDensity P := by
    simpa only [div_eq_mul_inv] using totient_primeModulus_ratio P
  rw [htarget] at hL
  rw [htarget, add_zero] at hU
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
  · apply Filter.Eventually.of_forall
    intro N
    have h := (roughCount_bounds P N).1
    have hr : (M.totient : ℝ) * (N / M : ℕ) ≤ roughCount P N := by exact_mod_cast h
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hr (Nat.cast_nonneg N)
  · apply Filter.Eventually.of_forall
    intro N
    have h := (roughCount_bounds P N).2
    have hr : (roughCount P N : ℝ) ≤ (M.totient : ℝ) * ((N / M : ℕ) + 1) := by exact_mod_cast h
    have hd := div_le_div_of_nonneg_right hr (Nat.cast_nonneg N)
    simpa only [mul_add, mul_one, add_div, mul_div_assoc] using hd

end Erdos302
