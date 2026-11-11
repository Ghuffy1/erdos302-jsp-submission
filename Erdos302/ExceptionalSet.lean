import Erdos302.RegularityBlocks

namespace Erdos302

theorem inverse_one_sub_exp_neg_le {t : ℝ} (ht : 0 < t) :
    (1 - Real.exp (-t))⁻¹ ≤ 1 + t⁻¹ := by
  have he := Real.add_one_le_exp t
  have he1 : 0 < Real.exp t - 1 := by
    have h := Real.one_lt_exp_iff.mpr ht
    linarith
  rw [Real.exp_neg]
  calc
    (1 - (Real.exp t)⁻¹)⁻¹ = Real.exp t / (Real.exp t - 1) := by field_simp
    _ ≤ (t + 1) / t := by
      apply (div_le_div_iff₀ he1 ht).mpr
      nlinarith
    _ = 1 + t⁻¹ := by field_simp

theorem regularity_geometric_coefficient :
    8 * Real.exp (Parameters.z - 1) * (1 - Real.exp (-regularityGap))⁻¹ ≤ 500000 := by
  have hz : 0 < 1 - (Parameters.z - 1) := by norm_num [Parameters.z]
  have he0 := Real.add_one_le_exp (-(Parameters.z - 1))
  have he : Real.exp (Parameters.z - 1) ≤ 500 / 439 := by
    calc
      Real.exp (Parameters.z - 1) = (Real.exp (-(Parameters.z - 1)))⁻¹ := by
        rw [Real.exp_neg, inv_inv]
      _ ≤ (1 - (Parameters.z - 1))⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hz (by linarith)
      _ = 500 / 439 := by norm_num [Parameters.z]
  have hg : (1 / 52000 : ℝ) ≤ regularityGap := Parameters.chernoff_gap.le
  have hi : regularityGap⁻¹ ≤ 52000 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 52000) hg
    norm_num [one_div] at h
    exact h
  have hs : (1 - Real.exp (-regularityGap))⁻¹ ≤ 52001 :=
    (inverse_one_sub_exp_neg_le regularityGap_pos).trans (by linarith)
  have hnonneg : 0 ≤ (1 - Real.exp (-regularityGap))⁻¹ := by
    apply inv_nonneg.mpr
    have h := Real.exp_lt_one_iff.mpr (neg_neg_of_pos regularityGap_pos)
    linarith
  calc
    8 * Real.exp (Parameters.z - 1) * (1 - Real.exp (-regularityGap))⁻¹ ≤
        8 * (500 / 439) * (52001 : ℝ) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left he (by norm_num)
      · exact hs
      · exact hnonneg
      · norm_num
    _ ≤ 500000 := by norm_num

noncomputable def irregularVertices (N K : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun n => ¬ KRegular K n)

theorem irregular_card_bound (N K : ℕ) :
    ((irregularVertices N K).card : ℝ) ≤
      500000 * Parameters.z ^ (-(K : ℝ)) * N := by
  classical
  unfold irregularVertices
  let B := (Finset.Icc 1 N).filter (fun n => ¬ KRegular K n)
  have hcover : ∀ n : B, ∃ j : ℕ, (n : ℕ) ∈ regularityBlock N K j := by
    intro n
    obtain ⟨hnI, hnBad⟩ := Finset.mem_filter.mp n.property
    obtain ⟨j, hj⟩ := irregular_has_block K n hnBad
    refine ⟨j, ?_⟩
    exact Finset.mem_filter.mpr ⟨hnI, hj⟩
  choose f hf using hcover
  let J := B.attach.sup f + 1
  have hsub : B ⊆ (Finset.range J).biUnion (regularityBlock N K) := by
    intro n hn
    have hj : f ⟨n, hn⟩ < J := Nat.lt_succ_of_le (Finset.le_sup (f := f) (Finset.mem_attach _ _))
    exact Finset.mem_biUnion.mpr ⟨f ⟨n, hn⟩, Finset.mem_range.mpr hj, hf ⟨n, hn⟩⟩
  have hcard : (B.card : ℝ) ≤
      ∑ j ∈ Finset.range J, ((regularityBlock N K j).card : ℝ) := by
    have h := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    exact_mod_cast h
  let D := 8 * Real.exp (Parameters.z - 1) * Parameters.z ^ (-(K : ℝ)) * N
  have hz : 0 < Parameters.z := by norm_num [Parameters.z]
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hr0 : 0 ≤ Real.exp (-regularityGap) := (Real.exp_pos _).le
  have hr1 : Real.exp (-regularityGap) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos regularityGap_pos)
  calc
    (B.card : ℝ) ≤ ∑ j ∈ Finset.range J, ((regularityBlock N K j).card : ℝ) := hcard
    _ ≤ ∑ j ∈ Finset.range J, D * (Real.exp (-regularityGap)) ^ j :=
      Finset.sum_le_sum (fun j hj => regularityBlock_card_bound N K j)
    _ = D * ∑ j ∈ Finset.range J, (Real.exp (-regularityGap)) ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ D * (1 - Real.exp (-regularityGap))⁻¹ :=
      mul_le_mul_of_nonneg_left (geometric_sum_le hr0 hr1 J) hD
    _ = (8 * Real.exp (Parameters.z - 1) * (1 - Real.exp (-regularityGap))⁻¹) *
        Parameters.z ^ (-(K : ℝ)) * N := by dsimp [D]; ring
    _ ≤ 500000 * Parameters.z ^ (-(K : ℝ)) * N := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
      exact mul_le_mul_of_nonneg_right regularity_geometric_coefficient (by positivity)

end Erdos302
