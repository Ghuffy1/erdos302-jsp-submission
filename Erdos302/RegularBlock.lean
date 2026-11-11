import Erdos302.RegularTripleWeight

namespace Erdos302

noncomputable def regularParameterBox (N K X : ℕ) : Finset (ℕ × ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 ⌊(N : ℝ) / (X : ℝ) ^ 2⌋₊) ×ˢ integerBox (2 * X)).filter
    (fun t => X ≤ t.2.2 ∧ KRegular K (t.1 * t.2.1 * t.2.2) ∧
      KRegular K (t.1 * t.2.1 * (t.2.1 + t.2.2)) ∧
      KRegular K (t.1 * t.2.2 * (t.2.1 + t.2.2)))

theorem mem_regularParameterBox {N K X g u v : ℕ} :
    (g, u, v) ∈ regularParameterBox N K X ↔
      (1 ≤ g ∧ g ≤ ⌊(N : ℝ) / (X : ℝ) ^ 2⌋₊) ∧
      (1 ≤ u ∧ u ≤ 2 * X) ∧ (1 ≤ v ∧ v ≤ 2 * X) ∧ X ≤ v ∧
      KRegular K (g * u * v) ∧ KRegular K (g * u * (u + v)) ∧
      KRegular K (g * v * (u + v)) := by
  classical
  simp only [regularParameterBox, Finset.mem_filter, Finset.mem_product,
    integerBox, Finset.mem_Icc]
  tauto

theorem regularParameterBox_card_bound (N K X : ℕ) (hX : 2 ≤ X) (hXN : X ^ 2 ≤ N) :
    ((regularParameterBox N K X).card : ℝ) ≤
      72 * 10 ^ 19 * Parameters.q ^ (3 * K) * N *
        ((Real.log (2 * (X : ℝ))) ^ (Parameters.H + Parameters.gamma - 1) +
          (Real.log (2 * (X : ℝ))) ^ Parameters.H *
            (Real.log (2 * ((N : ℝ) / (X : ℝ) ^ 2))) ^ (Parameters.gamma - 1)) := by
  classical
  let Y : ℝ := (N : ℝ) / (X : ℝ) ^ 2
  let R : ℝ := Real.log (2 * (X : ℝ))
  let S : ℝ := Real.log (2 * Y)
  let C : ℝ := 9 * Parameters.q ^ (3 * K) * R ^ Parameters.M
  let G : ℕ → ℝ := fun g => Parameters.gamma ^ smallOmega g X
  let T : ℕ × ℕ → ℝ := fun t =>
    Parameters.theta ^ (totalOmega t.1 + totalOmega t.2 + totalOmega (t.1 + t.2))
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hY : 1 ≤ Y := by
    apply (le_div_iff₀ (sq_pos_of_pos hX0)).mpr
    simpa using (show (X : ℝ) ^ 2 ≤ N by exact_mod_cast hXN)
  have hR : 0 < R := Real.log_pos (by exact_mod_cast (show 1 < 2 * X by omega))
  have hS : 0 < S := Real.log_pos (by linarith : 1 < 2 * Y)
  have hq0 : 0 ≤ Parameters.q := by norm_num [Parameters.q]
  have hg0 : 0 ≤ Parameters.gamma := by norm_num [Parameters.gamma]
  have ht0 : 0 ≤ Parameters.theta := by norm_num [Parameters.theta]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum : ((regularParameterBox N K X).card : ℝ) ≤
      C * (∑ g ∈ Finset.Icc 1 ⌊Y⌋₊, G g) * ∑ t ∈ integerBox (2 * X), T t := by
    calc
      ((regularParameterBox N K X).card : ℝ) =
          ∑ _ ∈ regularParameterBox N K X, (1 : ℝ) := by simp
      _ ≤ ∑ t ∈ regularParameterBox N K X, C * G t.1 * T t.2 := by
        apply Finset.sum_le_sum
        rintro ⟨g, u, v⟩ ht
        obtain ⟨hg, hu, hv, hvX, ha, hb, hc⟩ := mem_regularParameterBox.mp ht
        exact regular_triple_block_weight hX
          (Nat.lt_of_lt_of_le Nat.zero_lt_one hg.1)
          (Nat.lt_of_lt_of_le Nat.zero_lt_one hu.1) hvX hu.2 hv.2 ha hb hc
      _ ≤ ∑ t ∈ (Finset.Icc 1 ⌊Y⌋₊) ×ˢ integerBox (2 * X), C * G t.1 * T t.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro t ht hn
        exact mul_nonneg (mul_nonneg hC (pow_nonneg hg0 _)) (pow_nonneg ht0 _)
      _ = C * (∑ g ∈ Finset.Icc 1 ⌊Y⌋₊, G g) * ∑ t ∈ integerBox (2 * X), T t := by
        rw [Finset.sum_product]
        dsimp only [Prod.fst, Prod.snd]
        rw [← Finset.sum_mul_sum, ← Finset.mul_sum]
  have hG := common_scale_mean_sharp hg0 (by norm_num [Parameters.gamma]) hY X hX
  have hT := theta_weighted_square X hX
  have hG0 : 0 ≤ ∑ g ∈ Finset.Icc 1 ⌊Y⌋₊, G g :=
    Finset.sum_nonneg (fun g hg => pow_nonneg hg0 _)
  have hTb0 : 0 ≤ (20 : ℝ) * 10 ^ 9 * X ^ 2 * R ^ (-Parameters.beta) := by positivity
  have hbound := mul_le_mul hG hT (Finset.sum_nonneg (fun t ht => pow_nonneg ht0 _)) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hbound hC
  have hMH : R ^ Parameters.M * R ^ (-Parameters.beta) = R ^ Parameters.H := by
    rw [← Real.rpow_add hR]
    rfl
  have hE : R ^ Parameters.H * R ^ (Parameters.gamma - 1) =
      R ^ (Parameters.H + Parameters.gamma - 1) := by
    rw [← Real.rpow_add hR]
    congr 1
    ring
  have hcancel : Y * (X : ℝ) ^ 2 = N := by
    dsimp [Y]
    exact div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hX0))
  calc
    ((regularParameterBox N K X).card : ℝ) ≤
        C * ((4 * (10 : ℝ) ^ 9 * Y * (R ^ (Parameters.gamma - 1) + S ^ (Parameters.gamma - 1))) *
          (20 * 10 ^ 9 * X ^ 2 * R ^ (-Parameters.beta))) := hsum.trans (by
            simpa only [C, G, T, R, S, mul_assoc] using hscaled)
    _ = 72 * 10 ^ 19 * Parameters.q ^ (3 * K) * N *
        (R ^ (Parameters.H + Parameters.gamma - 1) + R ^ Parameters.H * S ^ (Parameters.gamma - 1)) := by
      dsimp [C]
      calc
        _ = (72 * 10 ^ 19 * Parameters.q ^ (3 * K)) * (Y * (X : ℝ) ^ 2) *
            ((R ^ Parameters.M * R ^ (-Parameters.beta)) * R ^ (Parameters.gamma - 1) +
              (R ^ Parameters.M * R ^ (-Parameters.beta)) * S ^ (Parameters.gamma - 1)) := by ring
        _ = _ := by rw [hcancel, hMH, hE]

end Erdos302
