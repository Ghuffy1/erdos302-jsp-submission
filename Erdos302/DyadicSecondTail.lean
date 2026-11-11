import Erdos302.DyadicTails

namespace Erdos302

theorem dyadic_low_tail (S : Finset ℕ) {U h : ℝ}
    (hU : 1 ≤ U) (hh : (1 / 2 : ℝ) ≤ h)
    (hS : ∀ j ∈ S, 1 ≤ j ∧ (j : ℝ) * h ≤ U / 4) :
    (∑ j ∈ S, (((j : ℝ) + 1) * h) ^ Parameters.H *
      (U + (1 - 2 * (j : ℝ)) * h) ^ (Parameters.gamma - 1)) ≤
      8 * U ^ (Parameters.H + Parameters.gamma) := by
  have hU0 : 0 < U := by linarith
  have hHlo := Parameters.summation_exponents.1
  have hH0 := Parameters.summation_exponents.2.1
  have hH1 : 0 < Parameters.H + 1 := by linarith
  have hg0 : 0 < Parameters.gamma := by norm_num [Parameters.gamma]
  have hge : -1 ≤ Parameters.gamma - 1 := by linarith
  have hge0 : Parameters.gamma - 1 ≤ 0 := by norm_num [Parameters.gamma]
  have hsub : S ⊆ Finset.range ⌊U⌋₊ := by
    intro j hj
    obtain ⟨hj1, hjU⟩ := hS j hj
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hU2 : 2 ≤ U := by nlinarith
    have hjhalf : (j : ℝ) ≤ U / 2 := by nlinarith
    have hjle : ((j + 1 : ℕ) : ℝ) ≤ U := by push_cast; linarith
    have hjfloor : j + 1 ≤ ⌊U⌋₊ := Nat.le_floor hjle
    exact Finset.mem_range.mpr (by omega)
  have hsum : (∑ j ∈ S, (((j + 1 : ℕ) : ℝ) ^ Parameters.H)) ≤
      2 * U ^ (Parameters.H + 1) := by
    have h0 := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ Parameters.H) hsub
      (fun j hj hn => Real.rpow_nonneg (Nat.cast_nonneg (j + 1)) Parameters.H)
    have h1 := sum_shifted_rpow_le ⌊U⌋₊ (show -1 < Parameters.H by linarith) hH0.le
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg ⌊U⌋₊) (Nat.floor_le hU0.le) hH1.le
    have hpow0 : 0 ≤ U ^ (Parameters.H + 1) := Real.rpow_nonneg hU0.le _
    have hdiv : (⌊U⌋₊ : ℝ) ^ (Parameters.H + 1) / (Parameters.H + 1) ≤
        2 * U ^ (Parameters.H + 1) := by
      apply (div_le_iff₀ hH1).mpr
      nlinarith [mul_nonneg hpow0 (show 0 ≤ 2 * (Parameters.H + 1) - 1 by linarith)]
    exact h0.trans (h1.trans hdiv)
  have hterm (j : ℕ) (hj : j ∈ S) :
      (((j : ℝ) + 1) * h) ^ Parameters.H *
        (U + (1 - 2 * (j : ℝ)) * h) ^ (Parameters.gamma - 1) ≤
      (4 * U ^ (Parameters.gamma - 1)) * (((j + 1 : ℕ) : ℝ) ^ Parameters.H) := by
    obtain ⟨hj1, hjU⟩ := hS j hj
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hR : 0 < ((j : ℝ) + 1) * h := by positivity
    have hD : 0 < U + (1 - 2 * (j : ℝ)) * h := by nlinarith
    have hRp := negative_rpow_scale hR
      (by positivity : (0 : ℝ) < (j + 1 : ℕ)) (by norm_num : (1 : ℝ) ≤ 2)
      (show ((j + 1 : ℕ) : ℝ) ≤ 2 * (((j : ℝ) + 1) * h) by push_cast; nlinarith)
      (show -1 ≤ Parameters.H by linarith) hH0.le
    have hDp := negative_rpow_scale hD hU0 (by norm_num : (1 : ℝ) ≤ 2)
      (show U ≤ 2 * (U + (1 - 2 * (j : ℝ)) * h) by nlinarith) hge hge0
    have hm := mul_le_mul hRp hDp (by positivity) (by positivity)
    nlinarith
  have hjoin : U ^ (Parameters.gamma - 1) * U ^ (Parameters.H + 1) =
      U ^ (Parameters.H + Parameters.gamma) := by
    rw [← Real.rpow_add hU0]
    congr 1
    ring
  calc
    (∑ j ∈ S, (((j : ℝ) + 1) * h) ^ Parameters.H *
        (U + (1 - 2 * (j : ℝ)) * h) ^ (Parameters.gamma - 1)) ≤
        ∑ j ∈ S, (4 * U ^ (Parameters.gamma - 1)) * (((j + 1 : ℕ) : ℝ) ^ Parameters.H) :=
      Finset.sum_le_sum hterm
    _ = (4 * U ^ (Parameters.gamma - 1)) *
        ∑ j ∈ S, (((j + 1 : ℕ) : ℝ) ^ Parameters.H) := by rw [Finset.mul_sum]
    _ ≤ (4 * U ^ (Parameters.gamma - 1)) * (2 * U ^ (Parameters.H + 1)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 8 * U ^ (Parameters.H + Parameters.gamma) := by nlinarith [hjoin]

theorem dyadic_high_tail (S : Finset ℕ) {U h : ℝ}
    (hU : 1 ≤ U) (hh : (1 / 2 : ℝ) ≤ h)
    (hS : ∀ j ∈ S, 1 ≤ j ∧ 2 * (j : ℝ) * h ≤ U ∧ U / 4 < (j : ℝ) * h) :
    (∑ j ∈ S, (((j : ℝ) + 1) * h) ^ Parameters.H *
      (U + (1 - 2 * (j : ℝ)) * h) ^ (Parameters.gamma - 1)) ≤
      32 * U ^ (Parameters.H + Parameters.gamma) := by
  classical
  have hU0 : 0 < U := by linarith
  have hh0 : 0 < h := by linarith
  have hHlo := Parameters.summation_exponents.1
  have hH0 := Parameters.summation_exponents.2.1
  have hg0 : 0 < Parameters.gamma := by norm_num [Parameters.gamma]
  have hge : -1 ≤ Parameters.gamma - 1 := by linarith
  have hge0 : Parameters.gamma - 1 ≤ 0 := by norm_num [Parameters.gamma]
  let B := ⌊U / (2 * h)⌋₊
  have hB0 : 0 ≤ U / (2 * h) := by positivity
  have hBU : (B : ℝ) ≤ U := by
    refine (Nat.floor_le hB0).trans ?_
    apply (div_le_iff₀ (by positivity : 0 < 2 * h)).mpr
    nlinarith
  have hUB : 2 * (B : ℝ) * h ≤ U := by
    have hb := (le_div_iff₀ (by positivity : 0 < 2 * h)).mp (Nat.floor_le hB0)
    dsimp [B]
    nlinarith
  have hjB (j : ℕ) (hj : j ∈ S) : j ≤ B := by
    apply Nat.le_floor
    apply (le_div_iff₀ (by positivity : 0 < 2 * h)).mpr
    nlinarith [(hS j hj).2.1]
  have hm (j : ℕ) (hj : j ∈ S) : 1 ≤ B - j + 1 ∧ B - j + 1 ≤ B := by
    have hb := hjB j hj
    have h1 := (hS j hj).1
    omega
  have hreflect : (∑ j ∈ S, ((B - j + 1 : ℕ) : ℝ) ^ (Parameters.gamma - 1)) ≤
      4 * U ^ Parameters.gamma := by
    have hinj : Set.InjOn (fun j : ℕ => B - j + 1) S := by
      intro a ha b hb hab
      change B - a + 1 = B - b + 1 at hab
      have haB := hjB a ha
      have hbB := hjB b hb
      omega
    have hsub : S.image (fun j => B - j + 1) ⊆ Finset.Icc 1 B := by
      intro n hn
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_Icc.mpr (hm j hj)
    have hsum : (∑ j ∈ S, ((B - j + 1 : ℕ) : ℝ) ^ (Parameters.gamma - 1)) ≤
        ∑ n ∈ Finset.Icc 1 B, (n : ℝ) ^ (Parameters.gamma - 1) := by
      rw [← Finset.sum_image (f := fun n : ℕ => (n : ℝ) ^ (Parameters.gamma - 1)) hinj]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn hnot => by positivity)
    have hi := sum_Icc_rpow_le B (show -1 < Parameters.gamma - 1 by linarith) hge0
    have hpow : (B : ℝ) ^ Parameters.gamma ≤ U ^ Parameters.gamma :=
      Real.rpow_le_rpow (Nat.cast_nonneg B) hBU hg0.le
    have hdiv : (B : ℝ) ^ Parameters.gamma / Parameters.gamma ≤ 4 * U ^ Parameters.gamma := by
      apply (div_le_iff₀ hg0).mpr
      have hc : 1 ≤ 4 * Parameters.gamma := by norm_num [Parameters.gamma]
      nlinarith [mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hU0.le Parameters.gamma)]
    have heq : Parameters.gamma - 1 + 1 = Parameters.gamma := by ring
    rw [heq] at hi
    exact hsum.trans (hi.trans hdiv)
  have hterm (j : ℕ) (hj : j ∈ S) :
      (((j : ℝ) + 1) * h) ^ Parameters.H *
        (U + (1 - 2 * (j : ℝ)) * h) ^ (Parameters.gamma - 1) ≤
      (8 * U ^ Parameters.H) * ((B - j + 1 : ℕ) : ℝ) ^ (Parameters.gamma - 1) := by
    obtain ⟨hj1, hjU, hjhi⟩ := hS j hj
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hjBR : (j : ℝ) ≤ B := by exact_mod_cast hjB j hj
    have hR : 0 < ((j : ℝ) + 1) * h := by positivity
    have hD : 0 < U + (1 - 2 * (j : ℝ)) * h := by nlinarith
    have hm0 : (0 : ℝ) < (B - j + 1 : ℕ) := by exact_mod_cast (hm j hj).1
    have hmR : ((B - j + 1 : ℕ) : ℝ) = (B : ℝ) - j + 1 := by
      rw [Nat.cast_add, Nat.cast_sub (hjB j hj), Nat.cast_one]
    have hmD : ((B - j + 1 : ℕ) : ℝ) ≤ 2 * (U + (1 - 2 * (j : ℝ)) * h) := by
      have hDlower : ((B - j + 1 : ℕ) : ℝ) * h ≤ U + (1 - 2 * (j : ℝ)) * h := by
        rw [hmR]
        nlinarith [mul_nonneg (show 0 ≤ (B : ℝ) - j by linarith) hh0.le]
      nlinarith
    have hRp := negative_rpow_scale hR hU0 (by norm_num : (1 : ℝ) ≤ 4)
      (show U ≤ 4 * (((j : ℝ) + 1) * h) by nlinarith)
      (show -1 ≤ Parameters.H by linarith) hH0.le
    have hDp := negative_rpow_scale hD hm0 (by norm_num : (1 : ℝ) ≤ 2) hmD hge hge0
    have hp := mul_le_mul hRp hDp (by positivity) (by positivity)
    nlinarith
  have hjoin : U ^ Parameters.H * U ^ Parameters.gamma = U ^ (Parameters.H + Parameters.gamma) := by
    rw [← Real.rpow_add hU0]
  calc
    (∑ j ∈ S, (((j : ℝ) + 1) * h) ^ Parameters.H *
        (U + (1 - 2 * (j : ℝ)) * h) ^ (Parameters.gamma - 1)) ≤
        ∑ j ∈ S, (8 * U ^ Parameters.H) * ((B - j + 1 : ℕ) : ℝ) ^ (Parameters.gamma - 1) :=
      Finset.sum_le_sum hterm
    _ = (8 * U ^ Parameters.H) *
        ∑ j ∈ S, ((B - j + 1 : ℕ) : ℝ) ^ (Parameters.gamma - 1) := by rw [Finset.mul_sum]
    _ ≤ (8 * U ^ Parameters.H) * (4 * U ^ Parameters.gamma) :=
      mul_le_mul_of_nonneg_left hreflect (by positivity)
    _ = 32 * U ^ (Parameters.H + Parameters.gamma) := by nlinarith [hjoin]

theorem dyadic_second_tail (S : Finset ℕ) {U h : ℝ}
    (hU : 1 ≤ U) (hh : (1 / 2 : ℝ) ≤ h)
    (hS : ∀ j ∈ S, 1 ≤ j ∧ 2 * (j : ℝ) * h ≤ U) :
    (∑ j ∈ S, (((j : ℝ) + 1) * h) ^ Parameters.H *
      (U + (1 - 2 * (j : ℝ)) * h) ^ (Parameters.gamma - 1)) ≤
      64 * U ^ (-Parameters.kappa) := by
  classical
  have hlo := dyadic_low_tail (S.filter (fun j => (j : ℝ) * h ≤ U / 4)) hU hh (by
    intro j hj
    obtain ⟨hjS, hjlo⟩ := Finset.mem_filter.mp hj
    exact ⟨(hS j hjS).1, hjlo⟩)
  have hhi := dyadic_high_tail (S.filter (fun j => ¬ (j : ℝ) * h ≤ U / 4)) hU hh (by
    intro j hj
    obtain ⟨hjS, hjhi⟩ := Finset.mem_filter.mp hj
    exact ⟨(hS j hjS).1, (hS j hjS).2, lt_of_not_ge hjhi⟩)
  have hp := Real.rpow_le_rpow_of_exponent_le hU Parameters.summation_exponents.2.2.le
  have hp0 : 0 ≤ U ^ (-Parameters.kappa) := Real.rpow_nonneg (by linarith) _
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun j => (j : ℝ) * h ≤ U / 4)
    (fun j => (((j : ℝ) + 1) * h) ^ Parameters.H *
      (U + (1 - 2 * (j : ℝ)) * h) ^ (Parameters.gamma - 1))
  linarith

end Erdos302
