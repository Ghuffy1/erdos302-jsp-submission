import Erdos302.RegularBlock
import Mathlib.Data.Nat.Log

namespace Erdos302

def dyadicParameterIndices (N V : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun j => 1 ≤ j ∧ V < 2 * 2 ^ j ∧ (2 ^ j) ^ 2 ≤ N)

theorem mem_dyadicParameterIndices {N V j : ℕ} :
    j ∈ dyadicParameterIndices N V ↔
      j < N + 1 ∧ 1 ≤ j ∧ V < 2 * 2 ^ j ∧ (2 ^ j) ^ 2 ≤ N := by
  simp only [dyadicParameterIndices, Finset.mem_filter, Finset.mem_range]

theorem largeRegularParameters_dyadic_cover (N V K : ℕ) (hV : 4 ≤ V) :
    largeRegularParameters N V K ⊆
      (dyadicParameterIndices N V).biUnion (fun j => regularParameterBox N K (2 ^ j)) := by
  classical
  rintro ⟨g, u, v⟩ ht
  obtain ⟨hg, hu, hv, huv, hVv, hcop, hcN, ha, hb, hc⟩ := mem_largeRegularParameters.mp ht
  let j := Nat.log 2 v
  let X := 2 ^ j
  have hv0 : 0 < v := by omega
  have hXv : X ≤ v := Nat.pow_log_le_self 2 hv0.ne'
  have hvX : v < 2 * X := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) v
    simpa only [Nat.pow_succ, mul_comm, j, X] using h
  have hj1 : 1 ≤ j := by
    apply Nat.le_log_of_pow_le (by norm_num)
    norm_num
    omega
  have hjN : j < N + 1 := by
    have h := (Nat.log_le_self 2 v).trans hv.2
    omega
  have hX2 : X ^ 2 ≤ v * (u + v) := by nlinarith
  have hgX2 : g * X ^ 2 ≤ N :=
    (Nat.mul_le_mul_left g hX2).trans (by simpa only [mul_assoc] using hcN)
  have hXN : X ^ 2 ≤ N :=
    (Nat.le_mul_of_pos_left _ (by omega : 0 < g)).trans hgX2
  have hgi : g ≤ ⌊(N : ℝ) / (X : ℝ) ^ 2⌋₊ := by
    apply Nat.le_floor
    have hX0 : (0 : ℝ) < X := by positivity
    apply (le_div_iff₀ (sq_pos_of_pos hX0)).mpr
    exact_mod_cast hgX2
  apply Finset.mem_biUnion.mpr
  refine ⟨j, mem_dyadicParameterIndices.mpr ⟨hjN, hj1, ?_, hXN⟩, ?_⟩
  · change V < 2 * X
    omega
  · apply mem_regularParameterBox.mpr
    exact ⟨⟨hg.1, hgi⟩, ⟨hu.1, by omega⟩, ⟨hv.1, hvX.le⟩, hXv, ha, hb, hc⟩

theorem largeRegularParameters_card_le_blocks (N V K : ℕ) (hV : 4 ≤ V) :
    ((largeRegularParameters N V K).card : ℝ) ≤
      ∑ j ∈ dyadicParameterIndices N V, ((regularParameterBox N K (2 ^ j)).card : ℝ) := by
  classical
  have h := (Finset.card_le_card (largeRegularParameters_dyadic_cover N V K hV)).trans
    Finset.card_biUnion_le
  exact_mod_cast h

theorem log_dyadic_double (j : ℕ) :
    Real.log (2 * ((2 ^ j : ℕ) : ℝ)) = ((j : ℝ) + 1) * Real.log 2 := by
  push_cast
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ (by norm_num)), Real.log_pow]
  ring

theorem log_dyadic_terminal {N : ℕ} (hN : 0 < N) (j : ℕ) :
    Real.log (2 * ((N : ℝ) / ((2 ^ j : ℕ) : ℝ) ^ 2)) =
      Real.log N + (1 - 2 * (j : ℝ)) * Real.log 2 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hp : (((2 ^ j : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [Real.log_mul (by norm_num) (div_ne_zero hN0 (pow_ne_zero _ hp)),
    Real.log_div hN0 (pow_ne_zero _ hp), Real.log_pow]
  push_cast
  rw [Real.log_pow]
  ring

end Erdos302
