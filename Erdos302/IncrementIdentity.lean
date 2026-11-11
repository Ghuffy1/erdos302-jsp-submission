import Erdos302.FiberMaximum

namespace Erdos302

theorem smoothAlpha_eq_sum_increments (P : Finset ℕ) (N : ℕ) :
    smoothAlpha P N = ∑ n ∈ Finset.Icc 1 N, smoothIncrement P n := by
  induction N with
  | zero => simp [smoothAlpha_zero]
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih]
    have hmono : smoothAlpha P N ≤ smoothAlpha P (N + 1) := smoothAlpha_mono P (Nat.le_succ N)
    change smoothAlpha P (N + 1) =
      smoothAlpha P N + (smoothAlpha P (N + 1) - smoothAlpha P N)
    omega

theorem smoothIncrement_eq_zero_of_not_smooth {P : Finset ℕ} {n : ℕ}
    (hn : n ∉ Nat.factoredNumbers P) : smoothIncrement P n = 0 := by
  have hsets : smoothVertices P n = smoothVertices P (n - 1) := by
    ext k
    simp only [mem_smoothVertices]
    constructor
    · rintro ⟨hkpos, hkn, hks⟩
      refine ⟨hkpos, ?_, hks⟩
      have hne : k ≠ n := by rintro rfl; exact hn hks
      omega
    · rintro ⟨hkpos, hkn, hks⟩
      exact ⟨hkpos, by omega, hks⟩
  simp only [smoothIncrement, smoothAlpha, hsets, Nat.sub_self]

noncomputable def roughCount (P : Finset ℕ) (N : ℕ) : ℕ := (roughIndices P N).card

theorem roughCount_zero (P : Finset ℕ) : roughCount P 0 = 0 := by
  simp [roughCount, roughIndices]

theorem sum_Icc_truncate (f : ℕ → ℕ) {M N : ℕ} (hMN : M ≤ N) :
    (∑ n ∈ Finset.Icc 1 M, f n) =
      ∑ n ∈ Finset.Icc 1 N, if n ≤ M then f n else 0 := by
  have hf : (Finset.Icc 1 N).filter (fun n => n ≤ M) = Finset.Icc 1 M := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [← Finset.sum_filter, hf]

theorem roughIndices_filter_quotient (P : Finset ℕ) {N n : ℕ} (hn : 0 < n) :
    (roughIndices P N).filter (fun q => n ≤ N / q) = roughIndices P (N / n) := by
  classical
  ext q
  simp only [roughIndices, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hqpos, hqN⟩, hrough⟩, hndiv⟩
    refine ⟨⟨hqpos, ?_⟩, hrough⟩
    apply (Nat.le_div_iff_mul_le hn).mpr
    simpa only [mul_comm] using (Nat.le_div_iff_mul_le (show 0 < q by omega)).mp hndiv
  · rintro ⟨⟨hqpos, hqN⟩, hrough⟩
    refine ⟨⟨⟨hqpos, hqN.trans (Nat.div_le_self N n)⟩, hrough⟩, ?_⟩
    apply (Nat.le_div_iff_mul_le (show 0 < q by omega)).mpr
    simpa only [mul_comm] using (Nat.le_div_iff_mul_le hn).mp hqN

theorem relaxedExtremal_increment_sum (V N : ℕ) :
    relaxedExtremal V N =
      ∑ n ∈ Finset.Icc 1 N, smoothIncrement (primeSet V) n * roughCount (primeSet V) (N / n) := by
  classical
  rw [relaxedExtremal_fiber_sum]
  simp_rw [smoothAlpha_eq_sum_increments]
  calc
    (∑ q ∈ roughIndices (primeSet V) N,
        ∑ n ∈ Finset.Icc 1 (N / q), smoothIncrement (primeSet V) n) =
      ∑ q ∈ roughIndices (primeSet V) N,
        ∑ n ∈ Finset.Icc 1 N, if n ≤ N / q then smoothIncrement (primeSet V) n else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact sum_Icc_truncate _ (Nat.div_le_self N q)
    _ = ∑ n ∈ Finset.Icc 1 N,
        ∑ q ∈ roughIndices (primeSet V) N, if n ≤ N / q then smoothIncrement (primeSet V) n else 0 :=
      Finset.sum_comm
    _ = ∑ n ∈ Finset.Icc 1 N, smoothIncrement (primeSet V) n * roughCount (primeSet V) (N / n) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Finset.sum_filter, roughIndices_filter_quotient _ (show 0 < n from (Finset.mem_Icc.mp hn).1)]
      simp [roughCount, mul_comm]

end Erdos302
